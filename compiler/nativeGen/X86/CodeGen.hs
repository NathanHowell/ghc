-----------------------------------------------------------------------------
--
-- Generating machine code (instruction selection)
--
-- (c) The University of Glasgow 1996-2004
--
-----------------------------------------------------------------------------

-- This is a big module, but, if you pay attention to
-- (a) the sectioning, and (b) the type signatures, the
-- structure should not be too overwhelming.

module X86.CodeGen (
        cmmTopCodeGen,
        generateJumpTableForInstr,
        InstrBlock
)

where

#include "HsVersions.h"
#include "nativeGen/NCG.h"
#include "../includes/MachDeps.h"

-- NCG stuff:
import X86.Instr
import X86.Cond
import X86.Regs
import X86.RegInfo
import CPrim
import Instruction
import PIC
import NCGMonad
import Size
import Reg
import Platform

-- Our intermediate code:
import BasicTypes
import BlockId
import Module           ( primPackageId )
import PprCmm           ()
import OldCmm
import OldPprCmm        ()
import CLabel

-- The rest:
import StaticFlags      ( opt_PIC )
import ForeignCall      ( CCallConv(..) )
import OrdList
import Outputable
import Unique
import FastString
import FastBool         ( isFastTrue )
import Constants        ( wORD_SIZE )
import DynFlags

import Control.Monad
import Data.Bits
import Data.Int
import Data.Maybe
import Data.Word

is32BitPlatform :: NatM Bool
is32BitPlatform = do
    dflags <- getDynFlagsNat
    return $ target32Bit (targetPlatform dflags)

sse2Enabled :: NatM Bool
sse2Enabled = do
  dflags <- getDynFlagsNat
  case platformArch (targetPlatform dflags) of
      ArchX86_64 -> -- SSE2 is fixed on for x86_64.  It would be
                    -- possible to make it optional, but we'd need to
                    -- fix at least the foreign call code where the
                    -- calling convention specifies the use of xmm regs,
                    -- and possibly other places.
                    return True
      ArchX86    -> return (dopt Opt_SSE2 dflags || dopt Opt_SSE4_2 dflags)
      _          -> panic "sse2Enabled: Not an X86* arch"

sse4_2Enabled :: NatM Bool
sse4_2Enabled = do
  dflags <- getDynFlagsNat
  return (dopt Opt_SSE4_2 dflags)

if_sse2 :: NatM a -> NatM a -> NatM a
if_sse2 sse2 x87 = do
  b <- sse2Enabled
  if b then sse2 else x87

cmmTopCodeGen
        :: RawCmmDecl
        -> NatM [NatCmmDecl (Alignment, CmmStatics) Instr]

cmmTopCodeGen (CmmProc info lab (ListGraph blocks)) = do
  (nat_blocks,statics) <- mapAndUnzipM basicBlockCodeGen blocks
  picBaseMb <- getPicBaseMaybeNat
  dflags <- getDynFlagsNat
  let proc = CmmProc info lab (ListGraph $ concat nat_blocks)
      tops = proc : concat statics
      os   = platformOS $ targetPlatform dflags

  case picBaseMb of
      Just picBase -> initializePicBase_x86 ArchX86 os picBase tops
      Nothing -> return tops

cmmTopCodeGen (CmmData sec dat) = do
  return [CmmData sec (1, dat)]  -- no translation, we just use CmmStatic


basicBlockCodeGen
        :: CmmBasicBlock
        -> NatM ( [NatBasicBlock Instr]
                , [NatCmmDecl (Alignment, CmmStatics) Instr])

basicBlockCodeGen (BasicBlock id stmts) = do
  instrs <- stmtsToInstrs stmts
  -- code generation may introduce new basic block boundaries, which
  -- are indicated by the NEWBLOCK instruction.  We must split up the
  -- instruction stream into basic blocks again.  Also, we extract
  -- LDATAs here too.
  let
        (top,other_blocks,statics) = foldrOL mkBlocks ([],[],[]) instrs

        mkBlocks (NEWBLOCK id) (instrs,blocks,statics)
          = ([], BasicBlock id instrs : blocks, statics)
        mkBlocks (LDATA sec dat) (instrs,blocks,statics)
          = (instrs, blocks, CmmData sec dat:statics)
        mkBlocks instr (instrs,blocks,statics)
          = (instr:instrs, blocks, statics)
  -- in
  return (BasicBlock id top : other_blocks, statics)


stmtsToInstrs :: [CmmStmt] -> NatM InstrBlock
stmtsToInstrs stmts
   = do instrss <- mapM stmtToInstrs stmts
        return (concatOL instrss)


stmtToInstrs :: CmmStmt -> NatM InstrBlock
stmtToInstrs stmt = do
  is32Bit <- is32BitPlatform
  case stmt of
    CmmNop         -> return nilOL
    CmmComment s   -> return (unitOL (COMMENT s))

    CmmAssign reg src
      | isFloatType ty         -> assignReg_FltCode size reg src
      | is32Bit && isWord64 ty -> assignReg_I64Code      reg src
      | otherwise              -> assignReg_IntCode size reg src
        where ty = cmmRegType reg
              size = cmmTypeSize ty

    CmmStore addr src
      | isFloatType ty         -> assignMem_FltCode size addr src
      | is32Bit && isWord64 ty -> assignMem_I64Code      addr src
      | otherwise              -> assignMem_IntCode size addr src
        where ty = cmmExprType src
              size = cmmTypeSize ty

    CmmCall target result_regs args _
       -> genCCall is32Bit target result_regs args

    CmmBranch id          -> genBranch id
    CmmCondBranch arg id  -> genCondJump id arg
    CmmSwitch arg ids     -> genSwitch arg ids
    CmmJump arg _         -> genJump arg
    CmmReturn _           ->
      panic "stmtToInstrs: return statement should have been cps'd away"


--------------------------------------------------------------------------------
-- | 'InstrBlock's are the insn sequences generated by the insn selectors.
--      They are really trees of insns to facilitate fast appending, where a
--      left-to-right traversal yields the insns in the correct order.
--
type InstrBlock
        = OrdList Instr


-- | Condition codes passed up the tree.
--
data CondCode
        = CondCode Bool Cond InstrBlock


-- | a.k.a "Register64"
--      Reg is the lower 32-bit temporary which contains the result.
--      Use getHiVRegFromLo to find the other VRegUnique.
--
--      Rules of this simplified insn selection game are therefore that
--      the returned Reg may be modified
--
data ChildCode64
   = ChildCode64
        InstrBlock
        Reg


-- | Register's passed up the tree.  If the stix code forces the register
--      to live in a pre-decided machine register, it comes out as @Fixed@;
--      otherwise, it comes out as @Any@, and the parent can decide which
--      register to put it in.
--
data Register
        = Fixed Size Reg InstrBlock
        | Any   Size (Reg -> InstrBlock)


swizzleRegisterRep :: Register -> Size -> Register
swizzleRegisterRep (Fixed _ reg code) size = Fixed size reg code
swizzleRegisterRep (Any _ codefn)     size = Any   size codefn


-- | Grab the Reg for a CmmReg
getRegisterReg :: Bool -> CmmReg -> Reg

getRegisterReg use_sse2 (CmmLocal (LocalReg u pk))
  = let sz = cmmTypeSize pk in
    if isFloatSize sz && not use_sse2
       then RegVirtual (mkVirtualReg u FF80)
       else RegVirtual (mkVirtualReg u sz)

getRegisterReg _ (CmmGlobal mid)
  = case globalRegMaybe mid of
        Just reg -> RegReal $ reg
        Nothing  -> pprPanic "getRegisterReg-memory" (ppr $ CmmGlobal mid)
        -- By this stage, the only MagicIds remaining should be the
        -- ones which map to a real machine register on this
        -- platform.  Hence ...


-- | Memory addressing modes passed up the tree.
data Amode
        = Amode AddrMode InstrBlock

{-
Now, given a tree (the argument to an CmmLoad) that references memory,
produce a suitable addressing mode.

A Rule of the Game (tm) for Amodes: use of the addr bit must
immediately follow use of the code part, since the code part puts
values in registers which the addr then refers to.  So you can't put
anything in between, lest it overwrite some of those registers.  If
you need to do some other computation between the code part and use of
the addr bit, first store the effective address from the amode in a
temporary, then do the other computation, and then use the temporary:

    code
    LEA amode, tmp
    ... other computation ...
    ... (tmp) ...
-}


-- | Check whether an integer will fit in 32 bits.
--      A CmmInt is intended to be truncated to the appropriate
--      number of bits, so here we truncate it to Int64.  This is
--      important because e.g. -1 as a CmmInt might be either
--      -1 or 18446744073709551615.
--
is32BitInteger :: Integer -> Bool
is32BitInteger i = i64 <= 0x7fffffff && i64 >= -0x80000000
  where i64 = fromIntegral i :: Int64


-- | Convert a BlockId to some CmmStatic data
jumpTableEntry :: Maybe BlockId -> CmmStatic
jumpTableEntry Nothing = CmmStaticLit (CmmInt 0 wordWidth)
jumpTableEntry (Just blockid) = CmmStaticLit (CmmLabel blockLabel)
    where blockLabel = mkAsmTempLabel (getUnique blockid)


-- -----------------------------------------------------------------------------
-- General things for putting together code sequences

-- Expand CmmRegOff.  ToDo: should we do it this way around, or convert
-- CmmExprs into CmmRegOff?
mangleIndexTree :: CmmReg -> Int -> CmmExpr
mangleIndexTree reg off
  = CmmMachOp (MO_Add width) [CmmReg reg, CmmLit (CmmInt (fromIntegral off) width)]
  where width = typeWidth (cmmRegType reg)

-- | The dual to getAnyReg: compute an expression into a register, but
--      we don't mind which one it is.
getSomeReg :: CmmExpr -> NatM (Reg, InstrBlock)
getSomeReg expr = do
  r <- getRegister expr
  case r of
    Any rep code -> do
        tmp <- getNewRegNat rep
        return (tmp, code tmp)
    Fixed _ reg code ->
        return (reg, code)


assignMem_I64Code :: CmmExpr -> CmmExpr -> NatM InstrBlock
assignMem_I64Code addrTree valueTree = do
  Amode addr addr_code <- getAmode addrTree
  ChildCode64 vcode rlo <- iselExpr64 valueTree
  let
        rhi = getHiVRegFromLo rlo

        -- Little-endian store
        mov_lo = MOV II32 (OpReg rlo) (OpAddr addr)
        mov_hi = MOV II32 (OpReg rhi) (OpAddr (fromJust (addrOffset addr 4)))
  -- in
  return (vcode `appOL` addr_code `snocOL` mov_lo `snocOL` mov_hi)


assignReg_I64Code :: CmmReg  -> CmmExpr -> NatM InstrBlock
assignReg_I64Code (CmmLocal (LocalReg u_dst _)) valueTree = do
   ChildCode64 vcode r_src_lo <- iselExpr64 valueTree
   let
         r_dst_lo = RegVirtual $ mkVirtualReg u_dst II32
         r_dst_hi = getHiVRegFromLo r_dst_lo
         r_src_hi = getHiVRegFromLo r_src_lo
         mov_lo = MOV II32 (OpReg r_src_lo) (OpReg r_dst_lo)
         mov_hi = MOV II32 (OpReg r_src_hi) (OpReg r_dst_hi)
   -- in
   return (
        vcode `snocOL` mov_lo `snocOL` mov_hi
     )

assignReg_I64Code _ _
   = panic "assignReg_I64Code(i386): invalid lvalue"


iselExpr64        :: CmmExpr -> NatM ChildCode64
iselExpr64 (CmmLit (CmmInt i _)) = do
  (rlo,rhi) <- getNewRegPairNat II32
  let
        r = fromIntegral (fromIntegral i :: Word32)
        q = fromIntegral (fromIntegral (i `shiftR` 32) :: Word32)
        code = toOL [
                MOV II32 (OpImm (ImmInteger r)) (OpReg rlo),
                MOV II32 (OpImm (ImmInteger q)) (OpReg rhi)
                ]
  -- in
  return (ChildCode64 code rlo)

iselExpr64 (CmmLoad addrTree ty) | isWord64 ty = do
   Amode addr addr_code <- getAmode addrTree
   (rlo,rhi) <- getNewRegPairNat II32
   let
        mov_lo = MOV II32 (OpAddr addr) (OpReg rlo)
        mov_hi = MOV II32 (OpAddr (fromJust (addrOffset addr 4))) (OpReg rhi)
   -- in
   return (
            ChildCode64 (addr_code `snocOL` mov_lo `snocOL` mov_hi)
                        rlo
     )

iselExpr64 (CmmReg (CmmLocal (LocalReg vu ty))) | isWord64 ty
   = return (ChildCode64 nilOL (RegVirtual $ mkVirtualReg vu II32))

-- we handle addition, but rather badly
iselExpr64 (CmmMachOp (MO_Add _) [e1, CmmLit (CmmInt i _)]) = do
   ChildCode64 code1 r1lo <- iselExpr64 e1
   (rlo,rhi) <- getNewRegPairNat II32
   let
        r = fromIntegral (fromIntegral i :: Word32)
        q = fromIntegral (fromIntegral (i `shiftR` 32) :: Word32)
        r1hi = getHiVRegFromLo r1lo
        code =  code1 `appOL`
                toOL [ MOV II32 (OpReg r1lo) (OpReg rlo),
                       ADD II32 (OpImm (ImmInteger r)) (OpReg rlo),
                       MOV II32 (OpReg r1hi) (OpReg rhi),
                       ADC II32 (OpImm (ImmInteger q)) (OpReg rhi) ]
   -- in
   return (ChildCode64 code rlo)

iselExpr64 (CmmMachOp (MO_Add _) [e1,e2]) = do
   ChildCode64 code1 r1lo <- iselExpr64 e1
   ChildCode64 code2 r2lo <- iselExpr64 e2
   (rlo,rhi) <- getNewRegPairNat II32
   let
        r1hi = getHiVRegFromLo r1lo
        r2hi = getHiVRegFromLo r2lo
        code =  code1 `appOL`
                code2 `appOL`
                toOL [ MOV II32 (OpReg r1lo) (OpReg rlo),
                       ADD II32 (OpReg r2lo) (OpReg rlo),
                       MOV II32 (OpReg r1hi) (OpReg rhi),
                       ADC II32 (OpReg r2hi) (OpReg rhi) ]
   -- in
   return (ChildCode64 code rlo)

iselExpr64 (CmmMachOp (MO_UU_Conv _ W64) [expr]) = do
     fn <- getAnyReg expr
     r_dst_lo <-  getNewRegNat II32
     let r_dst_hi = getHiVRegFromLo r_dst_lo
         code = fn r_dst_lo
     return (
             ChildCode64 (code `snocOL`
                          MOV II32 (OpImm (ImmInt 0)) (OpReg r_dst_hi))
                          r_dst_lo
            )

iselExpr64 expr
   = do dflags <- getDynFlagsNat
        pprPanic "iselExpr64(i386)" (pprPlatform (targetPlatform dflags) expr)


--------------------------------------------------------------------------------
getRegister :: CmmExpr -> NatM Register
getRegister e = do is32Bit <- is32BitPlatform
                   getRegister' is32Bit e

getRegister' :: Bool -> CmmExpr -> NatM Register

getRegister' is32Bit (CmmReg reg)
  = case reg of
        CmmGlobal PicBaseReg
         | is32Bit ->
            -- on x86_64, we have %rip for PicBaseReg, but it's not
            -- a full-featured register, it can only be used for
            -- rip-relative addressing.
            do reg' <- getPicBaseNat (archWordSize is32Bit)
               return (Fixed (archWordSize is32Bit) reg' nilOL)
        _ ->
            do use_sse2 <- sse2Enabled
               let
                 sz = cmmTypeSize (cmmRegType reg)
                 size | not use_sse2 && isFloatSize sz = FF80
                      | otherwise                      = sz
               --
               return (Fixed size (getRegisterReg use_sse2 reg) nilOL)


getRegister' is32Bit (CmmRegOff r n)
  = getRegister' is32Bit $ mangleIndexTree r n

-- for 32-bit architectuers, support some 64 -> 32 bit conversions:
-- TO_W_(x), TO_W_(x >> 32)

getRegister' is32Bit (CmmMachOp (MO_UU_Conv W64 W32)
                     [CmmMachOp (MO_U_Shr W64) [x,CmmLit (CmmInt 32 _)]])
 | is32Bit = do
  ChildCode64 code rlo <- iselExpr64 x
  return $ Fixed II32 (getHiVRegFromLo rlo) code

getRegister' is32Bit (CmmMachOp (MO_SS_Conv W64 W32)
                     [CmmMachOp (MO_U_Shr W64) [x,CmmLit (CmmInt 32 _)]])
 | is32Bit = do
  ChildCode64 code rlo <- iselExpr64 x
  return $ Fixed II32 (getHiVRegFromLo rlo) code

getRegister' is32Bit (CmmMachOp (MO_UU_Conv W64 W32) [x])
 | is32Bit = do
  ChildCode64 code rlo <- iselExpr64 x
  return $ Fixed II32 rlo code

getRegister' is32Bit (CmmMachOp (MO_SS_Conv W64 W32) [x])
 | is32Bit = do
  ChildCode64 code rlo <- iselExpr64 x
  return $ Fixed II32 rlo code

getRegister' _ (CmmLit lit@(CmmFloat f w)) =
  if_sse2 float_const_sse2 float_const_x87
 where
  float_const_sse2
    | f == 0.0 = do
      let
          size = floatSize w
          code dst = unitOL  (XOR size (OpReg dst) (OpReg dst))
        -- I don't know why there are xorpd, xorps, and pxor instructions.
        -- They all appear to do the same thing --SDM
      return (Any size code)

   | otherwise = do
      Amode addr code <- memConstant (widthInBytes w) lit
      loadFloatAmode True w addr code

  float_const_x87 = case w of
    W64
      | f == 0.0 ->
        let code dst = unitOL (GLDZ dst)
        in  return (Any FF80 code)

      | f == 1.0 ->
        let code dst = unitOL (GLD1 dst)
        in  return (Any FF80 code)

    _otherwise -> do
      Amode addr code <- memConstant (widthInBytes w) lit
      loadFloatAmode False w addr code

-- catch simple cases of zero- or sign-extended load
getRegister' _ (CmmMachOp (MO_UU_Conv W8 W32) [CmmLoad addr _]) = do
  code <- intLoadCode (MOVZxL II8) addr
  return (Any II32 code)

getRegister' _ (CmmMachOp (MO_SS_Conv W8 W32) [CmmLoad addr _]) = do
  code <- intLoadCode (MOVSxL II8) addr
  return (Any II32 code)

getRegister' _ (CmmMachOp (MO_UU_Conv W16 W32) [CmmLoad addr _]) = do
  code <- intLoadCode (MOVZxL II16) addr
  return (Any II32 code)

getRegister' _ (CmmMachOp (MO_SS_Conv W16 W32) [CmmLoad addr _]) = do
  code <- intLoadCode (MOVSxL II16) addr
  return (Any II32 code)

-- catch simple cases of zero- or sign-extended load
getRegister' is32Bit (CmmMachOp (MO_UU_Conv W8 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOVZxL II8) addr
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_SS_Conv W8 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOVSxL II8) addr
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_UU_Conv W16 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOVZxL II16) addr
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_SS_Conv W16 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOVSxL II16) addr
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_UU_Conv W32 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOV II32) addr -- 32-bit loads zero-extend
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_SS_Conv W32 W64) [CmmLoad addr _])
 | not is32Bit = do
  code <- intLoadCode (MOVSxL II32) addr
  return (Any II64 code)

getRegister' is32Bit (CmmMachOp (MO_Add W64) [CmmReg (CmmGlobal PicBaseReg),
                                     CmmLit displacement])
 | not is32Bit = do
      return $ Any II64 (\dst -> unitOL $
        LEA II64 (OpAddr (ripRel (litToImm displacement))) (OpReg dst))

getRegister' is32Bit (CmmMachOp mop [x]) = do -- unary MachOps
    sse2 <- sse2Enabled
    case mop of
      MO_F_Neg w
         | sse2      -> sse2NegCode w x
         | otherwise -> trivialUFCode FF80 (GNEG FF80) x

      MO_S_Neg w -> triv_ucode NEGI (intSize w)
      MO_Not w   -> triv_ucode NOT  (intSize w)

      -- Nop conversions
      MO_UU_Conv W32 W8  -> toI8Reg  W32 x
      MO_SS_Conv W32 W8  -> toI8Reg  W32 x
      MO_UU_Conv W16 W8  -> toI8Reg  W16 x
      MO_SS_Conv W16 W8  -> toI8Reg  W16 x
      MO_UU_Conv W32 W16 -> toI16Reg W32 x
      MO_SS_Conv W32 W16 -> toI16Reg W32 x

      MO_UU_Conv W64 W32 | not is32Bit -> conversionNop II64 x
      MO_SS_Conv W64 W32 | not is32Bit -> conversionNop II64 x
      MO_UU_Conv W64 W16 | not is32Bit -> toI16Reg W64 x
      MO_SS_Conv W64 W16 | not is32Bit -> toI16Reg W64 x
      MO_UU_Conv W64 W8  | not is32Bit -> toI8Reg  W64 x
      MO_SS_Conv W64 W8  | not is32Bit -> toI8Reg  W64 x

      MO_UU_Conv rep1 rep2 | rep1 == rep2 -> conversionNop (intSize rep1) x
      MO_SS_Conv rep1 rep2 | rep1 == rep2 -> conversionNop (intSize rep1) x

      -- widenings
      MO_UU_Conv W8  W32 -> integerExtend W8  W32 MOVZxL x
      MO_UU_Conv W16 W32 -> integerExtend W16 W32 MOVZxL x
      MO_UU_Conv W8  W16 -> integerExtend W8  W16 MOVZxL x

      MO_SS_Conv W8  W32 -> integerExtend W8  W32 MOVSxL x
      MO_SS_Conv W16 W32 -> integerExtend W16 W32 MOVSxL x
      MO_SS_Conv W8  W16 -> integerExtend W8  W16 MOVSxL x

      MO_UU_Conv W8  W64 | not is32Bit -> integerExtend W8  W64 MOVZxL x
      MO_UU_Conv W16 W64 | not is32Bit -> integerExtend W16 W64 MOVZxL x
      MO_UU_Conv W32 W64 | not is32Bit -> integerExtend W32 W64 MOVZxL x
      MO_SS_Conv W8  W64 | not is32Bit -> integerExtend W8  W64 MOVSxL x
      MO_SS_Conv W16 W64 | not is32Bit -> integerExtend W16 W64 MOVSxL x
      MO_SS_Conv W32 W64 | not is32Bit -> integerExtend W32 W64 MOVSxL x
        -- for 32-to-64 bit zero extension, amd64 uses an ordinary movl.
        -- However, we don't want the register allocator to throw it
        -- away as an unnecessary reg-to-reg move, so we keep it in
        -- the form of a movzl and print it as a movl later.

      MO_FF_Conv W32 W64
        | sse2      -> coerceFP2FP W64 x
        | otherwise -> conversionNop FF80 x

      MO_FF_Conv W64 W32 -> coerceFP2FP W32 x

      MO_FS_Conv from to -> coerceFP2Int from to x
      MO_SF_Conv from to -> coerceInt2FP from to x

      _other -> pprPanic "getRegister" (pprMachOp mop)
   where
        triv_ucode :: (Size -> Operand -> Instr) -> Size -> NatM Register
        triv_ucode instr size = trivialUCode size (instr size) x

        -- signed or unsigned extension.
        integerExtend :: Width -> Width
                      -> (Size -> Operand -> Operand -> Instr)
                      -> CmmExpr -> NatM Register
        integerExtend from to instr expr = do
            (reg,e_code) <- if from == W8 then getByteReg expr
                                          else getSomeReg expr
            let
                code dst =
                  e_code `snocOL`
                  instr (intSize from) (OpReg reg) (OpReg dst)
            return (Any (intSize to) code)

        toI8Reg :: Width -> CmmExpr -> NatM Register
        toI8Reg new_rep expr
            = do codefn <- getAnyReg expr
                 return (Any (intSize new_rep) codefn)
                -- HACK: use getAnyReg to get a byte-addressable register.
                -- If the source was a Fixed register, this will add the
                -- mov instruction to put it into the desired destination.
                -- We're assuming that the destination won't be a fixed
                -- non-byte-addressable register; it won't be, because all
                -- fixed registers are word-sized.

        toI16Reg = toI8Reg -- for now

        conversionNop :: Size -> CmmExpr -> NatM Register
        conversionNop new_size expr
            = do e_code <- getRegister' is32Bit expr
                 return (swizzleRegisterRep e_code new_size)


getRegister' is32Bit (CmmMachOp mop [x, y]) = do -- dyadic MachOps
  sse2 <- sse2Enabled
  case mop of
      MO_F_Eq _ -> condFltReg is32Bit EQQ x y
      MO_F_Ne _ -> condFltReg is32Bit NE  x y
      MO_F_Gt _ -> condFltReg is32Bit GTT x y
      MO_F_Ge _ -> condFltReg is32Bit GE  x y
      MO_F_Lt _ -> condFltReg is32Bit LTT x y
      MO_F_Le _ -> condFltReg is32Bit LE  x y

      MO_Eq _   -> condIntReg EQQ x y
      MO_Ne _   -> condIntReg NE  x y

      MO_S_Gt _ -> condIntReg GTT x y
      MO_S_Ge _ -> condIntReg GE  x y
      MO_S_Lt _ -> condIntReg LTT x y
      MO_S_Le _ -> condIntReg LE  x y

      MO_U_Gt _ -> condIntReg GU  x y
      MO_U_Ge _ -> condIntReg GEU x y
      MO_U_Lt _ -> condIntReg LU  x y
      MO_U_Le _ -> condIntReg LEU x y

      MO_F_Add w  | sse2      -> trivialFCode_sse2 w ADD  x y
                  | otherwise -> trivialFCode_x87    GADD x y
      MO_F_Sub w  | sse2      -> trivialFCode_sse2 w SUB  x y
                  | otherwise -> trivialFCode_x87    GSUB x y
      MO_F_Quot w | sse2      -> trivialFCode_sse2 w FDIV x y
                  | otherwise -> trivialFCode_x87    GDIV x y
      MO_F_Mul w  | sse2      -> trivialFCode_sse2 w MUL x y
                  | otherwise -> trivialFCode_x87    GMUL x y

      MO_Add rep -> add_code rep x y
      MO_Sub rep -> sub_code rep x y

      MO_S_Quot rep -> div_code rep True  True  x y
      MO_S_Rem  rep -> div_code rep True  False x y
      MO_U_Quot rep -> div_code rep False True  x y
      MO_U_Rem  rep -> div_code rep False False x y

      MO_S_MulMayOflo rep -> imulMayOflo rep x y

      MO_Mul rep -> triv_op rep IMUL
      MO_And rep -> triv_op rep AND
      MO_Or  rep -> triv_op rep OR
      MO_Xor rep -> triv_op rep XOR

        {- Shift ops on x86s have constraints on their source, it
           either has to be Imm, CL or 1
            => trivialCode is not restrictive enough (sigh.)
        -}
      MO_Shl rep   -> shift_code rep SHL x y {-False-}
      MO_U_Shr rep -> shift_code rep SHR x y {-False-}
      MO_S_Shr rep -> shift_code rep SAR x y {-False-}

      _other -> pprPanic "getRegister(x86) - binary CmmMachOp (1)" (pprMachOp mop)
  where
    --------------------
    triv_op width instr = trivialCode width op (Just op) x y
                        where op   = instr (intSize width)

    imulMayOflo :: Width -> CmmExpr -> CmmExpr -> NatM Register
    imulMayOflo rep a b = do
         (a_reg, a_code) <- getNonClobberedReg a
         b_code <- getAnyReg b
         let
             shift_amt  = case rep of
                           W32 -> 31
                           W64 -> 63
                           _ -> panic "shift_amt"

             size = intSize rep
             code = a_code `appOL` b_code eax `appOL`
                        toOL [
                           IMUL2 size (OpReg a_reg),   -- result in %edx:%eax
                           SAR size (OpImm (ImmInt shift_amt)) (OpReg eax),
                                -- sign extend lower part
                           SUB size (OpReg edx) (OpReg eax)
                                -- compare against upper
                           -- eax==0 if high part == sign extended low part
                        ]
         -- in
         return (Fixed size eax code)

    --------------------
    shift_code :: Width
               -> (Size -> Operand -> Operand -> Instr)
               -> CmmExpr
               -> CmmExpr
               -> NatM Register

    {- Case1: shift length as immediate -}
    shift_code width instr x (CmmLit lit) = do
          x_code <- getAnyReg x
          let
               size = intSize width
               code dst
                  = x_code dst `snocOL`
                    instr size (OpImm (litToImm lit)) (OpReg dst)
          -- in
          return (Any size code)

    {- Case2: shift length is complex (non-immediate)
      * y must go in %ecx.
      * we cannot do y first *and* put its result in %ecx, because
        %ecx might be clobbered by x.
      * if we do y second, then x cannot be
        in a clobbered reg.  Also, we cannot clobber x's reg
        with the instruction itself.
      * so we can either:
        - do y first, put its result in a fresh tmp, then copy it to %ecx later
        - do y second and put its result into %ecx.  x gets placed in a fresh
          tmp.  This is likely to be better, becuase the reg alloc can
          eliminate this reg->reg move here (it won't eliminate the other one,
          because the move is into the fixed %ecx).
    -}
    shift_code width instr x y{-amount-} = do
        x_code <- getAnyReg x
        let size = intSize width
        tmp <- getNewRegNat size
        y_code <- getAnyReg y
        let
           code = x_code tmp `appOL`
                  y_code ecx `snocOL`
                  instr size (OpReg ecx) (OpReg tmp)
        -- in
        return (Fixed size tmp code)

    --------------------
    add_code :: Width -> CmmExpr -> CmmExpr -> NatM Register
    add_code rep x (CmmLit (CmmInt y _))
        | is32BitInteger y = add_int rep x y
    add_code rep x y = trivialCode rep (ADD size) (Just (ADD size)) x y
      where size = intSize rep

    --------------------
    sub_code :: Width -> CmmExpr -> CmmExpr -> NatM Register
    sub_code rep x (CmmLit (CmmInt y _))
        | is32BitInteger (-y) = add_int rep x (-y)
    sub_code rep x y = trivialCode rep (SUB (intSize rep)) Nothing x y

    -- our three-operand add instruction:
    add_int width x y = do
        (x_reg, x_code) <- getSomeReg x
        let
            size = intSize width
            imm = ImmInt (fromInteger y)
            code dst
               = x_code `snocOL`
                 LEA size
                        (OpAddr (AddrBaseIndex (EABaseReg x_reg) EAIndexNone imm))
                        (OpReg dst)
        --
        return (Any size code)

    ----------------------
    div_code width signed quotient x y = do
           (y_op, y_code) <- getRegOrMem y -- cannot be clobbered
           x_code <- getAnyReg x
           let
             size = intSize width
             widen | signed    = CLTD size
                   | otherwise = XOR size (OpReg edx) (OpReg edx)

             instr | signed    = IDIV
                   | otherwise = DIV

             code = y_code `appOL`
                    x_code eax `appOL`
                    toOL [widen, instr size y_op]

             result | quotient  = eax
                    | otherwise = edx

           -- in
           return (Fixed size result code)


getRegister' _ (CmmLoad mem pk)
  | isFloatType pk
  = do
    Amode addr mem_code <- getAmode mem
    use_sse2 <- sse2Enabled
    loadFloatAmode use_sse2 (typeWidth pk) addr mem_code

getRegister' is32Bit (CmmLoad mem pk)
  | is32Bit && not (isWord64 pk)
  = do
    code <- intLoadCode instr mem
    return (Any size code)
  where
    width = typeWidth pk
    size = intSize width
    instr = case width of
                W8     -> MOVZxL II8
                _other -> MOV size
        -- We always zero-extend 8-bit loads, if we
        -- can't think of anything better.  This is because
        -- we can't guarantee access to an 8-bit variant of every register
        -- (esi and edi don't have 8-bit variants), so to make things
        -- simpler we do our 8-bit arithmetic with full 32-bit registers.

-- Simpler memory load code on x86_64
getRegister' is32Bit (CmmLoad mem pk)
 | not is32Bit
  = do
    code <- intLoadCode (MOV size) mem
    return (Any size code)
  where size = intSize $ typeWidth pk

getRegister' is32Bit (CmmLit (CmmInt 0 width))
  = let
        size = intSize width

        -- x86_64: 32-bit xor is one byte shorter, and zero-extends to 64 bits
        size1 = if is32Bit then size
                           else case size of
                                II64 -> II32
                                _ -> size
        code dst
           = unitOL (XOR size1 (OpReg dst) (OpReg dst))
    in
        return (Any size code)

  -- optimisation for loading small literals on x86_64: take advantage
  -- of the automatic zero-extension from 32 to 64 bits, because the 32-bit
  -- instruction forms are shorter.
getRegister' is32Bit (CmmLit lit)
  | not is32Bit, isWord64 (cmmLitType lit), not (isBigLit lit)
  = let
        imm = litToImm lit
        code dst = unitOL (MOV II32 (OpImm imm) (OpReg dst))
    in
        return (Any II64 code)
  where
   isBigLit (CmmInt i _) = i < 0 || i > 0xffffffff
   isBigLit _ = False
        -- note1: not the same as (not.is32BitLit), because that checks for
        -- signed literals that fit in 32 bits, but we want unsigned
        -- literals here.
        -- note2: all labels are small, because we're assuming the
        -- small memory model (see gcc docs, -mcmodel=small).

getRegister' _ (CmmLit lit)
  = let
        size = cmmTypeSize (cmmLitType lit)
        imm = litToImm lit
        code dst = unitOL (MOV size (OpImm imm) (OpReg dst))
    in
        return (Any size code)

getRegister' _ other = do dflags <- getDynFlagsNat
                          pprPanic "getRegister(x86)" (pprPlatform (targetPlatform dflags) other)


intLoadCode :: (Operand -> Operand -> Instr) -> CmmExpr
   -> NatM (Reg -> InstrBlock)
intLoadCode instr mem = do
  Amode src mem_code <- getAmode mem
  return (\dst -> mem_code `snocOL` instr (OpAddr src) (OpReg dst))

-- Compute an expression into *any* register, adding the appropriate
-- move instruction if necessary.
getAnyReg :: CmmExpr -> NatM (Reg -> InstrBlock)
getAnyReg expr = do
  r <- getRegister expr
  anyReg r

anyReg :: Register -> NatM (Reg -> InstrBlock)
anyReg (Any _ code)          = return code
anyReg (Fixed rep reg fcode) = return (\dst -> fcode `snocOL` reg2reg rep reg dst)

-- A bit like getSomeReg, but we want a reg that can be byte-addressed.
-- Fixed registers might not be byte-addressable, so we make sure we've
-- got a temporary, inserting an extra reg copy if necessary.
getByteReg :: CmmExpr -> NatM (Reg, InstrBlock)
getByteReg expr = do
  is32Bit <- is32BitPlatform
  if is32Bit
      then do r <- getRegister expr
              case r of
                Any rep code -> do
                    tmp <- getNewRegNat rep
                    return (tmp, code tmp)
                Fixed rep reg code
                    | isVirtualReg reg -> return (reg,code)
                    | otherwise -> do
                        tmp <- getNewRegNat rep
                        return (tmp, code `snocOL` reg2reg rep reg tmp)
                    -- ToDo: could optimise slightly by checking for
                    -- byte-addressable real registers, but that will
                    -- happen very rarely if at all.
      else getSomeReg expr -- all regs are byte-addressable on x86_64

-- Another variant: this time we want the result in a register that cannot
-- be modified by code to evaluate an arbitrary expression.
getNonClobberedReg :: CmmExpr -> NatM (Reg, InstrBlock)
getNonClobberedReg expr = do
  r <- getRegister expr
  case r of
    Any rep code -> do
        tmp <- getNewRegNat rep
        return (tmp, code tmp)
    Fixed rep reg code
        -- only free regs can be clobbered
        | RegReal (RealRegSingle rr) <- reg
        , isFastTrue (freeReg rr)
        -> do
                tmp <- getNewRegNat rep
                return (tmp, code `snocOL` reg2reg rep reg tmp)
        | otherwise ->
                return (reg, code)

reg2reg :: Size -> Reg -> Reg -> Instr
reg2reg size src dst
  | size == FF80 = GMOV src dst
  | otherwise    = MOV size (OpReg src) (OpReg dst)


--------------------------------------------------------------------------------
getAmode :: CmmExpr -> NatM Amode
getAmode e = do is32Bit <- is32BitPlatform
                getAmode' is32Bit e

getAmode' :: Bool -> CmmExpr -> NatM Amode
getAmode' _ (CmmRegOff r n) = getAmode $ mangleIndexTree r n

getAmode' is32Bit (CmmMachOp (MO_Add W64) [CmmReg (CmmGlobal PicBaseReg),
                                                  CmmLit displacement])
 | not is32Bit
    = return $ Amode (ripRel (litToImm displacement)) nilOL


-- This is all just ridiculous, since it carefully undoes
-- what mangleIndexTree has just done.
getAmode' is32Bit (CmmMachOp (MO_Sub _rep) [x, CmmLit lit@(CmmInt i _)])
  | is32BitLit is32Bit lit
  -- ASSERT(rep == II32)???
  = do (x_reg, x_code) <- getSomeReg x
       let off = ImmInt (-(fromInteger i))
       return (Amode (AddrBaseIndex (EABaseReg x_reg) EAIndexNone off) x_code)

getAmode' is32Bit (CmmMachOp (MO_Add _rep) [x, CmmLit lit])
  | is32BitLit is32Bit lit
  -- ASSERT(rep == II32)???
  = do (x_reg, x_code) <- getSomeReg x
       let off = litToImm lit
       return (Amode (AddrBaseIndex (EABaseReg x_reg) EAIndexNone off) x_code)

-- Turn (lit1 << n  + lit2) into  (lit2 + lit1 << n) so it will be
-- recognised by the next rule.
getAmode' is32Bit (CmmMachOp (MO_Add rep) [a@(CmmMachOp (MO_Shl _) _),
                                  b@(CmmLit _)])
  = getAmode' is32Bit (CmmMachOp (MO_Add rep) [b,a])

getAmode' _ (CmmMachOp (MO_Add _) [x, CmmMachOp (MO_Shl _)
                                        [y, CmmLit (CmmInt shift _)]])
  | shift == 0 || shift == 1 || shift == 2 || shift == 3
  = x86_complex_amode x y shift 0

getAmode' _ (CmmMachOp (MO_Add _)
                [x, CmmMachOp (MO_Add _)
                        [CmmMachOp (MO_Shl _) [y, CmmLit (CmmInt shift _)],
                         CmmLit (CmmInt offset _)]])
  | shift == 0 || shift == 1 || shift == 2 || shift == 3
  && is32BitInteger offset
  = x86_complex_amode x y shift offset

getAmode' _ (CmmMachOp (MO_Add _) [x,y])
  = x86_complex_amode x y 0 0

getAmode' is32Bit (CmmLit lit) | is32BitLit is32Bit lit
  = return (Amode (ImmAddr (litToImm lit) 0) nilOL)

getAmode' _ expr = do
  (reg,code) <- getSomeReg expr
  return (Amode (AddrBaseIndex (EABaseReg reg) EAIndexNone (ImmInt 0)) code)


x86_complex_amode :: CmmExpr -> CmmExpr -> Integer -> Integer -> NatM Amode
x86_complex_amode base index shift offset
  = do (x_reg, x_code) <- getNonClobberedReg base
        -- x must be in a temp, because it has to stay live over y_code
        -- we could compre x_reg and y_reg and do something better here...
       (y_reg, y_code) <- getSomeReg index
       let
           code = x_code `appOL` y_code
           base = case shift of 0 -> 1; 1 -> 2; 2 -> 4; 3 -> 8;
                                n -> panic $ "x86_complex_amode: unhandled shift! (" ++ show n ++ ")"
       return (Amode (AddrBaseIndex (EABaseReg x_reg) (EAIndex y_reg base) (ImmInt (fromIntegral offset)))
               code)




-- -----------------------------------------------------------------------------
-- getOperand: sometimes any operand will do.

-- getNonClobberedOperand: the value of the operand will remain valid across
-- the computation of an arbitrary expression, unless the expression
-- is computed directly into a register which the operand refers to
-- (see trivialCode where this function is used for an example).

getNonClobberedOperand :: CmmExpr -> NatM (Operand, InstrBlock)
getNonClobberedOperand (CmmLit lit) = do
  use_sse2 <- sse2Enabled
  if use_sse2 && isSuitableFloatingPointLit lit
    then do
      let CmmFloat _ w = lit
      Amode addr code <- memConstant (widthInBytes w) lit
      return (OpAddr addr, code)
     else do

  is32Bit <- is32BitPlatform
  if is32BitLit is32Bit lit && not (isFloatType (cmmLitType lit))
    then return (OpImm (litToImm lit), nilOL)
    else getNonClobberedOperand_generic (CmmLit lit)

getNonClobberedOperand (CmmLoad mem pk) = do
  is32Bit <- is32BitPlatform
  use_sse2 <- sse2Enabled
  if (not (isFloatType pk) || use_sse2)
      && (if is32Bit then not (isWord64 pk) else True)
    then do
      Amode src mem_code <- getAmode mem
      (src',save_code) <-
        if (amodeCouldBeClobbered src)
                then do
                   tmp <- getNewRegNat (archWordSize is32Bit)
                   return (AddrBaseIndex (EABaseReg tmp) EAIndexNone (ImmInt 0),
                           unitOL (LEA (archWordSize is32Bit) (OpAddr src) (OpReg tmp)))
                else
                   return (src, nilOL)
      return (OpAddr src', mem_code `appOL` save_code)
    else do
      getNonClobberedOperand_generic (CmmLoad mem pk)

getNonClobberedOperand e = getNonClobberedOperand_generic e

getNonClobberedOperand_generic :: CmmExpr -> NatM (Operand, InstrBlock)
getNonClobberedOperand_generic e = do
    (reg, code) <- getNonClobberedReg e
    return (OpReg reg, code)

amodeCouldBeClobbered :: AddrMode -> Bool
amodeCouldBeClobbered amode = any regClobbered (addrModeRegs amode)

regClobbered :: Reg -> Bool
regClobbered (RegReal (RealRegSingle rr)) = isFastTrue (freeReg rr)
regClobbered _ = False

-- getOperand: the operand is not required to remain valid across the
-- computation of an arbitrary expression.
getOperand :: CmmExpr -> NatM (Operand, InstrBlock)

getOperand (CmmLit lit) = do
  use_sse2 <- sse2Enabled
  if (use_sse2 && isSuitableFloatingPointLit lit)
    then do
      let CmmFloat _ w = lit
      Amode addr code <- memConstant (widthInBytes w) lit
      return (OpAddr addr, code)
    else do

  is32Bit <- is32BitPlatform
  if is32BitLit is32Bit lit && not (isFloatType (cmmLitType lit))
    then return (OpImm (litToImm lit), nilOL)
    else getOperand_generic (CmmLit lit)

getOperand (CmmLoad mem pk) = do
  is32Bit <- is32BitPlatform
  use_sse2 <- sse2Enabled
  if (not (isFloatType pk) || use_sse2) && (if is32Bit then not (isWord64 pk) else True)
     then do
       Amode src mem_code <- getAmode mem
       return (OpAddr src, mem_code)
     else
       getOperand_generic (CmmLoad mem pk)

getOperand e = getOperand_generic e

getOperand_generic :: CmmExpr -> NatM (Operand, InstrBlock)
getOperand_generic e = do
    (reg, code) <- getSomeReg e
    return (OpReg reg, code)

isOperand :: Bool -> CmmExpr -> Bool
isOperand _ (CmmLoad _ _) = True
isOperand is32Bit (CmmLit lit)  = is32BitLit is32Bit lit
                          || isSuitableFloatingPointLit lit
isOperand _ _            = False

memConstant :: Int -> CmmLit -> NatM Amode
memConstant align lit = do
  lbl <- getNewLabelNat
  dflags <- getDynFlagsNat
  (addr, addr_code) <- if target32Bit (targetPlatform dflags)
                       then do dynRef <- cmmMakeDynamicReference
                                             dflags
                                             addImportNat
                                             DataReference
                                             lbl
                               Amode addr addr_code <- getAmode dynRef
                               return (addr, addr_code)
                       else return (ripRel (ImmCLbl lbl), nilOL)
  let code =
        LDATA ReadOnlyData (align, Statics lbl [CmmStaticLit lit])
        `consOL` addr_code
  return (Amode addr code)


loadFloatAmode :: Bool -> Width -> AddrMode -> InstrBlock -> NatM Register
loadFloatAmode use_sse2 w addr addr_code = do
  let size = floatSize w
      code dst = addr_code `snocOL`
                 if use_sse2
                    then MOV size (OpAddr addr) (OpReg dst)
                    else GLD size addr dst
  -- in
  return (Any (if use_sse2 then size else FF80) code)


-- if we want a floating-point literal as an operand, we can
-- use it directly from memory.  However, if the literal is
-- zero, we're better off generating it into a register using
-- xor.
isSuitableFloatingPointLit :: CmmLit -> Bool
isSuitableFloatingPointLit (CmmFloat f _) = f /= 0.0
isSuitableFloatingPointLit _ = False

getRegOrMem :: CmmExpr -> NatM (Operand, InstrBlock)
getRegOrMem e@(CmmLoad mem pk) = do
  is32Bit <- is32BitPlatform
  use_sse2 <- sse2Enabled
  if (not (isFloatType pk) || use_sse2) && (if is32Bit then not (isWord64 pk) else True)
     then do
       Amode src mem_code <- getAmode mem
       return (OpAddr src, mem_code)
     else do
       (reg, code) <- getNonClobberedReg e
       return (OpReg reg, code)
getRegOrMem e = do
    (reg, code) <- getNonClobberedReg e
    return (OpReg reg, code)

is32BitLit :: Bool -> CmmLit -> Bool
is32BitLit is32Bit (CmmInt i W64)
 | not is32Bit
    = -- assume that labels are in the range 0-2^31-1: this assumes the
      -- small memory model (see gcc docs, -mcmodel=small).
      is32BitInteger i
is32BitLit _ _ = True




-- Set up a condition code for a conditional branch.

getCondCode :: CmmExpr -> NatM CondCode

-- yes, they really do seem to want exactly the same!

getCondCode (CmmMachOp mop [x, y])
  =
    case mop of
      MO_F_Eq W32 -> condFltCode EQQ x y
      MO_F_Ne W32 -> condFltCode NE  x y
      MO_F_Gt W32 -> condFltCode GTT x y
      MO_F_Ge W32 -> condFltCode GE  x y
      MO_F_Lt W32 -> condFltCode LTT x y
      MO_F_Le W32 -> condFltCode LE  x y

      MO_F_Eq W64 -> condFltCode EQQ x y
      MO_F_Ne W64 -> condFltCode NE  x y
      MO_F_Gt W64 -> condFltCode GTT x y
      MO_F_Ge W64 -> condFltCode GE  x y
      MO_F_Lt W64 -> condFltCode LTT x y
      MO_F_Le W64 -> condFltCode LE  x y

      MO_Eq _ -> condIntCode EQQ x y
      MO_Ne _ -> condIntCode NE  x y

      MO_S_Gt _ -> condIntCode GTT x y
      MO_S_Ge _ -> condIntCode GE  x y
      MO_S_Lt _ -> condIntCode LTT x y
      MO_S_Le _ -> condIntCode LE  x y

      MO_U_Gt _ -> condIntCode GU  x y
      MO_U_Ge _ -> condIntCode GEU x y
      MO_U_Lt _ -> condIntCode LU  x y
      MO_U_Le _ -> condIntCode LEU x y

      _other -> do dflags <- getDynFlagsNat
                   pprPanic "getCondCode(x86,x86_64,sparc)" (pprPlatform (targetPlatform dflags) (CmmMachOp mop [x,y]))

getCondCode other = do dflags <- getDynFlagsNat
                       pprPanic "getCondCode(2)(x86,sparc)" (pprPlatform (targetPlatform dflags) other)




-- @cond(Int|Flt)Code@: Turn a boolean expression into a condition, to be
-- passed back up the tree.

condIntCode :: Cond -> CmmExpr -> CmmExpr -> NatM CondCode
condIntCode cond x y = do is32Bit <- is32BitPlatform
                          condIntCode' is32Bit cond x y

condIntCode' :: Bool -> Cond -> CmmExpr -> CmmExpr -> NatM CondCode

-- memory vs immediate
condIntCode' is32Bit cond (CmmLoad x pk) (CmmLit lit)
 | is32BitLit is32Bit lit = do
    Amode x_addr x_code <- getAmode x
    let
        imm  = litToImm lit
        code = x_code `snocOL`
                  CMP (cmmTypeSize pk) (OpImm imm) (OpAddr x_addr)
    --
    return (CondCode False cond code)

-- anything vs zero, using a mask
-- TODO: Add some sanity checking!!!!
condIntCode' is32Bit cond (CmmMachOp (MO_And _) [x,o2]) (CmmLit (CmmInt 0 pk))
    | (CmmLit lit@(CmmInt mask _)) <- o2, is32BitLit is32Bit lit
    = do
      (x_reg, x_code) <- getSomeReg x
      let
         code = x_code `snocOL`
                TEST (intSize pk) (OpImm (ImmInteger mask)) (OpReg x_reg)
      --
      return (CondCode False cond code)

-- anything vs zero
condIntCode' _ cond x (CmmLit (CmmInt 0 pk)) = do
    (x_reg, x_code) <- getSomeReg x
    let
        code = x_code `snocOL`
                  TEST (intSize pk) (OpReg x_reg) (OpReg x_reg)
    --
    return (CondCode False cond code)

-- anything vs operand
condIntCode' is32Bit cond x y | isOperand is32Bit y = do
    (x_reg, x_code) <- getNonClobberedReg x
    (y_op,  y_code) <- getOperand y
    let
        code = x_code `appOL` y_code `snocOL`
                  CMP (cmmTypeSize (cmmExprType x)) y_op (OpReg x_reg)
    -- in
    return (CondCode False cond code)

-- anything vs anything
condIntCode' _ cond x y = do
  (y_reg, y_code) <- getNonClobberedReg y
  (x_op, x_code) <- getRegOrMem x
  let
        code = y_code `appOL`
               x_code `snocOL`
                  CMP (cmmTypeSize (cmmExprType x)) (OpReg y_reg) x_op
  -- in
  return (CondCode False cond code)



--------------------------------------------------------------------------------
condFltCode :: Cond -> CmmExpr -> CmmExpr -> NatM CondCode

condFltCode cond x y
  = if_sse2 condFltCode_sse2 condFltCode_x87
  where

  condFltCode_x87
    = ASSERT(cond `elem` ([EQQ, NE, LE, LTT, GE, GTT])) do
    (x_reg, x_code) <- getNonClobberedReg x
    (y_reg, y_code) <- getSomeReg y
    let
        code = x_code `appOL` y_code `snocOL`
                GCMP cond x_reg y_reg
    -- The GCMP insn does the test and sets the zero flag if comparable
    -- and true.  Hence we always supply EQQ as the condition to test.
    return (CondCode True EQQ code)

  -- in the SSE2 comparison ops (ucomiss, ucomisd) the left arg may be
  -- an operand, but the right must be a reg.  We can probably do better
  -- than this general case...
  condFltCode_sse2 = do
    (x_reg, x_code) <- getNonClobberedReg x
    (y_op, y_code) <- getOperand y
    let
        code = x_code `appOL`
               y_code `snocOL`
                  CMP (floatSize $ cmmExprWidth x) y_op (OpReg x_reg)
        -- NB(1): we need to use the unsigned comparison operators on the
        -- result of this comparison.
    -- in
    return (CondCode True (condToUnsigned cond) code)

-- -----------------------------------------------------------------------------
-- Generating assignments

-- Assignments are really at the heart of the whole code generation
-- business.  Almost all top-level nodes of any real importance are
-- assignments, which correspond to loads, stores, or register
-- transfers.  If we're really lucky, some of the register transfers
-- will go away, because we can use the destination register to
-- complete the code generation for the right hand side.  This only
-- fails when the right hand side is forced into a fixed register
-- (e.g. the result of a call).

assignMem_IntCode :: Size -> CmmExpr -> CmmExpr -> NatM InstrBlock
assignReg_IntCode :: Size -> CmmReg  -> CmmExpr -> NatM InstrBlock

assignMem_FltCode :: Size -> CmmExpr -> CmmExpr -> NatM InstrBlock
assignReg_FltCode :: Size -> CmmReg  -> CmmExpr -> NatM InstrBlock


-- integer assignment to memory

-- specific case of adding/subtracting an integer to a particular address.
-- ToDo: catch other cases where we can use an operation directly on a memory
-- address.
assignMem_IntCode pk addr (CmmMachOp op [CmmLoad addr2 _,
                                                 CmmLit (CmmInt i _)])
   | addr == addr2, pk /= II64 || is32BitInteger i,
     Just instr <- check op
   = do Amode amode code_addr <- getAmode addr
        let code = code_addr `snocOL`
                   instr pk (OpImm (ImmInt (fromIntegral i))) (OpAddr amode)
        return code
   where
        check (MO_Add _) = Just ADD
        check (MO_Sub _) = Just SUB
        check _ = Nothing
        -- ToDo: more?

-- general case
assignMem_IntCode pk addr src = do
    is32Bit <- is32BitPlatform
    Amode addr code_addr <- getAmode addr
    (code_src, op_src)   <- get_op_RI is32Bit src
    let
        code = code_src `appOL`
               code_addr `snocOL`
                  MOV pk op_src (OpAddr addr)
        -- NOTE: op_src is stable, so it will still be valid
        -- after code_addr.  This may involve the introduction
        -- of an extra MOV to a temporary register, but we hope
        -- the register allocator will get rid of it.
    --
    return code
  where
    get_op_RI :: Bool -> CmmExpr -> NatM (InstrBlock,Operand)   -- code, operator
    get_op_RI is32Bit (CmmLit lit) | is32BitLit is32Bit lit
      = return (nilOL, OpImm (litToImm lit))
    get_op_RI _ op
      = do (reg,code) <- getNonClobberedReg op
           return (code, OpReg reg)


-- Assign; dst is a reg, rhs is mem
assignReg_IntCode pk reg (CmmLoad src _) = do
  load_code <- intLoadCode (MOV pk) src
  return (load_code (getRegisterReg False{-no sse2-} reg))

-- dst is a reg, but src could be anything
assignReg_IntCode _ reg src = do
  code <- getAnyReg src
  return (code (getRegisterReg False{-no sse2-} reg))


-- Floating point assignment to memory
assignMem_FltCode pk addr src = do
  (src_reg, src_code) <- getNonClobberedReg src
  Amode addr addr_code <- getAmode addr
  use_sse2 <- sse2Enabled
  let
        code = src_code `appOL`
               addr_code `snocOL`
                if use_sse2 then MOV pk (OpReg src_reg) (OpAddr addr)
                            else GST pk src_reg addr
  return code

-- Floating point assignment to a register/temporary
assignReg_FltCode _ reg src = do
  use_sse2 <- sse2Enabled
  src_code <- getAnyReg src
  return (src_code (getRegisterReg use_sse2 reg))


genJump :: CmmExpr{-the branch target-} -> NatM InstrBlock

genJump (CmmLoad mem _) = do
  Amode target code <- getAmode mem
  return (code `snocOL` JMP (OpAddr target))

genJump (CmmLit lit) = do
  return (unitOL (JMP (OpImm (litToImm lit))))

genJump expr = do
  (reg,code) <- getSomeReg expr
  return (code `snocOL` JMP (OpReg reg))


-- -----------------------------------------------------------------------------
--  Unconditional branches

genBranch :: BlockId -> NatM InstrBlock
genBranch = return . toOL . mkJumpInstr



-- -----------------------------------------------------------------------------
--  Conditional jumps

{-
Conditional jumps are always to local labels, so we can use branch
instructions.  We peek at the arguments to decide what kind of
comparison to do.

I386: First, we have to ensure that the condition
codes are set according to the supplied comparison operation.
-}

genCondJump
    :: BlockId      -- the branch target
    -> CmmExpr      -- the condition on which to branch
    -> NatM InstrBlock

genCondJump id bool = do
  CondCode is_float cond cond_code <- getCondCode bool
  use_sse2 <- sse2Enabled
  if not is_float || not use_sse2
    then
        return (cond_code `snocOL` JXX cond id)
    else do
        lbl <- getBlockIdNat

        -- see comment with condFltReg
        let code = case cond of
                        NE  -> or_unordered
                        GU  -> plain_test
                        GEU -> plain_test
                        _   -> and_ordered

            plain_test = unitOL (
                  JXX cond id
                )
            or_unordered = toOL [
                  JXX cond id,
                  JXX PARITY id
                ]
            and_ordered = toOL [
                  JXX PARITY lbl,
                  JXX cond id,
                  JXX ALWAYS lbl,
                  NEWBLOCK lbl
                ]
        return (cond_code `appOL` code)


-- -----------------------------------------------------------------------------
--  Generating C calls

-- Now the biggest nightmare---calls.  Most of the nastiness is buried in
-- @get_arg@, which moves the arguments to the correct registers/stack
-- locations.  Apart from that, the code is easy.
--
-- (If applicable) Do not fill the delay slots here; you will confuse the
-- register allocator.

genCCall
    :: Bool                     -- 32 bit platform?
    -> CmmCallTarget            -- function to call
    -> [HintedCmmFormal]        -- where to put the result
    -> [HintedCmmActual]        -- arguments (of mixed type)
    -> NatM InstrBlock

-- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

-- Unroll memcpy calls if the source and destination pointers are at
-- least DWORD aligned and the number of bytes to copy isn't too
-- large.  Otherwise, call C's memcpy.
genCCall is32Bit (CmmPrim MO_Memcpy) _
         [CmmHinted dst _, CmmHinted src _,
          CmmHinted (CmmLit (CmmInt n _)) _,
          CmmHinted (CmmLit (CmmInt align _)) _]
    | n <= maxInlineSizeThreshold && align .&. 3 == 0 = do
        code_dst <- getAnyReg dst
        dst_r <- getNewRegNat size
        code_src <- getAnyReg src
        src_r <- getNewRegNat size
        tmp_r <- getNewRegNat size
        return $ code_dst dst_r `appOL` code_src src_r `appOL`
            go dst_r src_r tmp_r n
  where
    size = if align .&. 4 /= 0 then II32 else (archWordSize is32Bit)

    sizeBytes = fromIntegral (sizeInBytes size)

    go :: Reg -> Reg -> Reg -> Integer -> OrdList Instr
    go dst src tmp i
        | i >= sizeBytes =
            unitOL (MOV size (OpAddr src_addr) (OpReg tmp)) `appOL`
            unitOL (MOV size (OpReg tmp) (OpAddr dst_addr)) `appOL`
            go dst src tmp (i - sizeBytes)
        -- Deal with remaining bytes.
        | i >= 4 =  -- Will never happen on 32-bit
            unitOL (MOV II32 (OpAddr src_addr) (OpReg tmp)) `appOL`
            unitOL (MOV II32 (OpReg tmp) (OpAddr dst_addr)) `appOL`
            go dst src tmp (i - 4)
        | i >= 2 =
            unitOL (MOVZxL II16 (OpAddr src_addr) (OpReg tmp)) `appOL`
            unitOL (MOV II16 (OpReg tmp) (OpAddr dst_addr)) `appOL`
            go dst src tmp (i - 2)
        | i >= 1 =
            unitOL (MOVZxL II8 (OpAddr src_addr) (OpReg tmp)) `appOL`
            unitOL (MOV II8 (OpReg tmp) (OpAddr dst_addr)) `appOL`
            go dst src tmp (i - 1)
        | otherwise = nilOL
      where
        src_addr = AddrBaseIndex (EABaseReg src) EAIndexNone
                   (ImmInteger (n - i))
        dst_addr = AddrBaseIndex (EABaseReg dst) EAIndexNone
                   (ImmInteger (n - i))

genCCall _ (CmmPrim MO_Memset) _
         [CmmHinted dst _,
          CmmHinted (CmmLit (CmmInt c _)) _,
          CmmHinted (CmmLit (CmmInt n _)) _,
          CmmHinted (CmmLit (CmmInt align _)) _]
    | n <= maxInlineSizeThreshold && align .&. 3 == 0 = do
        code_dst <- getAnyReg dst
        dst_r <- getNewRegNat size
        return $ code_dst dst_r `appOL` go dst_r n
  where
    (size, val) = case align .&. 3 of
        2 -> (II16, c2)
        0 -> (II32, c4)
        _ -> (II8, c)
    c2 = c `shiftL` 8 .|. c
    c4 = c2 `shiftL` 16 .|. c2

    sizeBytes = fromIntegral (sizeInBytes size)

    go :: Reg -> Integer -> OrdList Instr
    go dst i
        -- TODO: Add movabs instruction and support 64-bit sets.
        | i >= sizeBytes =  -- This might be smaller than the below sizes
            unitOL (MOV size (OpImm (ImmInteger val)) (OpAddr dst_addr)) `appOL`
            go dst (i - sizeBytes)
        | i >= 4 =  -- Will never happen on 32-bit
            unitOL (MOV II32 (OpImm (ImmInteger c4)) (OpAddr dst_addr)) `appOL`
            go dst (i - 4)
        | i >= 2 =
            unitOL (MOV II16 (OpImm (ImmInteger c2)) (OpAddr dst_addr)) `appOL`
            go dst (i - 2)
        | i >= 1 =
            unitOL (MOV II8 (OpImm (ImmInteger c)) (OpAddr dst_addr)) `appOL`
            go dst (i - 1)
        | otherwise = nilOL
      where
        dst_addr = AddrBaseIndex (EABaseReg dst) EAIndexNone
                   (ImmInteger (n - i))

genCCall _ (CmmPrim MO_WriteBarrier) _ _ = return nilOL
        -- write barrier compiles to no code on x86/x86-64;
        -- we keep it this long in order to prevent earlier optimisations.

genCCall is32Bit (CmmPrim (MO_PopCnt width)) dest_regs@[CmmHinted dst _]
         args@[CmmHinted src _] = do
    sse4_2 <- sse4_2Enabled
    if sse4_2
        then do code_src <- getAnyReg src
                src_r <- getNewRegNat size
                return $ code_src src_r `appOL`
                    (if width == W8 then
                         -- The POPCNT instruction doesn't take a r/m8
                         unitOL (MOVZxL II8 (OpReg src_r) (OpReg src_r)) `appOL`
                         unitOL (POPCNT II16 (OpReg src_r)
                                 (getRegisterReg False (CmmLocal dst)))
                     else
                         unitOL (POPCNT size (OpReg src_r)
                                 (getRegisterReg False (CmmLocal dst))))
        else do
            dflags <- getDynFlagsNat
            targetExpr <- cmmMakeDynamicReference dflags addImportNat
                          CallReference lbl
            let target = CmmCallee targetExpr CCallConv
            genCCall is32Bit target dest_regs args
  where
    size = intSize width
    lbl = mkCmmCodeLabel primPackageId (fsLit (popCntLabel width))

genCCall is32Bit target dest_regs args
 | is32Bit   = genCCall32 target dest_regs args
 | otherwise = genCCall64 target dest_regs args

genCCall32 :: CmmCallTarget            -- function to call
           -> [HintedCmmFormal]        -- where to put the result
           -> [HintedCmmActual]        -- arguments (of mixed type)
           -> NatM InstrBlock
genCCall32 target dest_regs args =
    case (target, dest_regs) of
    -- void return type prim op
    (CmmPrim op, []) ->
        outOfLineCmmOp op Nothing args
    -- we only cope with a single result for foreign calls
    (CmmPrim op, [r_hinted@(CmmHinted r _)]) -> do
        l1 <- getNewLabelNat
        l2 <- getNewLabelNat
        sse2 <- sse2Enabled
        if sse2
          then
            outOfLineCmmOp op (Just r_hinted) args
          else case op of
              MO_F32_Sqrt -> actuallyInlineFloatOp GSQRT FF32 args
              MO_F64_Sqrt -> actuallyInlineFloatOp GSQRT FF64 args

              MO_F32_Sin  -> actuallyInlineFloatOp (\s -> GSIN s l1 l2) FF32 args
              MO_F64_Sin  -> actuallyInlineFloatOp (\s -> GSIN s l1 l2) FF64 args

              MO_F32_Cos  -> actuallyInlineFloatOp (\s -> GCOS s l1 l2) FF32 args
              MO_F64_Cos  -> actuallyInlineFloatOp (\s -> GCOS s l1 l2) FF64 args

              MO_F32_Tan  -> actuallyInlineFloatOp (\s -> GTAN s l1 l2) FF32 args
              MO_F64_Tan  -> actuallyInlineFloatOp (\s -> GTAN s l1 l2) FF64 args

              _other_op   -> outOfLineCmmOp op (Just r_hinted) args

       where
        actuallyInlineFloatOp instr size [CmmHinted x _]
              = do res <- trivialUFCode size (instr size) x
                   any <- anyReg res
                   return (any (getRegisterReg False (CmmLocal r)))

        actuallyInlineFloatOp _ _ args
              = panic $ "genCCall.actuallyInlineFloatOp: bad number of arguments! ("
                      ++ show (length args) ++ ")"
    _ -> do
        let
            -- Align stack to 16n for calls, assuming a starting stack
            -- alignment of 16n - word_size on procedure entry. Which we
            -- maintiain. See Note [rts/StgCRun.c : Stack Alignment on X86]
            sizes               = map (arg_size . cmmExprType . hintlessCmm) (reverse args)
            raw_arg_size        = sum sizes + wORD_SIZE
            arg_pad_size        = (roundTo 16 $ raw_arg_size) - raw_arg_size
            tot_arg_size        = raw_arg_size + arg_pad_size - wORD_SIZE
        delta0 <- getDeltaNat
        setDeltaNat (delta0 - arg_pad_size)

        use_sse2 <- sse2Enabled
        push_codes <- mapM (push_arg use_sse2) (reverse args)
        delta <- getDeltaNat

        -- in
        -- deal with static vs dynamic call targets
        (callinsns,cconv) <-
          case target of
            CmmCallee (CmmLit (CmmLabel lbl)) conv
               -> -- ToDo: stdcall arg sizes
                  return (unitOL (CALL (Left fn_imm) []), conv)
               where fn_imm = ImmCLbl lbl
            CmmCallee expr conv
               -> do { (dyn_r, dyn_c) <- getSomeReg expr
                     ; ASSERT( isWord32 (cmmExprType expr) )
                       return (dyn_c `snocOL` CALL (Right dyn_r) [], conv) }
            CmmPrim _
                -> panic $ "genCCall: Can't handle CmmPrim call type here, error "
                            ++ "probably because too many return values."

        let push_code
                | arg_pad_size /= 0
                = toOL [SUB II32 (OpImm (ImmInt arg_pad_size)) (OpReg esp),
                        DELTA (delta0 - arg_pad_size)]
                  `appOL` concatOL push_codes
                | otherwise
                = concatOL push_codes

              -- Deallocate parameters after call for ccall;
              -- but not for stdcall (callee does it)
              --
              -- We have to pop any stack padding we added
              -- even if we are doing stdcall, though (#5052)
            pop_size | cconv /= StdCallConv = tot_arg_size
                     | otherwise = arg_pad_size

            call = callinsns `appOL`
                   toOL (
                      (if pop_size==0 then [] else
                       [ADD II32 (OpImm (ImmInt pop_size)) (OpReg esp)])
                      ++
                      [DELTA (delta + tot_arg_size)]
                   )
        -- in
        setDeltaNat (delta + tot_arg_size)

        let
            -- assign the results, if necessary
            assign_code []     = nilOL
            assign_code [CmmHinted dest _hint]
              | isFloatType ty =
                 if use_sse2
                    then let tmp_amode = AddrBaseIndex (EABaseReg esp)
                                                       EAIndexNone
                                                       (ImmInt 0)
                             sz = floatSize w
                         in toOL [ SUB II32 (OpImm (ImmInt b)) (OpReg esp),
                                   GST sz fake0 tmp_amode,
                                   MOV sz (OpAddr tmp_amode) (OpReg r_dest),
                                   ADD II32 (OpImm (ImmInt b)) (OpReg esp)]
                    else unitOL (GMOV fake0 r_dest)
              | isWord64 ty    = toOL [MOV II32 (OpReg eax) (OpReg r_dest),
                                        MOV II32 (OpReg edx) (OpReg r_dest_hi)]
              | otherwise      = unitOL (MOV (intSize w) (OpReg eax) (OpReg r_dest))
              where
                    ty = localRegType dest
                    w  = typeWidth ty
                    b  = widthInBytes w
                    r_dest_hi = getHiVRegFromLo r_dest
                    r_dest    = getRegisterReg use_sse2 (CmmLocal dest)
            assign_code many = pprPanic "genCCall.assign_code - too many return values:" (ppr many)

        return (push_code `appOL`
                call `appOL`
                assign_code dest_regs)

      where
        arg_size :: CmmType -> Int  -- Width in bytes
        arg_size ty = widthInBytes (typeWidth ty)

        roundTo a x | x `mod` a == 0 = x
                    | otherwise = x + a - (x `mod` a)

        push_arg :: Bool -> HintedCmmActual {-current argument-}
                        -> NatM InstrBlock  -- code

        push_arg use_sse2 (CmmHinted arg _hint) -- we don't need the hints on x86
          | isWord64 arg_ty = do
            ChildCode64 code r_lo <- iselExpr64 arg
            delta <- getDeltaNat
            setDeltaNat (delta - 8)
            let
                r_hi = getHiVRegFromLo r_lo
            -- in
            return (       code `appOL`
                           toOL [PUSH II32 (OpReg r_hi), DELTA (delta - 4),
                                 PUSH II32 (OpReg r_lo), DELTA (delta - 8),
                                 DELTA (delta-8)]
                )

          | isFloatType arg_ty = do
            (reg, code) <- getSomeReg arg
            delta <- getDeltaNat
            setDeltaNat (delta-size)
            return (code `appOL`
                            toOL [SUB II32 (OpImm (ImmInt size)) (OpReg esp),
                                  DELTA (delta-size),
                                  let addr = AddrBaseIndex (EABaseReg esp)
                                                            EAIndexNone
                                                            (ImmInt 0)
                                      size = floatSize (typeWidth arg_ty)
                                  in
                                  if use_sse2
                                     then MOV size (OpReg reg) (OpAddr addr)
                                     else GST size reg addr
                                 ]
                           )

          | otherwise = do
            (operand, code) <- getOperand arg
            delta <- getDeltaNat
            setDeltaNat (delta-size)
            return (code `snocOL`
                    PUSH II32 operand `snocOL`
                    DELTA (delta-size))

          where
             arg_ty = cmmExprType arg
             size = arg_size arg_ty -- Byte size

genCCall64 :: CmmCallTarget            -- function to call
           -> [HintedCmmFormal]        -- where to put the result
           -> [HintedCmmActual]        -- arguments (of mixed type)
           -> NatM InstrBlock
genCCall64 target dest_regs args =
    case (target, dest_regs) of

    (CmmPrim op, []) ->
        -- void return type prim op
        outOfLineCmmOp op Nothing args

    (CmmPrim op, [res]) ->
        -- we only cope with a single result for foreign calls
        outOfLineCmmOp op (Just res) args

    _ -> do
        -- load up the register arguments
        (stack_args, aregs, fregs, load_args_code)
             <- load_args args allArgRegs allFPArgRegs nilOL

        let
            fp_regs_used  = reverse (drop (length fregs) (reverse allFPArgRegs))
            int_regs_used = reverse (drop (length aregs) (reverse allArgRegs))
            arg_regs = [eax] ++ int_regs_used ++ fp_regs_used
                    -- for annotating the call instruction with
            sse_regs = length fp_regs_used
            tot_arg_size = arg_size * length stack_args


        -- Align stack to 16n for calls, assuming a starting stack
        -- alignment of 16n - word_size on procedure entry. Which we
        -- maintiain. See Note [rts/StgCRun.c : Stack Alignment on X86]
        (real_size, adjust_rsp) <-
            if (tot_arg_size + wORD_SIZE) `rem` 16 == 0
                then return (tot_arg_size, nilOL)
                else do -- we need to adjust...
                    delta <- getDeltaNat
                    setDeltaNat (delta - wORD_SIZE)
                    return (tot_arg_size + wORD_SIZE, toOL [
                                    SUB II64 (OpImm (ImmInt wORD_SIZE)) (OpReg rsp),
                                    DELTA (delta - wORD_SIZE) ])

        -- push the stack args, right to left
        push_code <- push_args (reverse stack_args) nilOL
        delta <- getDeltaNat

        -- deal with static vs dynamic call targets
        (callinsns,_cconv) <-
          case target of
            CmmCallee (CmmLit (CmmLabel lbl)) conv
               -> -- ToDo: stdcall arg sizes
                  return (unitOL (CALL (Left fn_imm) arg_regs), conv)
               where fn_imm = ImmCLbl lbl
            CmmCallee expr conv
               -> do (dyn_r, dyn_c) <- getSomeReg expr
                     return (dyn_c `snocOL` CALL (Right dyn_r) arg_regs, conv)
            CmmPrim _
                -> panic $ "genCCall: Can't handle CmmPrim call type here, error "
                            ++ "probably because too many return values."

        let
            -- The x86_64 ABI requires us to set %al to the number of SSE2
            -- registers that contain arguments, if the called routine
            -- is a varargs function.  We don't know whether it's a
            -- varargs function or not, so we have to assume it is.
            --
            -- It's not safe to omit this assignment, even if the number
            -- of SSE2 regs in use is zero.  If %al is larger than 8
            -- on entry to a varargs function, seg faults ensue.
            assign_eax n = unitOL (MOV II32 (OpImm (ImmInt n)) (OpReg eax))

        let call = callinsns `appOL`
                   toOL (
                        -- Deallocate parameters after call for ccall;
                        -- stdcall has callee do it, but is not supported on
                        -- x86_64 target (see #3336)
                      (if real_size==0 then [] else
                       [ADD (intSize wordWidth) (OpImm (ImmInt real_size)) (OpReg esp)])
                      ++
                      [DELTA (delta + real_size)]
                   )
        -- in
        setDeltaNat (delta + real_size)

        let
            -- assign the results, if necessary
            assign_code []     = nilOL
            assign_code [CmmHinted dest _hint] =
              case typeWidth rep of
                    W32 | isFloatType rep -> unitOL (MOV (floatSize W32) (OpReg xmm0) (OpReg r_dest))
                    W64 | isFloatType rep -> unitOL (MOV (floatSize W64) (OpReg xmm0) (OpReg r_dest))
                    _ -> unitOL (MOV (cmmTypeSize rep) (OpReg rax) (OpReg r_dest))
              where
                    rep = localRegType dest
                    r_dest = getRegisterReg True (CmmLocal dest)
            assign_code _many = panic "genCCall.assign_code many"

        return (load_args_code      `appOL`
                adjust_rsp          `appOL`
                push_code           `appOL`
                assign_eax sse_regs `appOL`
                call                `appOL`
                assign_code dest_regs)

      where
        arg_size = 8 -- always, at the mo

        load_args :: [CmmHinted CmmExpr]
                  -> [Reg]                  -- int regs avail for args
                  -> [Reg]                  -- FP regs avail for args
                  -> InstrBlock
                  -> NatM ([CmmHinted CmmExpr],[Reg],[Reg],InstrBlock)
        load_args args [] [] code     =  return (args, [], [], code)
            -- no more regs to use
        load_args [] aregs fregs code =  return ([], aregs, fregs, code)
            -- no more args to push
        load_args ((CmmHinted arg hint) : rest) aregs fregs code
            | isFloatType arg_rep =
            case fregs of
              [] -> push_this_arg
              (r:rs) -> do
                 arg_code <- getAnyReg arg
                 load_args rest aregs rs (code `appOL` arg_code r)
            | otherwise =
            case aregs of
              [] -> push_this_arg
              (r:rs) -> do
                 arg_code <- getAnyReg arg
                 load_args rest rs fregs (code `appOL` arg_code r)
            where
              arg_rep = cmmExprType arg

              push_this_arg = do
                (args',ars,frs,code') <- load_args rest aregs fregs code
                return ((CmmHinted arg hint):args', ars, frs, code')

        push_args [] code = return code
        push_args ((CmmHinted arg _):rest) code
           | isFloatType arg_rep = do
             (arg_reg, arg_code) <- getSomeReg arg
             delta <- getDeltaNat
             setDeltaNat (delta-arg_size)
             dflags <- getDynFlagsNat
             let platform = targetPlatform dflags
                 code' = code `appOL` arg_code `appOL` toOL [
                            SUB (intSize wordWidth) (OpImm (ImmInt arg_size)) (OpReg rsp) ,
                            DELTA (delta-arg_size),
                            MOV (floatSize width) (OpReg arg_reg) (OpAddr  (spRel platform 0))]
             push_args rest code'

           | otherwise = do
           -- we only ever generate word-sized function arguments.  Promotion
           -- has already happened: our Int8# type is kept sign-extended
           -- in an Int#, for example.
             ASSERT(width == W64) return ()
             (arg_op, arg_code) <- getOperand arg
             delta <- getDeltaNat
             setDeltaNat (delta-arg_size)
             let code' = code `appOL` arg_code `appOL` toOL [
                                    PUSH II64 arg_op,
                                    DELTA (delta-arg_size)]
             push_args rest code'
            where
              arg_rep = cmmExprType arg
              width = typeWidth arg_rep

-- | We're willing to inline and unroll memcpy/memset calls that touch
-- at most these many bytes.  This threshold is the same as the one
-- used by GCC and LLVM.
maxInlineSizeThreshold :: Integer
maxInlineSizeThreshold = 128

outOfLineCmmOp :: CallishMachOp -> Maybe HintedCmmFormal -> [HintedCmmActual] -> NatM InstrBlock
outOfLineCmmOp mop res args
  = do
      dflags <- getDynFlagsNat
      targetExpr <- cmmMakeDynamicReference dflags addImportNat CallReference lbl
      let target = CmmCallee targetExpr CCallConv

      stmtToInstrs (CmmCall target (catMaybes [res]) args' CmmMayReturn)
  where
        -- Assume we can call these functions directly, and that they're not in a dynamic library.
        -- TODO: Why is this ok? Under linux this code will be in libm.so
        --       Is is because they're really implemented as a primitive instruction by the assembler??  -- BL 2009/12/31
        lbl = mkForeignLabel fn Nothing ForeignLabelInThisPackage IsFunction

        args' = case mop of
                    MO_Memcpy    -> init args
                    MO_Memset    -> init args
                    MO_Memmove   -> init args
                    _            -> args

        fn = case mop of
              MO_F32_Sqrt  -> fsLit "sqrtf"
              MO_F32_Sin   -> fsLit "sinf"
              MO_F32_Cos   -> fsLit "cosf"
              MO_F32_Tan   -> fsLit "tanf"
              MO_F32_Exp   -> fsLit "expf"
              MO_F32_Log   -> fsLit "logf"

              MO_F32_Asin  -> fsLit "asinf"
              MO_F32_Acos  -> fsLit "acosf"
              MO_F32_Atan  -> fsLit "atanf"

              MO_F32_Sinh  -> fsLit "sinhf"
              MO_F32_Cosh  -> fsLit "coshf"
              MO_F32_Tanh  -> fsLit "tanhf"
              MO_F32_Pwr   -> fsLit "powf"

              MO_F64_Sqrt  -> fsLit "sqrt"
              MO_F64_Sin   -> fsLit "sin"
              MO_F64_Cos   -> fsLit "cos"
              MO_F64_Tan   -> fsLit "tan"
              MO_F64_Exp   -> fsLit "exp"
              MO_F64_Log   -> fsLit "log"

              MO_F64_Asin  -> fsLit "asin"
              MO_F64_Acos  -> fsLit "acos"
              MO_F64_Atan  -> fsLit "atan"

              MO_F64_Sinh  -> fsLit "sinh"
              MO_F64_Cosh  -> fsLit "cosh"
              MO_F64_Tanh  -> fsLit "tanh"
              MO_F64_Pwr   -> fsLit "pow"

              MO_Memcpy    -> fsLit "memcpy"
              MO_Memset    -> fsLit "memset"
              MO_Memmove   -> fsLit "memmove"

              MO_PopCnt _  -> fsLit "popcnt"

              MO_WriteBarrier ->
                  panic $ "outOfLineCmmOp: MO_WriteBarrier not supported here"
              MO_Touch ->
                  panic $ "outOfLineCmmOp: MO_Touch not supported here"

-- -----------------------------------------------------------------------------
-- Generating a table-branch

genSwitch :: CmmExpr -> [Maybe BlockId] -> NatM InstrBlock

genSwitch expr ids
  | opt_PIC
  = do
        (reg,e_code) <- getSomeReg expr
        lbl <- getNewLabelNat
        dflags <- getDynFlagsNat
        dynRef <- cmmMakeDynamicReference dflags addImportNat DataReference lbl
        (tableReg,t_code) <- getSomeReg $ dynRef
        let op = OpAddr (AddrBaseIndex (EABaseReg tableReg)
                                       (EAIndex reg wORD_SIZE) (ImmInt 0))

        return $ if target32Bit (targetPlatform dflags)
                 then e_code `appOL` t_code `appOL` toOL [
                                ADD (intSize wordWidth) op (OpReg tableReg),
                                JMP_TBL (OpReg tableReg) ids ReadOnlyData lbl
                       ]
                 else case platformOS (targetPlatform dflags) of
                      OSDarwin ->
                          -- on Mac OS X/x86_64, put the jump table
                          -- in the text section to work around a
                          -- limitation of the linker.
                          -- ld64 is unable to handle the relocations for
                          --     .quad L1 - L0
                          -- if L0 is not preceded by a non-anonymous
                          -- label in its section.
                          e_code `appOL` t_code `appOL` toOL [
                                   ADD (intSize wordWidth) op (OpReg tableReg),
                                   JMP_TBL (OpReg tableReg) ids Text lbl
                           ]
                      _ ->
                          -- HACK: On x86_64 binutils<2.17 is only able
                          -- to generate PC32 relocations, hence we only
                          -- get 32-bit offsets in the jump table. As
                          -- these offsets are always negative we need
                          -- to properly sign extend them to 64-bit.
                          -- This hack should be removed in conjunction
                          -- with the hack in PprMach.hs/pprDataItem
                          -- once binutils 2.17 is standard.
                          e_code `appOL` t_code `appOL` toOL [
                                   MOVSxL II32 op (OpReg reg),
                                   ADD (intSize wordWidth) (OpReg reg) (OpReg tableReg),
                                   JMP_TBL (OpReg tableReg) ids ReadOnlyData lbl
                           ]
  | otherwise
  = do
        (reg,e_code) <- getSomeReg expr
        lbl <- getNewLabelNat
        let op = OpAddr (AddrBaseIndex EABaseNone (EAIndex reg wORD_SIZE) (ImmCLbl lbl))
            code = e_code `appOL` toOL [
                    JMP_TBL op ids ReadOnlyData lbl
                 ]
        -- in
        return code

generateJumpTableForInstr :: Instr -> Maybe (NatCmmDecl (Alignment, CmmStatics) Instr)
generateJumpTableForInstr (JMP_TBL _ ids section lbl) = Just (createJumpTable ids section lbl)
generateJumpTableForInstr _ = Nothing

createJumpTable :: [Maybe BlockId] -> Section -> CLabel -> GenCmmDecl (Alignment, CmmStatics) h g
createJumpTable ids section lbl
    = let jumpTable
            | opt_PIC =
                  let jumpTableEntryRel Nothing
                          = CmmStaticLit (CmmInt 0 wordWidth)
                      jumpTableEntryRel (Just blockid)
                          = CmmStaticLit (CmmLabelDiffOff blockLabel lbl 0)
                          where blockLabel = mkAsmTempLabel (getUnique blockid)
                  in map jumpTableEntryRel ids
            | otherwise = map jumpTableEntry ids
      in CmmData section (1, Statics lbl jumpTable)

-- -----------------------------------------------------------------------------
-- 'condIntReg' and 'condFltReg': condition codes into registers

-- Turn those condition codes into integers now (when they appear on
-- the right hand side of an assignment).
--
-- (If applicable) Do not fill the delay slots here; you will confuse the
-- register allocator.

condIntReg :: Cond -> CmmExpr -> CmmExpr -> NatM Register

condIntReg cond x y = do
  CondCode _ cond cond_code <- condIntCode cond x y
  tmp <- getNewRegNat II8
  let
        code dst = cond_code `appOL` toOL [
                    SETCC cond (OpReg tmp),
                    MOVZxL II8 (OpReg tmp) (OpReg dst)
                  ]
  -- in
  return (Any II32 code)



condFltReg :: Bool -> Cond -> CmmExpr -> CmmExpr -> NatM Register
condFltReg is32Bit cond x y = if_sse2 condFltReg_sse2 condFltReg_x87
 where
  condFltReg_x87 = do
    CondCode _ cond cond_code <- condFltCode cond x y
    tmp <- getNewRegNat II8
    let
        code dst = cond_code `appOL` toOL [
                    SETCC cond (OpReg tmp),
                    MOVZxL II8 (OpReg tmp) (OpReg dst)
                  ]
    -- in
    return (Any II32 code)

  condFltReg_sse2 = do
    CondCode _ cond cond_code <- condFltCode cond x y
    tmp1 <- getNewRegNat (archWordSize is32Bit)
    tmp2 <- getNewRegNat (archWordSize is32Bit)
    let
        -- We have to worry about unordered operands (eg. comparisons
        -- against NaN).  If the operands are unordered, the comparison
        -- sets the parity flag, carry flag and zero flag.
        -- All comparisons are supposed to return false for unordered
        -- operands except for !=, which returns true.
        --
        -- Optimisation: we don't have to test the parity flag if we
        -- know the test has already excluded the unordered case: eg >
        -- and >= test for a zero carry flag, which can only occur for
        -- ordered operands.
        --
        -- ToDo: by reversing comparisons we could avoid testing the
        -- parity flag in more cases.

        code dst =
           cond_code `appOL`
             (case cond of
                NE  -> or_unordered dst
                GU  -> plain_test   dst
                GEU -> plain_test   dst
                _   -> and_ordered  dst)

        plain_test dst = toOL [
                    SETCC cond (OpReg tmp1),
                    MOVZxL II8 (OpReg tmp1) (OpReg dst)
                 ]
        or_unordered dst = toOL [
                    SETCC cond (OpReg tmp1),
                    SETCC PARITY (OpReg tmp2),
                    OR II8 (OpReg tmp1) (OpReg tmp2),
                    MOVZxL II8 (OpReg tmp2) (OpReg dst)
                  ]
        and_ordered dst = toOL [
                    SETCC cond (OpReg tmp1),
                    SETCC NOTPARITY (OpReg tmp2),
                    AND II8 (OpReg tmp1) (OpReg tmp2),
                    MOVZxL II8 (OpReg tmp2) (OpReg dst)
                  ]
    -- in
    return (Any II32 code)


-- -----------------------------------------------------------------------------
-- 'trivial*Code': deal with trivial instructions

-- Trivial (dyadic: 'trivialCode', floating-point: 'trivialFCode',
-- unary: 'trivialUCode', unary fl-pt:'trivialUFCode') instructions.
-- Only look for constants on the right hand side, because that's
-- where the generic optimizer will have put them.

-- Similarly, for unary instructions, we don't have to worry about
-- matching an StInt as the argument, because genericOpt will already
-- have handled the constant-folding.


{-
The Rules of the Game are:

* You cannot assume anything about the destination register dst;
  it may be anything, including a fixed reg.

* You may compute an operand into a fixed reg, but you may not
  subsequently change the contents of that fixed reg.  If you
  want to do so, first copy the value either to a temporary
  or into dst.  You are free to modify dst even if it happens
  to be a fixed reg -- that's not your problem.

* You cannot assume that a fixed reg will stay live over an
  arbitrary computation.  The same applies to the dst reg.

* Temporary regs obtained from getNewRegNat are distinct from
  each other and from all other regs, and stay live over
  arbitrary computations.

--------------------

SDM's version of The Rules:

* If getRegister returns Any, that means it can generate correct
  code which places the result in any register, period.  Even if that
  register happens to be read during the computation.

  Corollary #1: this means that if you are generating code for an
  operation with two arbitrary operands, you cannot assign the result
  of the first operand into the destination register before computing
  the second operand.  The second operand might require the old value
  of the destination register.

  Corollary #2: A function might be able to generate more efficient
  code if it knows the destination register is a new temporary (and
  therefore not read by any of the sub-computations).

* If getRegister returns Any, then the code it generates may modify only:
        (a) fresh temporaries
        (b) the destination register
        (c) known registers (eg. %ecx is used by shifts)
  In particular, it may *not* modify global registers, unless the global
  register happens to be the destination register.
-}

trivialCode :: Width -> (Operand -> Operand -> Instr)
            -> Maybe (Operand -> Operand -> Instr)
            -> CmmExpr -> CmmExpr -> NatM Register
trivialCode width instr m a b
    = do is32Bit <- is32BitPlatform
         trivialCode' is32Bit width instr m a b

trivialCode' :: Bool -> Width -> (Operand -> Operand -> Instr)
             -> Maybe (Operand -> Operand -> Instr)
             -> CmmExpr -> CmmExpr -> NatM Register
trivialCode' is32Bit width _ (Just revinstr) (CmmLit lit_a) b
  | is32BitLit is32Bit lit_a = do
  b_code <- getAnyReg b
  let
       code dst
         = b_code dst `snocOL`
           revinstr (OpImm (litToImm lit_a)) (OpReg dst)
  -- in
  return (Any (intSize width) code)

trivialCode' _ width instr _ a b
  = genTrivialCode (intSize width) instr a b

-- This is re-used for floating pt instructions too.
genTrivialCode :: Size -> (Operand -> Operand -> Instr)
               -> CmmExpr -> CmmExpr -> NatM Register
genTrivialCode rep instr a b = do
  (b_op, b_code) <- getNonClobberedOperand b
  a_code <- getAnyReg a
  tmp <- getNewRegNat rep
  let
     -- We want the value of b to stay alive across the computation of a.
     -- But, we want to calculate a straight into the destination register,
     -- because the instruction only has two operands (dst := dst `op` src).
     -- The troublesome case is when the result of b is in the same register
     -- as the destination reg.  In this case, we have to save b in a
     -- new temporary across the computation of a.
     code dst
        | dst `regClashesWithOp` b_op =
                b_code `appOL`
                unitOL (MOV rep b_op (OpReg tmp)) `appOL`
                a_code dst `snocOL`
                instr (OpReg tmp) (OpReg dst)
        | otherwise =
                b_code `appOL`
                a_code dst `snocOL`
                instr b_op (OpReg dst)
  -- in
  return (Any rep code)

regClashesWithOp :: Reg -> Operand -> Bool
reg `regClashesWithOp` OpReg reg2   = reg == reg2
reg `regClashesWithOp` OpAddr amode = any (==reg) (addrModeRegs amode)
_   `regClashesWithOp` _            = False

-----------

trivialUCode :: Size -> (Operand -> Instr)
             -> CmmExpr -> NatM Register
trivialUCode rep instr x = do
  x_code <- getAnyReg x
  let
     code dst =
        x_code dst `snocOL`
        instr (OpReg dst)
  return (Any rep code)

-----------

trivialFCode_x87 :: (Size -> Reg -> Reg -> Reg -> Instr)
                 -> CmmExpr -> CmmExpr -> NatM Register
trivialFCode_x87 instr x y = do
  (x_reg, x_code) <- getNonClobberedReg x -- these work for float regs too
  (y_reg, y_code) <- getSomeReg y
  let
     size = FF80 -- always, on x87
     code dst =
        x_code `appOL`
        y_code `snocOL`
        instr size x_reg y_reg dst
  return (Any size code)

trivialFCode_sse2 :: Width -> (Size -> Operand -> Operand -> Instr)
                  -> CmmExpr -> CmmExpr -> NatM Register
trivialFCode_sse2 pk instr x y
    = genTrivialCode size (instr size) x y
    where size = floatSize pk


trivialUFCode :: Size -> (Reg -> Reg -> Instr) -> CmmExpr -> NatM Register
trivialUFCode size instr x = do
  (x_reg, x_code) <- getSomeReg x
  let
     code dst =
        x_code `snocOL`
        instr x_reg dst
  -- in
  return (Any size code)


--------------------------------------------------------------------------------
coerceInt2FP :: Width -> Width -> CmmExpr -> NatM Register
coerceInt2FP from to x = if_sse2 coerce_sse2 coerce_x87
 where
   coerce_x87 = do
     (x_reg, x_code) <- getSomeReg x
     let
           opc  = case to of W32 -> GITOF; W64 -> GITOD;
                             n -> panic $ "coerceInt2FP.x87: unhandled width ("
                                         ++ show n ++ ")"
           code dst = x_code `snocOL` opc x_reg dst
        -- ToDo: works for non-II32 reps?
     return (Any FF80 code)

   coerce_sse2 = do
     (x_op, x_code) <- getOperand x  -- ToDo: could be a safe operand
     let
           opc  = case to of W32 -> CVTSI2SS; W64 -> CVTSI2SD
                             n -> panic $ "coerceInt2FP.sse: unhandled width ("
                                         ++ show n ++ ")"
           code dst = x_code `snocOL` opc (intSize from) x_op dst
     -- in
     return (Any (floatSize to) code)
        -- works even if the destination rep is <II32

--------------------------------------------------------------------------------
coerceFP2Int :: Width -> Width -> CmmExpr -> NatM Register
coerceFP2Int from to x = if_sse2 coerceFP2Int_sse2 coerceFP2Int_x87
 where
   coerceFP2Int_x87 = do
     (x_reg, x_code) <- getSomeReg x
     let
           opc  = case from of W32 -> GFTOI; W64 -> GDTOI
                               n -> panic $ "coerceFP2Int.x87: unhandled width ("
                                           ++ show n ++ ")"
           code dst = x_code `snocOL` opc x_reg dst
        -- ToDo: works for non-II32 reps?
     -- in
     return (Any (intSize to) code)

   coerceFP2Int_sse2 = do
     (x_op, x_code) <- getOperand x  -- ToDo: could be a safe operand
     let
           opc  = case from of W32 -> CVTTSS2SIQ; W64 -> CVTTSD2SIQ;
                               n -> panic $ "coerceFP2Init.sse: unhandled width ("
                                           ++ show n ++ ")"
           code dst = x_code `snocOL` opc (intSize to) x_op dst
     -- in
     return (Any (intSize to) code)
         -- works even if the destination rep is <II32


--------------------------------------------------------------------------------
coerceFP2FP :: Width -> CmmExpr -> NatM Register
coerceFP2FP to x = do
  use_sse2 <- sse2Enabled
  (x_reg, x_code) <- getSomeReg x
  let
        opc | use_sse2  = case to of W32 -> CVTSD2SS; W64 -> CVTSS2SD;
                                     n -> panic $ "coerceFP2FP: unhandled width ("
                                                 ++ show n ++ ")"
            | otherwise = GDTOF
        code dst = x_code `snocOL` opc x_reg dst
  -- in
  return (Any (if use_sse2 then floatSize to else FF80) code)

--------------------------------------------------------------------------------

sse2NegCode :: Width -> CmmExpr -> NatM Register
sse2NegCode w x = do
  let sz = floatSize w
  x_code <- getAnyReg x
  -- This is how gcc does it, so it can't be that bad:
  let
    const | FF32 <- sz = CmmInt 0x80000000 W32
          | otherwise  = CmmInt 0x8000000000000000 W64
  Amode amode amode_code <- memConstant (widthInBytes w) const
  tmp <- getNewRegNat sz
  let
    code dst = x_code dst `appOL` amode_code `appOL` toOL [
        MOV sz (OpAddr amode) (OpReg tmp),
        XOR sz (OpReg tmp) (OpReg dst)
        ]
  --
  return (Any sz code)
