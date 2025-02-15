--------------------------------------------------------------------------------
-- | Pretty print LLVM IR Code.
--

module Llvm.PpLlvm (

    -- * Top level LLVM objects.
    ppLlvmModule,
    ppLlvmComments,
    ppLlvmComment,
    ppLlvmGlobals,
    ppLlvmGlobal,
    ppLlvmAlias,
    ppLlvmAliases,
    ppLlvmFunctionDecls,
    ppLlvmFunctionDecl,
    ppLlvmFunctions,
    ppLlvmFunction,

    ) where

#include "HsVersions.h"

import Llvm.AbsSyn
import Llvm.Types

import Data.List ( intersperse )
import Outputable
import Unique
import FastString ( sLit )

--------------------------------------------------------------------------------
-- * Top Level Print functions
--------------------------------------------------------------------------------

-- | Print out a whole LLVM module.
ppLlvmModule :: LlvmModule -> SDoc
ppLlvmModule (LlvmModule comments aliases globals decls funcs)
  = ppLlvmComments comments
    $+$ empty
    $+$ ppLlvmAliases aliases
    $+$ empty
    $+$ ppLlvmGlobals globals
    $+$ empty
    $+$ ppLlvmFunctionDecls decls
    $+$ empty
    $+$ ppLlvmFunctions funcs

-- | Print out a multi-line comment, can be inside a function or on its own
ppLlvmComments :: [LMString] -> SDoc
ppLlvmComments comments = vcat $ map ppLlvmComment comments

-- | Print out a comment, can be inside a function or on its own
ppLlvmComment :: LMString -> SDoc
ppLlvmComment com = semi <+> ftext com


-- | Print out a list of global mutable variable definitions
ppLlvmGlobals :: [LMGlobal] -> SDoc
ppLlvmGlobals ls = vcat $ map ppLlvmGlobal ls

-- | Print out a global mutable variable definition
ppLlvmGlobal :: LMGlobal -> SDoc
ppLlvmGlobal (LMGlobal var@(LMGlobalVar _ _ link x a c) dat) =
    let sect = case x of
            Just x' -> text ", section" <+> doubleQuotes (ftext x')
            Nothing -> empty

        align = case a of
            Just a' -> text ", align" <+> int a'
            Nothing -> empty

        rhs = case dat of
            Just stat -> ppr stat
            Nothing   -> ppr (pLower $ getVarType var)

        const' = if c then text "constant" else text "global"

    in ppAssignment var $ ppr link <+> const' <+> rhs <> sect <> align

ppLlvmGlobal (LMGlobal var@(LMMetaVar _) (Just val)) =
  ppAssignment var (ppr val)

ppLlvmGlobal (LMGlobal var val) = error $ "Non Global var ppr as global! "
                                          ++ showSDoc (ppr var) ++ " " ++ showSDoc (ppr val)


-- | Print out a list of LLVM type aliases.
ppLlvmAliases :: [LlvmAlias] -> SDoc
ppLlvmAliases tys = vcat $ map ppLlvmAlias tys

-- | Print out an LLVM type alias.
ppLlvmAlias :: LlvmAlias -> SDoc
ppLlvmAlias (name, ty) = text "%" <> ftext name <+> equals <+> text "type" <+> ppr ty


-- | Print out a list of function definitions.
ppLlvmFunctions :: LlvmFunctions -> SDoc
ppLlvmFunctions funcs = vcat $ map ppLlvmFunction funcs

-- | Print out a function definition.
ppLlvmFunction :: LlvmFunction -> SDoc
ppLlvmFunction (LlvmFunction dec args attrs sec body instr) =
    let attrDoc = ppSpaceJoin attrs
        secDoc = case sec of
                      Just s' -> text "section" <+> (doubleQuotes $ ftext s')
                      Nothing -> empty
    in text "define" <+> ppLlvmFunctionHeader dec args
        <+> attrDoc <+> secDoc
        $+$ lbrace
        $+$ ppLlvmBlocks instr body
        $+$ rbrace

-- | Print out a function defenition header.
ppLlvmFunctionHeader :: LlvmFunctionDecl -> [LMString] -> SDoc
ppLlvmFunctionHeader (LlvmFunctionDecl n l c r varg p a) args
  = let varg' = case varg of
                      VarArgs | null p    -> sLit "..."
                              | otherwise -> sLit ", ..."
                      _otherwise          -> sLit ""
        align = case a of
                     Just a' -> text " align " <> ppr a'
                     Nothing -> empty
        args' = map (\((ty,p),n) -> ppr ty <+> ppSpaceJoin p <+> char '%'
                                    <> ftext n)
                    (zip p args)
    in ppr l <+> ppr c <+> ppr r <+> char '@' <> ftext n <> lparen <>
        (hsep $ punctuate comma args') <> ptext varg' <> rparen <> align


-- | Print out a list of function declaration.
ppLlvmFunctionDecls :: LlvmFunctionDecls -> SDoc
ppLlvmFunctionDecls decs = vcat $ map ppLlvmFunctionDecl decs

-- | Print out a function declaration.
-- Declarations define the function type but don't define the actual body of
-- the function.
ppLlvmFunctionDecl :: LlvmFunctionDecl -> SDoc
ppLlvmFunctionDecl (LlvmFunctionDecl n l c r varg p a)
  = let varg' = case varg of
                      VarArgs | null p    -> sLit "..."
                              | otherwise -> sLit ", ..."
                      _otherwise          -> sLit ""
        align = case a of
                     Just a' -> text " align" <+> ppr a'
                     Nothing -> empty
        args = hcat $ intersperse (comma <> space) $
                  map (\(t,a) -> ppr t <+> ppSpaceJoin a) p
    in text "declare" <+> ppr l <+> ppr c <+> ppr r <+> text "@" <>
        ftext n <> lparen <> args <> ptext varg' <> rparen <> align


-- | Print out a list of LLVM blocks.
ppLlvmBlocks :: Maybe Int -> LlvmBlocks -> SDoc
ppLlvmBlocks tick blocks = vcat $ map (ppLlvmBlock tick) blocks

-- | Print out an LLVM block.
-- It must be part of a function definition.
ppLlvmBlock :: Maybe Int -> LlvmBlock -> SDoc
ppLlvmBlock tick (LlvmBlock blockId stmts)
  = ppLlvmStatement (MkLabel blockId)
        $+$ nest 4 (vcat $ map ppStmt stmts)
  where ppStmt | Just n <- tick  = ppLlvmStatementDbg n
               | otherwise       = ppLlvmStatement

-- | Print out an LLVM statement with debug annotation
ppLlvmStatementDbg :: Int -> LlvmStatement -> SDoc
ppLlvmStatementDbg _ stmt@(Comment _) = ppLlvmStatement stmt
ppLlvmStatementDbg _ stmt@(MkLabel _) = ppLlvmStatement stmt
ppLlvmStatementDbg n stmt             = ppLlvmStatement stmt <> text ", !dbg !" <> ppr n

-- | Print out an LLVM statement.
ppLlvmStatement :: LlvmStatement -> SDoc
ppLlvmStatement stmt
  = case stmt of
        Assignment  dst expr      -> ppAssignment dst (ppLlvmExpression expr)
        Branch      target        -> ppBranch target
        BranchIf    cond ifT ifF  -> ppBranchIf cond ifT ifF
        Comment     comments      -> ppLlvmComments comments
        MkLabel     label         -> pprUnique label <> colon
        Store       value ptr     -> ppStore value ptr
        Switch      scrut def tgs -> ppSwitch scrut def tgs
        Return      result        -> ppReturn result
        Expr        expr          -> ppLlvmExpression expr
        Unreachable               -> text "unreachable"
        Nop                       -> empty


-- | Print out an LLVM expression.
ppLlvmExpression :: LlvmExpression -> SDoc
ppLlvmExpression expr
  = case expr of
        Alloca     tp amount        -> ppAlloca tp amount
        LlvmOp     op left right    -> ppMachOp op left right
        Call       tp fp args attrs -> ppCall tp fp args attrs
        Cast       op from to       -> ppCast op from to
        Compare    op left right    -> ppCmpOp op left right
        GetElemPtr inb ptr indexes  -> ppGetElementPtr inb ptr indexes
        Load       ptr              -> ppLoad ptr
        Malloc     tp amount        -> ppMalloc tp amount
        Phi        tp precessors    -> ppPhi tp precessors
        Asm        asm c ty v se sk -> ppAsm asm c ty v se sk


--------------------------------------------------------------------------------
-- * Individual print functions
--------------------------------------------------------------------------------

-- | Should always be a function pointer. So a global var of function type
-- (since globals are always pointers) or a local var of pointer function type.
ppCall :: LlvmCallType -> LlvmVar -> [LlvmVar] -> [LlvmFuncAttr] -> SDoc
ppCall ct fptr vals attrs = case fptr of
                           --
    -- if local var function pointer, unwrap
    LMLocalVar _ (LMPointer (LMFunction d)) -> ppCall' d

    -- should be function type otherwise
    LMGlobalVar _ (LMFunction d) _ _ _ _    -> ppCall' d

    -- not pointer or function, so error
    _other -> error $ "ppCall called with non LMFunction type!\nMust be "
                ++ " called with either global var of function type or "
                ++ "local var of pointer function type."

    where
        ppCall' (LlvmFunctionDecl _ _ cc ret argTy params _) =
            let tc = if ct == TailCall then text "tail " else empty
                ppValues = ppCommaJoin vals
                ppArgTy  = (ppCommaJoin $ map fst params) <>
                           (case argTy of
                               VarArgs   -> text ", ..."
                               FixedArgs -> empty)
                fnty = space <> lparen <> ppArgTy <> rparen <> text "*"
                attrDoc = ppSpaceJoin attrs
            in  tc <> text "call" <+> ppr cc <+> ppr ret
                    <> fnty <+> ppName fptr <> lparen <+> ppValues
                    <+> rparen <+> attrDoc


ppMachOp :: LlvmMachOp -> LlvmVar -> LlvmVar -> SDoc
ppMachOp op left right =
  (ppr op) <+> (ppr (getVarType left)) <+> ppName left
        <> comma <+> ppName right


ppCmpOp :: LlvmCmpOp -> LlvmVar -> LlvmVar -> SDoc
ppCmpOp op left right =
  let cmpOp
        | isInt (getVarType left) && isInt (getVarType right) = text "icmp"
        | isFloat (getVarType left) && isFloat (getVarType right) = text "fcmp"
        | otherwise = text "icmp" -- Just continue as its much easier to debug
        {-
        | otherwise = error ("can't compare different types, left = "
                ++ (show $ getVarType left) ++ ", right = "
                ++ (show $ getVarType right))
        -}
  in cmpOp <+> ppr op <+> ppr (getVarType left)
        <+> ppName left <> comma <+> ppName right


ppAssignment :: LlvmVar -> SDoc -> SDoc
ppAssignment var expr = ppName var <+> equals <+> expr


ppLoad :: LlvmVar -> SDoc
ppLoad var = text "load" <+> ppr var


ppStore :: LlvmVar -> LlvmVar -> SDoc
ppStore val dst = text "store" <+> ppr val <> comma <+> ppr dst


ppCast :: LlvmCastOp -> LlvmVar -> LlvmType -> SDoc
ppCast op from to = ppr op <+> ppr from <+> text "to" <+> ppr to


ppMalloc :: LlvmType -> Int -> SDoc
ppMalloc tp amount =
  let amount' = LMLitVar $ LMIntLit (toInteger amount) i32
  in text "malloc" <+> ppr tp <> comma <+> ppr amount'


ppAlloca :: LlvmType -> Int -> SDoc
ppAlloca tp amount =
  let amount' = LMLitVar $ LMIntLit (toInteger amount) i32
  in text "alloca" <+> ppr tp <> comma <+> ppr amount'


ppGetElementPtr :: Bool -> LlvmVar -> [LlvmVar] -> SDoc
ppGetElementPtr inb ptr idx =
  let indexes = comma <+> ppCommaJoin idx
      inbound = if inb then text "inbounds" else empty
  in text "getelementptr" <+> inbound <+> ppr ptr <> indexes


ppReturn :: Maybe LlvmVar -> SDoc
ppReturn (Just var) = text "ret" <+> ppr var
ppReturn Nothing    = text "ret" <+> ppr LMVoid


ppBranch :: LlvmVar -> SDoc
ppBranch var = text "br" <+> ppr var


ppBranchIf :: LlvmVar -> LlvmVar -> LlvmVar -> SDoc
ppBranchIf cond trueT falseT
  = text "br" <+> ppr cond <> comma <+> ppr trueT <> comma <+> ppr falseT


ppPhi :: LlvmType -> [(LlvmVar,LlvmVar)] -> SDoc
ppPhi tp preds =
  let ppPreds (val, label) = brackets $ ppName val <> comma <+> ppName label
  in text "phi" <+> ppr tp <+> hsep (punctuate comma $ map ppPreds preds)


ppSwitch :: LlvmVar -> LlvmVar -> [(LlvmVar,LlvmVar)] -> SDoc
ppSwitch scrut dflt targets =
  let ppTarget  (val, lab) = ppr val <> comma <+> ppr lab
      ppTargets  xs        = brackets $ vcat (map ppTarget xs)
  in text "switch" <+> ppr scrut <> comma <+> ppr dflt
        <+> ppTargets targets


ppAsm :: LMString -> LMString -> LlvmType -> [LlvmVar] -> Bool -> Bool -> SDoc
ppAsm asm constraints rty vars sideeffect alignstack =
  let asm'  = doubleQuotes $ ftext asm
      cons  = doubleQuotes $ ftext constraints
      rty'  = ppr rty
      vars' = lparen <+> ppCommaJoin vars <+> rparen
      side  = if sideeffect then text "sideeffect" else empty
      align = if alignstack then text "alignstack" else empty
  in text "call" <+> rty' <+> text "asm" <+> side <+> align <+> asm' <> comma
        <+> cons <> vars'

