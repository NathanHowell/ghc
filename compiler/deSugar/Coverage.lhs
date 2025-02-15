%
% (c) Galois, 2006
% (c) University of Glasgow, 2007
%
\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module Coverage (addTicksToBinds, hpcInitCode) where

import Type
import HsSyn
import Module
import Outputable
import DynFlags
import Control.Monad
import SrcLoc
import ErrUtils
import NameSet hiding (FreeVars)
import Name
import Bag
import CostCentre
import CoreSyn
import Id
import VarSet
import Data.List
import FastString
import HscTypes	
import Platform
import StaticFlags
import TyCon
import Unique
import BasicTypes
import MonadUtils
import Maybes
import CLabel
import Util

import Data.Array
import System.Directory ( createDirectoryIfMissing )

import Trace.Hpc.Mix
import Trace.Hpc.Util

import BreakArray 
import Data.HashTable   ( hashString )
import Data.Map (Map)
import qualified Data.Map as Map
\end{code}


%************************************************************************
%*									*
%*              The main function: addTicksToBinds
%*									*
%************************************************************************

\begin{code}
addTicksToBinds
        :: DynFlags
        -> Module
        -> ModLocation          -- ... off the current module
        -> NameSet              -- Exported Ids.  When we call addTicksToBinds,
                                -- isExportedId doesn't work yet (the desugarer
                                -- hasn't set it), so we have to work from this set.
        -> [TyCon]              -- Type constructor in this module
        -> LHsBinds Id
        -> IO (LHsBinds Id, HpcInfo, ModBreaks)

addTicksToBinds dflags mod mod_loc exports tyCons binds =

 case ml_hs_file mod_loc of
   Nothing        -> return (binds, emptyHpcInfo False, emptyModBreaks)
   Just orig_file -> do

     if "boot" `isSuffixOf` orig_file
         then return (binds, emptyHpcInfo False, emptyModBreaks)
         else do
   
     let  orig_file2 = guessSourceFile binds orig_file

          (binds1,_,st)
		 = unTM (addTickLHsBinds binds) 
		   (TTE
                      { fileName     = mkFastString orig_file2
		      , declPath     = []
                      , dflags       = dflags
                      , exports      = exports
                      , inScope      = emptyVarSet
                      , blackList    = Map.fromList
                                          [ (getSrcSpan (tyConName tyCon),())
                                          | tyCon <- tyCons ]
                      , density      = mkDensity dflags
                      , this_mod     = mod
                      , tickishType  = case hscTarget dflags of
                          HscInterpreted          -> Breakpoints
                          _ | opt_Hpc             -> HpcTicks
                            | opt_SccProfilingOn  -> ProfNotes
                            | otherwise           -> SourceNotes
                       })
		   (TT 
		      { tickBoxCount = 0
		      , mixEntries   = []
		      })

     let entries = reverse $ mixEntries st

     let count = tickBoxCount st
     hashNo <- writeMixEntries dflags mod count entries orig_file2
     modBreaks <- mkModBreaks count entries

     doIfSet_dyn dflags Opt_D_dump_ticked $ printDump (pprLHsBinds binds1)
   
     return (binds1, HpcInfo count hashNo, modBreaks)


guessSourceFile :: LHsBinds Id -> FilePath -> FilePath
guessSourceFile binds orig_file =
     -- Try look for a file generated from a .hsc file to a
     -- .hs file, by peeking ahead.
     let top_pos = catMaybes $ foldrBag (\ (L pos _) rest ->
                                 srcSpanFileName_maybe pos : rest) [] binds
     in
     case top_pos of
        (file_name:_) | ".hsc" `isSuffixOf` unpackFS file_name
                      -> unpackFS file_name
        _ -> orig_file


mkModBreaks :: Int -> [MixEntry_] -> IO ModBreaks
mkModBreaks count entries = do
  breakArray <- newBreakArray $ length entries
  let
         locsTicks = listArray (0,count-1) [ span  | (span,_,_,_)  <- entries ]
         varsTicks = listArray (0,count-1) [ vars  | (_,_,vars,_)  <- entries ]
         declsTicks= listArray (0,count-1) [ decls | (_,decls,_,_) <- entries ]
         modBreaks = emptyModBreaks 
                     { modBreaks_flags = breakArray 
                     , modBreaks_locs  = locsTicks 
                     , modBreaks_vars  = varsTicks
                     , modBreaks_decls = declsTicks
                     } 
  --
  return modBreaks


writeMixEntries :: DynFlags -> Module -> Int -> [MixEntry_] -> FilePath -> IO Int
writeMixEntries dflags mod count entries filename
  | not opt_Hpc = return 0
  | otherwise   = do
        let
            hpc_dir = hpcDir dflags
            mod_name = moduleNameString (moduleName mod)

            hpc_mod_dir
              | modulePackageId mod == mainPackageId  = hpc_dir
              | otherwise = hpc_dir ++ "/" ++ packageIdString (modulePackageId mod)
   
            tabStop = 8 -- <tab> counts as a normal char in GHC's location ranges.

        createDirectoryIfMissing True hpc_mod_dir
        modTime <- getModificationTime filename
        let entries' = [ (hpcPos, box) 
                       | (span,_,_,box) <- entries, hpcPos <- [mkHpcPos span] ]
        when (length entries' /= count) $ do
          panic "the number of .mix entries are inconsistent"
        let hashNo = mixHash filename modTime tabStop entries'
        mixCreate hpc_mod_dir mod_name 
                       $ Mix filename modTime (toHash hashNo) tabStop entries'
        return hashNo


-- -----------------------------------------------------------------------------
-- TickDensity: where to insert ticks

data TickDensity
  = TickForCoverage       -- for Hpc
  | TickForBreakPoints    -- for GHCi
  | TickAllFunctions      -- for -prof-auto-all
  | TickTopFunctions      -- for -prof-auto-top
  | TickExportedFunctions -- for -prof-auto-exported
  | TickCallSites         -- for stack tracing
  deriving Eq

mkDensity :: DynFlags -> TickDensity
mkDensity dflags
  | opt_Hpc                              = TickForCoverage
  | HscInterpreted  <- hscTarget dflags  = TickForBreakPoints
  | ProfAutoAll     <- profAuto dflags   = TickAllFunctions
  | ProfAutoTop     <- profAuto dflags   = TickTopFunctions
  | ProfAutoExports <- profAuto dflags   = TickExportedFunctions
  | HscLlvm         <- hscTarget dflags  = TickAllFunctions
  | ProfAutoCalls   <- profAuto dflags   = TickCallSites
  | otherwise = panic "density"

  -- ToDo: -fhpc is taking priority over -fprof-auto here.  It seems
  -- that coverage works perfectly well with profiling, but you don't
  -- get any auto-generated SCCs.  It would make perfect sense to
  -- allow both of them, and indeed to combine some of the other flags
  -- (-fprof-auto-calls -fprof-auto-top, for example)

-- | Decide whether to add a tick to a binding or not.
shouldTickBind  :: TickDensity
                -> Bool         -- top level?
                -> Bool         -- exported?
                -> Bool         -- simple pat bind?
                -> Bool         -- INLINE pragma?
                -> Bool

shouldTickBind density top_lev exported simple_pat inline
 = case density of
      TickForBreakPoints    -> not simple_pat
        -- we never add breakpoints to simple pattern bindings
        -- (there's always a tick on the rhs anyway).
      TickAllFunctions      -> not inline
      TickTopFunctions      -> top_lev && not inline
      TickExportedFunctions -> exported && not inline
      TickForCoverage       -> True
      TickCallSites         -> False

shouldTickPatBind :: TickDensity -> Bool -> Bool
shouldTickPatBind density top_lev
  = case density of
      TickForBreakPoints    -> False
      TickAllFunctions      -> True
      TickTopFunctions      -> top_lev
      TickExportedFunctions -> False
      TickForCoverage       -> False
      TickCallSites         -> False

-- -----------------------------------------------------------------------------
-- Adding ticks to bindings

addTickLHsBinds :: LHsBinds Id -> TM (LHsBinds Id)
addTickLHsBinds binds = mapBagM addTickLHsBind binds

addTickLHsBind :: LHsBind Id -> TM (LHsBind Id)
addTickLHsBind (L pos bind@(AbsBinds { abs_binds   = binds,
                                       abs_exports = abs_exports })) = do
  withEnv add_exports $ do
  binds' <- addTickLHsBinds binds
  return $ L pos $ bind { abs_binds = binds' }
 where
   -- in AbsBinds, the Id on each binding is not the actual top-level
   -- Id that we are defining, they are related by the abs_exports
   -- field of AbsBinds.  So if we're doing TickExportedFunctions we need
   -- to add the local Ids to the set of exported Names so that we know to
   -- tick the right bindings.
   add_exports env =
     env{ exports = exports env `addListToNameSet`
                      [ idName mid
                      | ABE{ abe_poly = pid, abe_mono = mid } <- abs_exports
                      , idName pid `elemNameSet` (exports env) ] }

addTickLHsBind (L pos (funBind@(FunBind { fun_id = (L _ id)  }))) = do
  let name = getOccString id
  decl_path <- getPathEntry

  (fvs, (MatchGroup matches' ty)) <- 
        getFreeVars $
        addPathEntry name $
        addTickMatchGroup False (fun_matches funBind)

  blackListed <- isBlackListed pos
  density <- getDensity
  exported_names <- liftM exports getEnv

  -- We don't want to generate code for blacklisted positions
  -- We don't want redundant ticks on simple pattern bindings
  -- We don't want to tick non-exported bindings in TickExportedFunctions
  let simple = isSimplePatBind funBind
      toplev = null decl_path
      exported = idName id `elemNameSet` exported_names
      inline   = {- pprTrace "inline" (ppr id <+> ppr (idInlinePragma id)) $ -}
                 isAnyInlinePragma (idInlinePragma id)

  tick <- if not blackListed &&
               shouldTickBind density toplev exported simple inline
             then
                bindTick density name pos fvs
             else
                return Nothing

  return $ L pos $ funBind { fun_matches = MatchGroup matches' ty
                           , fun_tick = tick }

   where
   -- a binding is a simple pattern binding if it is a funbind with zero patterns
   isSimplePatBind :: HsBind a -> Bool
   isSimplePatBind funBind = matchGroupArity (fun_matches funBind) == 0

-- TODO: Revisit this
addTickLHsBind (L pos (pat@(PatBind { pat_lhs = lhs, pat_rhs = rhs }))) = do
  let name = "(...)"
  (fvs, rhs') <- getFreeVars $ addPathEntry name $ addTickGRHSs False False rhs

  density <- getDensity
  decl_path <- getPathEntry
  let top_lev = null decl_path
  let add_ticks = shouldTickPatBind density top_lev

  tickish <- if add_ticks
                then bindTick density name pos fvs
                else return Nothing

  let patvars = map getOccString (collectPatBinders lhs)
  patvar_ticks <- if add_ticks
                     then mapM (\v -> bindTick density v pos fvs) patvars
                     else return []

  return $ L pos $ pat { pat_rhs = rhs',
                         pat_ticks = (tickish, patvar_ticks)}

-- Only internal stuff, not from source, uses VarBind, so we ignore it.
addTickLHsBind var_bind@(L _ (VarBind {})) = return var_bind


bindTick :: TickDensity -> String -> SrcSpan -> FreeVars -> TM (Maybe (Tickish Id))
bindTick density name pos fvs = do
  decl_path <- getPathEntry
  let
      toplev        = null decl_path
      count_entries = toplev || density == TickAllFunctions
      top_only      = density /= TickAllFunctions
      box_label     = if toplev then TopLevelBox [name]
                                else LocalBox (decl_path ++ [name])
  --
  allocATickBox box_label count_entries top_only pos fvs


-- -----------------------------------------------------------------------------
-- Decorate an LHsExpr with ticks

-- selectively add ticks to interesting expressions
addTickLHsExpr :: LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExpr e@(L pos e0) = do
  d <- getDensity
  case d of
    TickForBreakPoints | isGoodBreakExpr e0 -> tick_it
    TickForCoverage    -> tick_it
    TickCallSites      | isCallSite e0      -> tick_it
    _other             -> dont_tick_it
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- Add a tick to an expression which is the RHS of an equation or a binding.
-- We always consider these to be breakpoints, unless the expression is a 'let'
-- (because the body will definitely have a tick somewhere).  ToDo: perhaps
-- we should treat 'case' and 'if' the same way?
addTickLHsExprRHS :: LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExprRHS e@(L pos e0) = do
  d <- getDensity
  case d of
     TickForBreakPoints | HsLet{} <- e0 -> dont_tick_it
                        | otherwise     -> tick_it
     TickForCoverage -> tick_it
     TickCallSites   | isCallSite e0 -> tick_it
     _other          -> dont_tick_it
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- The inner expression of an evaluation context:
--    let binds in [], ( [] )
-- we never tick these if we're doing HPC, but otherwise
-- we treat it like an ordinary expression.
addTickLHsExprEvalInner :: LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExprEvalInner e = do
   d <- getDensity
   case d of
     TickForCoverage -> addTickLHsExprNever e
     _otherwise      -> addTickLHsExpr e

-- | A let body is treated differently from addTickLHsExprEvalInner
-- above with TickForBreakPoints, because for breakpoints we always
-- want to tick the body, even if it is not a redex.  See test
-- break012.  This gives the user the opportunity to inspect the
-- values of the let-bound variables.
addTickLHsExprLetBody :: LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExprLetBody e@(L pos e0) = do
  d <- getDensity
  case d of
     TickForBreakPoints | HsLet{} <- e0 -> dont_tick_it
                        | otherwise     -> tick_it
     _other -> addTickLHsExprEvalInner e
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- version of addTick that does not actually add a tick,
-- because the scope of this tick is completely subsumed by 
-- another.
addTickLHsExprNever :: LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExprNever (L pos e0) = do
    e1 <- addTickHsExpr e0
    return $ L pos e1

-- general heuristic: expressions which do not denote values are good break points
isGoodBreakExpr :: HsExpr Id -> Bool
isGoodBreakExpr (HsApp {})     = True
isGoodBreakExpr (OpApp {})     = True
isGoodBreakExpr (NegApp {})    = True
isGoodBreakExpr (HsIf {})      = True
isGoodBreakExpr (HsCase {})    = True
isGoodBreakExpr (RecordCon {}) = True
isGoodBreakExpr (RecordUpd {}) = True
isGoodBreakExpr (ArithSeq {})  = True
isGoodBreakExpr (PArrSeq {})   = True
isGoodBreakExpr _other         = False 

isCallSite :: HsExpr Id -> Bool
isCallSite HsApp{}  = True
isCallSite OpApp{}  = True
isCallSite _ = False

addTickLHsExprOptAlt :: Bool -> LHsExpr Id -> TM (LHsExpr Id)
addTickLHsExprOptAlt oneOfMany (L pos e0)
  = ifDensity TickForCoverage
        (allocTickBox (ExpBox oneOfMany) False False pos $ addTickHsExpr e0)
        (addTickLHsExpr (L pos e0))

addBinTickLHsExpr :: (Bool -> BoxLabel) -> LHsExpr Id -> TM (LHsExpr Id)
addBinTickLHsExpr boxLabel (L pos e0)
  = ifDensity TickForCoverage
        (allocBinTickBox boxLabel pos $ addTickHsExpr e0)
        (addTickLHsExpr (L pos e0))


-- -----------------------------------------------------------------------------
-- Decoarate an HsExpr with ticks

addTickHsExpr :: HsExpr Id -> TM (HsExpr Id)
addTickHsExpr e@(HsVar id) = do freeVar id; return e
addTickHsExpr e@(HsIPVar _) = return e
addTickHsExpr e@(HsOverLit _) = return e
addTickHsExpr e@(HsLit _) = return e
addTickHsExpr (HsLam matchgroup) =
        liftM HsLam (addTickMatchGroup True matchgroup)
addTickHsExpr (HsApp e1 e2) =
	liftM2 HsApp (addTickLHsExprNever e1) (addTickLHsExpr e2)
addTickHsExpr (OpApp e1 e2 fix e3) = 
	liftM4 OpApp 
		(addTickLHsExpr e1) 
		(addTickLHsExprNever e2)
		(return fix)
                (addTickLHsExpr e3)
addTickHsExpr (NegApp e neg) =
	liftM2 NegApp
		(addTickLHsExpr e) 
		(addTickSyntaxExpr hpcSrcSpan neg)
addTickHsExpr (HsPar e) =
        liftM HsPar (addTickLHsExprEvalInner e)
addTickHsExpr (SectionL e1 e2) =
	liftM2 SectionL
		(addTickLHsExpr e1)
                (addTickLHsExprNever e2)
addTickHsExpr (SectionR e1 e2) = 
	liftM2 SectionR
                (addTickLHsExprNever e1)
		(addTickLHsExpr e2)
addTickHsExpr (ExplicitTuple es boxity) =
        liftM2 ExplicitTuple
                (mapM addTickTupArg es)
                (return boxity)
addTickHsExpr (HsCase e mgs) = 
	liftM2 HsCase
                (addTickLHsExpr e) -- not an EvalInner; e might not necessarily
                                   -- be evaluated.
                (addTickMatchGroup False mgs)
addTickHsExpr (HsIf cnd e1 e2 e3) = 
	liftM3 (HsIf cnd)
		(addBinTickLHsExpr (BinBox CondBinBox) e1)
		(addTickLHsExprOptAlt True e2)
		(addTickLHsExprOptAlt True e3)
addTickHsExpr (HsLet binds e) =
	bindLocals (collectLocalBinders binds) $
	liftM2 HsLet
		(addTickHsLocalBinds binds) -- to think about: !patterns.
                (addTickLHsExprLetBody e)
addTickHsExpr (HsDo cxt stmts srcloc) 
  = do { (stmts', _) <- addTickLStmts' forQual stmts (return ())
       ; return (HsDo cxt stmts' srcloc) }
  where
	forQual = case cxt of
		    ListComp -> Just $ BinBox QualBinBox
		    _        -> Nothing
addTickHsExpr (ExplicitList ty es) = 
	liftM2 ExplicitList
		(return ty)
		(mapM (addTickLHsExpr) es)
addTickHsExpr (ExplicitPArr ty es) =
	liftM2 ExplicitPArr
		(return ty)
		(mapM (addTickLHsExpr) es)
addTickHsExpr (RecordCon id ty rec_binds) = 
	liftM3 RecordCon
		(return id)
		(return ty)
		(addTickHsRecordBinds rec_binds)
addTickHsExpr (RecordUpd e rec_binds cons tys1 tys2) =
	liftM5 RecordUpd
		(addTickLHsExpr e)
		(addTickHsRecordBinds rec_binds)
		(return cons) (return tys1) (return tys2)

addTickHsExpr (ExprWithTySigOut e ty) =
	liftM2 ExprWithTySigOut
		(addTickLHsExprNever e) -- No need to tick the inner expression
				    -- for expressions with signatures
		(return ty)
addTickHsExpr (ArithSeq	 ty arith_seq) =
	liftM2 ArithSeq	
		(return ty)
		(addTickArithSeqInfo arith_seq)
addTickHsExpr (HsTickPragma _ (L pos e0)) = do
    e2 <- allocTickBox (ExpBox False) False False pos $
                addTickHsExpr e0
    return $ unLoc e2
addTickHsExpr (PArrSeq	 ty arith_seq) =
	liftM2 PArrSeq	
		(return ty)
		(addTickArithSeqInfo arith_seq)
addTickHsExpr (HsSCC nm e) =
        liftM2 HsSCC 
                (return nm)
                (addTickLHsExpr e)
addTickHsExpr (HsCoreAnn nm e) = 
        liftM2 HsCoreAnn 
                (return nm)
                (addTickLHsExpr e)
addTickHsExpr e@(HsBracket     {}) = return e
addTickHsExpr e@(HsBracketOut  {}) = return e
addTickHsExpr e@(HsSpliceE  {}) = return e
addTickHsExpr (HsProc pat cmdtop) =
	liftM2 HsProc
		(addTickLPat pat)
		(liftL (addTickHsCmdTop) cmdtop)
addTickHsExpr (HsWrap w e) = 
	liftM2 HsWrap
		(return w)
		(addTickHsExpr e)	-- explicitly no tick on inside

addTickHsExpr e@(HsType _) = return e

-- Others dhould never happen in expression content.
addTickHsExpr e  = pprPanic "addTickHsExpr" (ppr e)

addTickTupArg :: HsTupArg Id -> TM (HsTupArg Id)
addTickTupArg (Present e)  = do { e' <- addTickLHsExpr e; return (Present e') }
addTickTupArg (Missing ty) = return (Missing ty)

addTickMatchGroup :: Bool{-is lambda-} -> MatchGroup Id -> TM (MatchGroup Id)
addTickMatchGroup is_lam (MatchGroup matches ty) = do
  let isOneOfMany = matchesOneOfMany matches
  matches' <- mapM (liftL (addTickMatch isOneOfMany is_lam)) matches
  return $ MatchGroup matches' ty

addTickMatch :: Bool -> Bool -> Match Id -> TM (Match Id)
addTickMatch isOneOfMany isLambda (Match pats opSig gRHSs) =
  bindLocals (collectPatsBinders pats) $ do
    gRHSs' <- addTickGRHSs isOneOfMany isLambda gRHSs
    return $ Match pats opSig gRHSs'

addTickGRHSs :: Bool -> Bool -> GRHSs Id -> TM (GRHSs Id)
addTickGRHSs isOneOfMany isLambda (GRHSs guarded local_binds) = do
  bindLocals binders $ do
    local_binds' <- addTickHsLocalBinds local_binds
    guarded' <- mapM (liftL (addTickGRHS isOneOfMany isLambda)) guarded
    return $ GRHSs guarded' local_binds'
  where
    binders = collectLocalBinders local_binds

addTickGRHS :: Bool -> Bool -> GRHS Id -> TM (GRHS Id)
addTickGRHS isOneOfMany isLambda (GRHS stmts expr) = do
  (stmts',expr') <- addTickLStmts' (Just $ BinBox $ GuardBinBox) stmts
                        (addTickGRHSBody isOneOfMany isLambda expr)
  return $ GRHS stmts' expr'

addTickGRHSBody :: Bool -> Bool -> LHsExpr Id -> TM (LHsExpr Id)
addTickGRHSBody isOneOfMany isLambda expr@(L pos e0) = do
  d <- getDensity
  case d of
    TickForCoverage  -> addTickLHsExprOptAlt isOneOfMany expr
    TickAllFunctions | isLambda ->
       addPathEntry "\\" $
         allocTickBox (ExpBox False) True{-count-} False{-not top-} pos $
           addTickHsExpr e0
    _otherwise ->
       addTickLHsExprRHS expr

addTickLStmts :: (Maybe (Bool -> BoxLabel)) -> [LStmt Id] -> TM [LStmt Id]
addTickLStmts isGuard stmts = do
  (stmts, _) <- addTickLStmts' isGuard stmts (return ())
  return stmts

addTickLStmts' :: (Maybe (Bool -> BoxLabel)) -> [LStmt Id] -> TM a 
               -> TM ([LStmt Id], a)
addTickLStmts' isGuard lstmts res
  = bindLocals (collectLStmtsBinders lstmts) $ 
    do { lstmts' <- mapM (liftL (addTickStmt isGuard)) lstmts
       ; a <- res
       ; return (lstmts', a) }

addTickStmt :: (Maybe (Bool -> BoxLabel)) -> Stmt Id -> TM (Stmt Id)
addTickStmt _isGuard (LastStmt e ret) = do
	liftM2 LastStmt
		(addTickLHsExpr e)
		(addTickSyntaxExpr hpcSrcSpan ret)
addTickStmt _isGuard (BindStmt pat e bind fail) = do
	liftM4 BindStmt
		(addTickLPat pat)
		(addTickLHsExprRHS e)
		(addTickSyntaxExpr hpcSrcSpan bind)
		(addTickSyntaxExpr hpcSrcSpan fail)
addTickStmt isGuard (ExprStmt e bind' guard' ty) = do
	liftM4 ExprStmt
		(addTick isGuard e)
		(addTickSyntaxExpr hpcSrcSpan bind')
		(addTickSyntaxExpr hpcSrcSpan guard')
		(return ty)
addTickStmt _isGuard (LetStmt binds) = do
	liftM LetStmt
		(addTickHsLocalBinds binds)
addTickStmt isGuard (ParStmt pairs mzipExpr bindExpr returnExpr) = do
    liftM4 ParStmt 
        (mapM (addTickStmtAndBinders isGuard) pairs)
        (addTickSyntaxExpr hpcSrcSpan mzipExpr)
        (addTickSyntaxExpr hpcSrcSpan bindExpr)
        (addTickSyntaxExpr hpcSrcSpan returnExpr)

addTickStmt isGuard stmt@(TransStmt { trS_stmts = stmts
                                    , trS_by = by, trS_using = using
                                    , trS_ret = returnExpr, trS_bind = bindExpr
                                    , trS_fmap = liftMExpr }) = do
    t_s <- addTickLStmts isGuard stmts
    t_y <- fmapMaybeM  addTickLHsExprRHS by
    t_u <- addTickLHsExprRHS using
    t_f <- addTickSyntaxExpr hpcSrcSpan returnExpr
    t_b <- addTickSyntaxExpr hpcSrcSpan bindExpr
    t_m <- addTickSyntaxExpr hpcSrcSpan liftMExpr
    return $ stmt { trS_stmts = t_s, trS_by = t_y, trS_using = t_u
                  , trS_ret = t_f, trS_bind = t_b, trS_fmap = t_m }

addTickStmt isGuard stmt@(RecStmt {})
  = do { stmts' <- addTickLStmts isGuard (recS_stmts stmt)
       ; ret'   <- addTickSyntaxExpr hpcSrcSpan (recS_ret_fn stmt)
       ; mfix'  <- addTickSyntaxExpr hpcSrcSpan (recS_mfix_fn stmt)
       ; bind'  <- addTickSyntaxExpr hpcSrcSpan (recS_bind_fn stmt)
       ; return (stmt { recS_stmts = stmts', recS_ret_fn = ret'
                      , recS_mfix_fn = mfix', recS_bind_fn = bind' }) }

addTick :: Maybe (Bool -> BoxLabel) -> LHsExpr Id -> TM (LHsExpr Id)
addTick isGuard e | Just fn <- isGuard = addBinTickLHsExpr fn e
                  | otherwise          = addTickLHsExprRHS e

addTickStmtAndBinders :: Maybe (Bool -> BoxLabel) -> ([LStmt Id], a) 
                      -> TM ([LStmt Id], a)
addTickStmtAndBinders isGuard (stmts, ids) = 
    liftM2 (,) 
        (addTickLStmts isGuard stmts)
        (return ids)

addTickHsLocalBinds :: HsLocalBinds Id -> TM (HsLocalBinds Id)
addTickHsLocalBinds (HsValBinds binds) = 
	liftM HsValBinds 
		(addTickHsValBinds binds)
addTickHsLocalBinds (HsIPBinds binds)  = 
	liftM HsIPBinds 
		(addTickHsIPBinds binds)
addTickHsLocalBinds (EmptyLocalBinds)  = return EmptyLocalBinds

addTickHsValBinds :: HsValBindsLR Id a -> TM (HsValBindsLR Id b)
addTickHsValBinds (ValBindsOut binds sigs) =
	liftM2 ValBindsOut
		(mapM (\ (rec,binds') -> 
				liftM2 (,)
					(return rec)
					(addTickLHsBinds binds'))
			binds)
		(return sigs)
addTickHsValBinds _ = panic "addTickHsValBinds"

addTickHsIPBinds :: HsIPBinds Id -> TM (HsIPBinds Id)
addTickHsIPBinds (IPBinds ipbinds dictbinds) =
	liftM2 IPBinds
		(mapM (liftL (addTickIPBind)) ipbinds)
		(return dictbinds)

addTickIPBind :: IPBind Id -> TM (IPBind Id)
addTickIPBind (IPBind nm e) =
	liftM2 IPBind
		(return nm)
		(addTickLHsExpr e)

-- There is no location here, so we might need to use a context location??
addTickSyntaxExpr :: SrcSpan -> SyntaxExpr Id -> TM (SyntaxExpr Id)
addTickSyntaxExpr pos x = do
	L _ x' <- addTickLHsExpr (L pos x)
	return $ x'
-- we do not walk into patterns.
addTickLPat :: LPat Id -> TM (LPat Id)
addTickLPat pat = return pat

addTickHsCmdTop :: HsCmdTop Id -> TM (HsCmdTop Id)
addTickHsCmdTop (HsCmdTop cmd tys ty syntaxtable) =
	liftM4 HsCmdTop
		(addTickLHsCmd cmd)
		(return tys)
		(return ty)
		(return syntaxtable)

addTickLHsCmd ::  LHsCmd Id -> TM (LHsCmd Id)
addTickLHsCmd (L pos c0) = do
        c1 <- addTickHsCmd c0
        return $ L pos c1 

addTickHsCmd :: HsCmd Id -> TM (HsCmd Id)
addTickHsCmd (HsLam matchgroup) =
        liftM HsLam (addTickCmdMatchGroup matchgroup)
addTickHsCmd (HsApp c e) = 
	liftM2 HsApp (addTickLHsCmd c) (addTickLHsExpr e)
addTickHsCmd (OpApp e1 c2 fix c3) = 
	liftM4 OpApp 
		(addTickLHsExpr e1) 
		(addTickLHsCmd c2)
		(return fix)
		(addTickLHsCmd c3)
addTickHsCmd (HsPar e) = liftM HsPar (addTickLHsCmd e)
addTickHsCmd (HsCase e mgs) = 
	liftM2 HsCase
		(addTickLHsExpr e) 
		(addTickCmdMatchGroup mgs)
addTickHsCmd (HsIf cnd e1 c2 c3) = 
	liftM3 (HsIf cnd)
		(addBinTickLHsExpr (BinBox CondBinBox) e1)
		(addTickLHsCmd c2)
		(addTickLHsCmd c3)
addTickHsCmd (HsLet binds c) =
	bindLocals (collectLocalBinders binds) $
	liftM2 HsLet
		(addTickHsLocalBinds binds) -- to think about: !patterns.
                (addTickLHsCmd c)
addTickHsCmd (HsDo cxt stmts srcloc)
  = do { (stmts', _) <- addTickLCmdStmts' stmts (return ())
       ; return (HsDo cxt stmts' srcloc) }

addTickHsCmd (HsArrApp	 e1 e2 ty1 arr_ty lr) = 
        liftM5 HsArrApp
	       (addTickLHsExpr e1)
	       (addTickLHsExpr e2)
	       (return ty1)
	       (return arr_ty)
	       (return lr)
addTickHsCmd (HsArrForm e fix cmdtop) = 
        liftM3 HsArrForm
	       (addTickLHsExpr e)
	       (return fix)
	       (mapM (liftL (addTickHsCmdTop)) cmdtop)

-- Others should never happen in a command context.
addTickHsCmd e  = pprPanic "addTickHsCmd" (ppr e)

addTickCmdMatchGroup :: MatchGroup Id -> TM (MatchGroup Id)
addTickCmdMatchGroup (MatchGroup matches ty) = do
  matches' <- mapM (liftL addTickCmdMatch) matches
  return $ MatchGroup matches' ty

addTickCmdMatch :: Match Id -> TM (Match Id)
addTickCmdMatch (Match pats opSig gRHSs) =
  bindLocals (collectPatsBinders pats) $ do
    gRHSs' <- addTickCmdGRHSs gRHSs
    return $ Match pats opSig gRHSs'

addTickCmdGRHSs :: GRHSs Id -> TM (GRHSs Id)
addTickCmdGRHSs (GRHSs guarded local_binds) = do
  bindLocals binders $ do
    local_binds' <- addTickHsLocalBinds local_binds
    guarded' <- mapM (liftL addTickCmdGRHS) guarded
    return $ GRHSs guarded' local_binds'
  where
    binders = collectLocalBinders local_binds

addTickCmdGRHS :: GRHS Id -> TM (GRHS Id)
-- The *guards* are *not* Cmds, although the body is
-- C.f. addTickGRHS for the BinBox stuff
addTickCmdGRHS (GRHS stmts cmd)
  = do { (stmts',expr') <- addTickLStmts' (Just $ BinBox $ GuardBinBox) 
                                   stmts (addTickLHsCmd cmd)
       ; return $ GRHS stmts' expr' }

addTickLCmdStmts :: [LStmt Id] -> TM [LStmt Id]
addTickLCmdStmts stmts = do
  (stmts, _) <- addTickLCmdStmts' stmts (return ())
  return stmts

addTickLCmdStmts' :: [LStmt Id] -> TM a -> TM ([LStmt Id], a)
addTickLCmdStmts' lstmts res
  = bindLocals binders $ do
        lstmts' <- mapM (liftL addTickCmdStmt) lstmts
        a <- res
        return (lstmts', a)
  where
        binders = collectLStmtsBinders lstmts

addTickCmdStmt :: Stmt Id -> TM (Stmt Id)
addTickCmdStmt (BindStmt pat c bind fail) = do
	liftM4 BindStmt
		(addTickLPat pat)
		(addTickLHsCmd c)
		(return bind)
		(return fail)
addTickCmdStmt (LastStmt c ret) = do
	liftM2 LastStmt
		(addTickLHsCmd c)
		(addTickSyntaxExpr hpcSrcSpan ret)
addTickCmdStmt (ExprStmt c bind' guard' ty) = do
	liftM4 ExprStmt
		(addTickLHsCmd c)
		(addTickSyntaxExpr hpcSrcSpan bind')
                (addTickSyntaxExpr hpcSrcSpan guard')
		(return ty)
addTickCmdStmt (LetStmt binds) = do
	liftM LetStmt
		(addTickHsLocalBinds binds)
addTickCmdStmt stmt@(RecStmt {})
  = do { stmts' <- addTickLCmdStmts (recS_stmts stmt)
       ; ret'   <- addTickSyntaxExpr hpcSrcSpan (recS_ret_fn stmt)
       ; mfix'  <- addTickSyntaxExpr hpcSrcSpan (recS_mfix_fn stmt)
       ; bind'  <- addTickSyntaxExpr hpcSrcSpan (recS_bind_fn stmt)
       ; return (stmt { recS_stmts = stmts', recS_ret_fn = ret'
                      , recS_mfix_fn = mfix', recS_bind_fn = bind' }) }

-- Others should never happen in a command context.
addTickCmdStmt stmt  = pprPanic "addTickHsCmd" (ppr stmt)

addTickHsRecordBinds :: HsRecordBinds Id -> TM (HsRecordBinds Id)
addTickHsRecordBinds (HsRecFields fields dd) 
  = do	{ fields' <- mapM process fields
	; return (HsRecFields fields' dd) }
  where
    process (HsRecField ids expr doc)
	= do { expr' <- addTickLHsExpr expr
	     ; return (HsRecField ids expr' doc) }

addTickArithSeqInfo :: ArithSeqInfo Id -> TM (ArithSeqInfo Id)
addTickArithSeqInfo (From e1) =
	liftM From
		(addTickLHsExpr e1)
addTickArithSeqInfo (FromThen e1 e2) =
	liftM2 FromThen
		(addTickLHsExpr e1)
		(addTickLHsExpr e2)
addTickArithSeqInfo (FromTo e1 e2) =
	liftM2 FromTo
		(addTickLHsExpr e1)
		(addTickLHsExpr e2)
addTickArithSeqInfo (FromThenTo e1 e2 e3) =
	liftM3 FromThenTo
		(addTickLHsExpr e1)
		(addTickLHsExpr e2)
		(addTickLHsExpr e3)

liftL :: (Monad m) => (a -> m a) -> Located a -> m (Located a)
liftL f (L loc a) = do
  a' <- f a
  return $ L loc a'
\end{code}

\begin{code}
data TickTransState = TT { tickBoxCount:: Int
                         , mixEntries  :: [MixEntry_]
                         }                        

data TickTransEnv = TTE { fileName     :: FastString
                        , density      :: TickDensity
                        , dflags       :: DynFlags
                        , exports      :: NameSet
                        , declPath     :: [String]
                        , inScope      :: VarSet
                        , blackList    :: Map SrcSpan ()
                        , this_mod     :: Module
                        , tickishType  :: TickishType
                        }

--	deriving Show

data TickishType = ProfNotes | HpcTicks | Breakpoints | SourceNotes

type FreeVars = OccEnv Id
noFVs :: FreeVars
noFVs = emptyOccEnv

-- Note [freevars]
--   For breakpoints we want to collect the free variables of an
--   expression for pinning on the HsTick.  We don't want to collect
--   *all* free variables though: in particular there's no point pinning
--   on free variables that are will otherwise be in scope at the GHCi
--   prompt, which means all top-level bindings.  Unfortunately detecting
--   top-level bindings isn't easy (collectHsBindsBinders on the top-level
--   bindings doesn't do it), so we keep track of a set of "in-scope"
--   variables in addition to the free variables, and the former is used
--   to filter additions to the latter.  This gives us complete control
--   over what free variables we track.

data TM a = TM { unTM :: TickTransEnv -> TickTransState -> (a,FreeVars,TickTransState) }
        -- a combination of a state monad (TickTransState) and a writer
        -- monad (FreeVars).

instance Monad TM where
  return a = TM $ \ _env st -> (a,noFVs,st)
  (TM m) >>= k = TM $ \ env st -> 
		                case m env st of
				  (r1,fv1,st1) -> 
                                     case unTM (k r1) env st1 of
                                       (r2,fv2,st2) -> 
                                          (r2, fv1 `plusOccEnv` fv2, st2)

-- getState :: TM TickTransState
-- getState = TM $ \ env st -> (st, noFVs, st)

-- setState :: (TickTransState -> TickTransState) -> TM ()
-- setState f = TM $ \ env st -> ((), noFVs, f st)

getEnv :: TM TickTransEnv
getEnv = TM $ \ env st -> (env, noFVs, st)

withEnv :: (TickTransEnv -> TickTransEnv) -> TM a -> TM a
withEnv f (TM m) = TM $ \ env st -> 
		                 case m (f env) st of
                                   (a, fvs, st') -> (a, fvs, st')

getDensity :: TM TickDensity
getDensity = TM $ \env st -> (density env, noFVs, st)

ifDensity :: TickDensity -> TM a -> TM a -> TM a
ifDensity d th el = do d0 <- getDensity; if d == d0 then th else el

getFreeVars :: TM a -> TM (FreeVars, a)
getFreeVars (TM m) 
  = TM $ \ env st -> case m env st of (a, fv, st') -> ((fv,a), fv, st')

freeVar :: Id -> TM ()
freeVar id = TM $ \ env st -> 
                if id `elemVarSet` inScope env
                   then ((), unitOccEnv (nameOccName (idName id)) id, st)
                   else ((), noFVs, st)

addPathEntry :: String -> TM a -> TM a
addPathEntry nm = withEnv (\ env -> env { declPath = declPath env ++ [nm] })

getPathEntry :: TM [String]
getPathEntry = declPath `liftM` getEnv

getFileName :: TM FastString
getFileName = fileName `liftM` getEnv

sameFileName :: SrcSpan -> TM a -> TM a -> TM a
sameFileName pos out_of_scope in_scope = do
  file_name <- getFileName
  case srcSpanFileName_maybe pos of 
    Just file_name2 
      | file_name == file_name2 -> in_scope
    _ -> out_of_scope

bindLocals :: [Id] -> TM a -> TM a
bindLocals new_ids (TM m)
  = TM $ \ env st -> 
                 case m env{ inScope = inScope env `extendVarSetList` new_ids } st of
                   (r, fv, st') -> (r, fv `delListFromOccEnv` occs, st')
  where occs = [ nameOccName (idName id) | id <- new_ids ] 

isBlackListed :: SrcSpan -> TM Bool
isBlackListed pos = TM $ \ env st -> 
	      case Map.lookup pos (blackList env) of
	        Nothing -> (False,noFVs,st)
		Just () -> (True,noFVs,st)

-- the tick application inherits the source position of its
-- expression argument to support nested box allocations 
allocTickBox :: BoxLabel -> Bool -> Bool -> SrcSpan -> TM (HsExpr Id)
             -> TM (LHsExpr Id)
allocTickBox boxLabel countEntries topOnly pos m | isGoodSrcSpan' pos =
  sameFileName pos (do e <- m; return (L pos e)) $ do
    (fvs, e) <- getFreeVars m
    env <- getEnv
    tickish <- mkTickish boxLabel countEntries topOnly pos fvs (declPath env)
    return (L pos (HsTick tickish (L pos e)))
allocTickBox _boxLabel _countEntries _topOnly pos m = do
  e <- m
  return (L pos e)


-- the tick application inherits the source position of its
-- expression argument to support nested box allocations 
allocATickBox :: BoxLabel -> Bool -> Bool -> SrcSpan -> FreeVars
              -> TM (Maybe (Tickish Id))
allocATickBox boxLabel countEntries topOnly  pos fvs | isGoodSrcSpan' pos =
  sameFileName pos (return Nothing) $ do
    let
      mydecl_path = case boxLabel of
                      TopLevelBox x -> x
                      LocalBox xs  -> xs
                      _ -> panic "allocATickBox"
    tickish <- mkTickish boxLabel countEntries topOnly pos fvs mydecl_path
    return (Just tickish)
allocATickBox _boxLabel _countEntries _topOnly _pos _fvs =
  return Nothing


mkTickish :: BoxLabel -> Bool -> Bool -> SrcSpan -> OccEnv Id -> [String]
          -> TM (Tickish Id)
mkTickish boxLabel countEntries topOnly pos fvs decl_path =
  TM $ \ env st ->
    let c = tickBoxCount st
        ids = filter (not . isUnLiftedType . idType) $ occEnvElts fvs
            -- unlifted types cause two problems here:
            --   * we can't bind them  at the GHCi prompt
            --     (bindLocalsAtBreakpoint already fliters them out),
            --   * the simplifier might try to substitute a literal for
            --     the Id, and we can't handle that.

        mes = mixEntries st
        me = (pos, decl_path, map (nameOccName.idName) ids, boxLabel)

        cc_name | topOnly   = head decl_path
                | otherwise = concat (intersperse "." decl_path)

        cc = mkUserCC (mkFastString cc_name) (this_mod env) pos (mkCostCentreUnique c)

        count = countEntries && dopt Opt_ProfCountEntries (dflags env)

        tickish = case tickishType env of
          HpcTicks    -> HpcTick (this_mod env) c
          ProfNotes   -> ProfNote cc count True{-scopes-}
          Breakpoints -> Breakpoint c ids
          SourceNotes | RealSrcSpan pos' <- pos
                      -> SourceNote pos' cc_name
          _otherwise  -> panic "mkTickish: bad source span!"
    in
    ( tickish
    , fvs
    , st {tickBoxCount=c+1,mixEntries=me:mes}
    )


allocBinTickBox :: (Bool -> BoxLabel) -> SrcSpan -> TM (HsExpr Id)
                -> TM (LHsExpr Id)
allocBinTickBox boxLabel pos m = do {
 ; env <- getEnv
 ; case tickishType env of
   HpcTicks -> do {
 ; e <- m
 ; if not (isGoodSrcSpan' pos)
   then return (L pos e)
   else
 TM $ \ env st ->
  let meT = (pos,declPath env, [],boxLabel True)
      meF = (pos,declPath env, [],boxLabel False)
      meE = (pos,declPath env, [],ExpBox False)
      c = tickBoxCount st
      mes = mixEntries st
  in 
             ( L pos $ HsTick (HpcTick (this_mod env) c) $ L pos $ HsBinTick (c+1) (c+2) (L pos e)
           -- notice that F and T are reversed,
           -- because we are building the list in
           -- reverse...
             , noFVs
             , st {tickBoxCount=c+3 , mixEntries=meF:meT:meE:mes}
             )
  }
   _other -> allocTickBox (ExpBox False) False False pos m
  }

isGoodSrcSpan' :: SrcSpan -> Bool
isGoodSrcSpan' pos@(RealSrcSpan _) = srcSpanStart pos /= srcSpanEnd pos
isGoodSrcSpan' (UnhelpfulSpan _) = False

mkHpcPos :: SrcSpan -> HpcPos
mkHpcPos pos@(RealSrcSpan s)
   | isGoodSrcSpan' pos = toHpcPos (srcSpanStartLine s,
                                    srcSpanStartCol s,
                                    srcSpanEndLine s,
                                    srcSpanEndCol s - 1)
                              -- the end column of a SrcSpan is one
                              -- greater than the last column of the
                              -- span (see SrcLoc), whereas HPC
                              -- expects to the column range to be
                              -- inclusive, hence we subtract one above.
mkHpcPos _ = panic "bad source span; expected such spans to be filtered out"

hpcSrcSpan :: SrcSpan
hpcSrcSpan = mkGeneralSrcSpan (fsLit "Haskell Program Coverage internals")
\end{code}


\begin{code}
matchesOneOfMany :: [LMatch Id] -> Bool
matchesOneOfMany lmatches = sum (map matchCount lmatches) > 1
  where
	matchCount (L _ (Match _pats _ty (GRHSs grhss _binds))) = length grhss
\end{code}


\begin{code}
type MixEntry_ = (SrcSpan, [String], [OccName], BoxLabel)

-- For the hash value, we hash everything: the file name, 
--  the timestamp of the original source file, the tab stop,
--  and the mix entries. We cheat, and hash the show'd string.
-- This hash only has to be hashed at Mix creation time,
-- and is for sanity checking only.

mixHash :: FilePath -> Integer -> Int -> [MixEntry] -> Int
mixHash file tm tabstop entries = fromIntegral $ hashString
	(show $ Mix file tm 0 tabstop entries)
\end{code}

%************************************************************************
%*									*
%*              initialisation
%*									*
%************************************************************************

Each module compiled with -fhpc declares an initialisation function of
the form `hpc_init_<module>()`, which is emitted into the _stub.c file
and annotated with __attribute__((constructor)) so that it gets
executed at startup time.

The function's purpose is to call hs_hpc_module to register this
module with the RTS, and it looks something like this:

static void hpc_init_Main(void) __attribute__((constructor));
static void hpc_init_Main(void)
{extern StgWord64 _hpc_tickboxes_Main_hpc[];
 hs_hpc_module("Main",8,1150288664,_hpc_tickboxes_Main_hpc);}

\begin{code}
hpcInitCode :: DynFlags -> Module -> ModLocation -> HpcInfo -> SDoc
hpcInitCode dflags this_mod mod_loc hpc_info
 = vcat
    [ text "static void hpc_init_" <> ppr this_mod
         <> text "(void) __attribute__((constructor));"
    , text "static void hpc_init_" <> ppr this_mod <> text "(void)"
    , braces (vcat [
        tickboxes_decl,
        ptext (sLit "hs_hpc_module") <>
          parens (hcat (punctuate comma [
              doubleQuotes full_name_str,
              doubleQuotes mod_loc_str,
              int tickCount, -- really StgWord32
              int hashNo,    -- really StgWord32
              if opt_Hpc then tickboxes else int 0
            ])) <> semi
       ])
    ]
  where
    platform = targetPlatform dflags

    do_hpc | not opt_Hpc               = False
           | NoHpcInfo {} <- hpc_info  = False
           | otherwise                 = True
    (tickCount, hashNo)
      | do_hpc    = (hpcInfoTickCount hpc_info, hpcInfoHash hpc_info) 
      | otherwise = (0, 0)

    tickboxes = pprCLabel platform (mkHpcTicksLabel this_mod)
    tickboxes_decl
      | opt_Hpc   = ptext (sLit "extern StgWord64 ") <> tickboxes <> ptext (sLit "[]") <> semi
      | otherwise = empty

    module_name  = hcat (map (text.charToC) $
                         bytesFS (moduleNameFS (Module.moduleName this_mod)))
    package_name = hcat (map (text.charToC) $
                         bytesFS (packageIdFS  (modulePackageId this_mod)))
    full_name_str
       | modulePackageId this_mod == mainPackageId
       = module_name
       | otherwise
       = package_name <> char '/' <> module_name

    mod_loc_str = case ml_hs_file mod_loc of
                       Just path -> text path
                       Nothing   -> text "*** no source *** "
\end{code}
