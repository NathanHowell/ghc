%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1998
%

Type - public interface

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

-- | Main functions for manipulating types and type-related things
module Type (
	-- Note some of this is just re-exports from TyCon..

        -- * Main data types representing Types
	-- $type_classification
	
        -- $representation_types
        TyThing(..), Type, KindOrType, PredType, ThetaType,
        Var, TyVar, isTyVar, 

        -- ** Constructing and deconstructing types
        mkTyVarTy, mkTyVarTys, getTyVar, getTyVar_maybe,

	mkAppTy, mkAppTys, splitAppTy, splitAppTys, 
	splitAppTy_maybe, repSplitAppTy_maybe,

	mkFunTy, mkFunTys, splitFunTy, splitFunTy_maybe, 
	splitFunTys, splitFunTysN,
	funResultTy, funArgTy, zipFunTys, 

	mkTyConApp, mkTyConTy,
	tyConAppTyCon_maybe, tyConAppArgs_maybe, tyConAppTyCon, tyConAppArgs, 
	splitTyConApp_maybe, splitTyConApp, tyConAppArgN,

        mkForAllTy, mkForAllTys, splitForAllTy_maybe, splitForAllTys, 
        mkPiKinds, mkPiType, mkPiTypes,
	applyTy, applyTys, applyTysD, isForAllTy, dropForAlls,
	
	-- (Newtypes)
	newTyConInstRhs, carefullySplitNewType_maybe,
	
	-- Pred types
        mkFamilyTyConApp,
	isDictLikeTy,
        mkEqPred, mkClassPred,
	mkIPPred,
        noParenPred, isClassPred, isEqPred, isIPPred,
        mkPrimEqType,

        -- Deconstructing predicate types
        PredTree(..), predTreePredType, classifyPredType,
        getClassPredTys, getClassPredTys_maybe,
        getEqPredTys, getEqPredTys_maybe,
        getIPPredTy_maybe,

	-- ** Common type constructors
        funTyCon,

        -- ** Predicates on types
        isTyVarTy, isFunTy, isDictTy, isPredTy, isKindTy,

	-- (Lifting and boxity)
	isUnLiftedType, isUnboxedTupleType, isAlgType, isClosedAlgType,
	isPrimitiveType, isStrictType,

	-- * Main data types representing Kinds
	-- $kind_subtyping
        Kind, SimpleKind, MetaKindVar,

        -- ** Finding the kind of a type
        typeKind,
        
        -- ** Common Kinds and SuperKinds
        anyKind, liftedTypeKind, unliftedTypeKind, openTypeKind,
        argTypeKind, ubxTupleKind, constraintKind,
        tySuperKind, 

        -- ** Common Kind type constructors
        liftedTypeKindTyCon, openTypeKindTyCon, unliftedTypeKindTyCon,
        argTypeKindTyCon, ubxTupleKindTyCon, constraintKindTyCon,
        anyKindTyCon,

	-- * Type free variables
	tyVarsOfType, tyVarsOfTypes,
	expandTypeSynonyms, 
	typeSize, varSetElemsKvsFirst, sortQuantVars,

	-- * Type comparison
        eqType, eqTypeX, eqTypes, cmpType, cmpTypes, 
	eqPred, eqPredX, cmpPred, eqKind,

	-- * Forcing evaluation of types
        seqType, seqTypes,

        -- * Other views onto Types
        coreView, tcView, 

        repType, deepRepType,

	-- * Type representation for the code generator
	PrimRep(..),

	typePrimRep,

	-- * Main type substitution data types
	TvSubstEnv,	-- Representation widely visible
	TvSubst(..), 	-- Representation visible to a few friends
	
	-- ** Manipulating type substitutions
	emptyTvSubstEnv, emptyTvSubst,
	
	mkTvSubst, mkOpenTvSubst, zipOpenTvSubst, zipTopTvSubst, mkTopTvSubst, notElemTvSubst,
        getTvSubstEnv, setTvSubstEnv,
        zapTvSubstEnv, getTvInScope,
        extendTvInScope, extendTvInScopeList,
 	extendTvSubst, extendTvSubstList,
        isInScope, composeTvSubst, zipTyEnv,
        isEmptyTvSubst, unionTvSubst,

	-- ** Performing substitution on types and kinds
	substTy, substTys, substTyWith, substTysWith, substTheta, 
        substTyVar, substTyVars, substTyVarBndr,
        cloneTyVarBndr, deShadowTy, lookupTyVar,
        substKiWith, substKisWith,

	-- * Pretty-printing
	pprType, pprParendType, pprTypeApp, pprTyThingCategory, pprTyThing, pprForAll,
	pprEqPred, pprTheta, pprThetaArrowTy, pprClassPred, 
        pprKind, pprParendKind, pprSourceTyCon,
    ) where

#include "HsVersions.h"

-- We import the representation and primitive functions from TypeRep.
-- Many things are reexported, but not the representation!

import Kind
import TypeRep

-- friends:
import Var
import VarEnv
import VarSet

import Class
import TyCon
import TysPrim
import {-# SOURCE #-} TysWiredIn ( eqTyCon, mkBoxedTupleTy )
import PrelNames	         ( eqTyConKey )

-- others
import {-# SOURCE #-} IParam ( ipTyCon )
import Unique		( Unique, hasKey )
import BasicTypes	( IPName(..) )
import Name		( Name )
import NameSet
import StaticFlags
import Util
import Outputable
import FastString

import Maybes		( orElse )
import Data.Maybe	( isJust )

infixr 3 `mkFunTy`	-- Associates to the right
\end{code}

\begin{code}
-- $type_classification
-- #type_classification#
-- 
-- Types are one of:
-- 
-- [Unboxed]            Iff its representation is other than a pointer
-- 			Unboxed types are also unlifted.
-- 
-- [Lifted]             Iff it has bottom as an element.
-- 			Closures always have lifted types: i.e. any
-- 			let-bound identifier in Core must have a lifted
-- 			type. Operationally, a lifted object is one that
-- 			can be entered.
-- 			Only lifted types may be unified with a type variable.
-- 
-- [Algebraic]          Iff it is a type with one or more constructors, whether
-- 			declared with @data@ or @newtype@.
-- 			An algebraic type is one that can be deconstructed
-- 			with a case expression. This is /not/ the same as 
--			lifted types, because we also include unboxed
-- 			tuples in this classification.
-- 
-- [Data]               Iff it is a type declared with @data@, or a boxed tuple.
-- 
-- [Primitive]          Iff it is a built-in type that can't be expressed in Haskell.
-- 
-- Currently, all primitive types are unlifted, but that's not necessarily
-- the case: for example, @Int@ could be primitive.
-- 
-- Some primitive types are unboxed, such as @Int#@, whereas some are boxed
-- but unlifted (such as @ByteArray#@).  The only primitive types that we
-- classify as algebraic are the unboxed tuples.
-- 
-- Some examples of type classifications that may make this a bit clearer are:
-- 
-- @
-- Type         primitive       boxed           lifted          algebraic
-- -----------------------------------------------------------------------------
-- Int#         Yes             No              No              No
-- ByteArray#   Yes             Yes             No              No
-- (\# a, b \#)   Yes             No              No              Yes
-- (  a, b  )   No              Yes             Yes             Yes
-- [a]          No              Yes             Yes             Yes
-- @

-- $representation_types
-- A /source type/ is a type that is a separate type as far as the type checker is
-- concerned, but which has a more low-level representation as far as Core-to-Core
-- passes and the rest of the back end is concerned.
--
-- You don't normally have to worry about this, as the utility functions in
-- this module will automatically convert a source into a representation type
-- if they are spotted, to the best of it's abilities. If you don't want this
-- to happen, use the equivalent functions from the "TcType" module.
\end{code}

%************************************************************************
%*									*
		Type representation
%*									*
%************************************************************************

\begin{code}
{-# INLINE coreView #-}
coreView :: Type -> Maybe Type
-- ^ In Core, we \"look through\" non-recursive newtypes and 'PredTypes': this
-- function tries to obtain a different view of the supplied type given this
--
-- Strips off the /top layer only/ of a type to give 
-- its underlying representation type. 
-- Returns Nothing if there is nothing to look through.
--
-- By being non-recursive and inlined, this case analysis gets efficiently
-- joined onto the case analysis that the caller is already doing
coreView (TyConApp tc tys) | Just (tenv, rhs, tys') <- coreExpandTyCon_maybe tc tys 
              = Just (mkAppTys (substTy (mkTopTvSubst tenv) rhs) tys')
               -- Its important to use mkAppTys, rather than (foldl AppTy),
               -- because the function part might well return a 
               -- partially-applied type constructor; indeed, usually will!
coreView _                 = Nothing

-----------------------------------------------
{-# INLINE tcView #-}
tcView :: Type -> Maybe Type
-- ^ Similar to 'coreView', but for the type checker, which just looks through synonyms
tcView (TyConApp tc tys) | Just (tenv, rhs, tys') <- tcExpandTyCon_maybe tc tys 
			 = Just (mkAppTys (substTy (mkTopTvSubst tenv) rhs) tys')
tcView _                 = Nothing
  -- You might think that tcView belows in TcType rather than Type, but unfortunately
  -- it is needed by Unify, which is turn imported by Coercion (for MatchEnv and matchList).
  -- So we will leave it here to avoid module loops.

-----------------------------------------------
expandTypeSynonyms :: Type -> Type
-- ^ Expand out all type synonyms.  Actually, it'd suffice to expand out
-- just the ones that discard type variables (e.g.  type Funny a = Int)
-- But we don't know which those are currently, so we just expand all.
expandTypeSynonyms ty 
  = go ty
  where
    go (TyConApp tc tys)
      | Just (tenv, rhs, tys') <- tcExpandTyCon_maybe tc tys 
      = go (mkAppTys (substTy (mkTopTvSubst tenv) rhs) tys')
      | otherwise
      = TyConApp tc (map go tys)
    go (TyVarTy tv)    = TyVarTy tv
    go (AppTy t1 t2)   = AppTy (go t1) (go t2)
    go (FunTy t1 t2)   = FunTy (go t1) (go t2)
    go (ForAllTy tv t) = ForAllTy tv (go t)
\end{code}


%************************************************************************
%*									*
\subsection{Constructor-specific functions}
%*									*
%************************************************************************


---------------------------------------------------------------------
				TyVarTy
				~~~~~~~
\begin{code}
-- | Attempts to obtain the type variable underlying a 'Type', and panics with the
-- given message if this is not a type variable type. See also 'getTyVar_maybe'
getTyVar :: String -> Type -> TyVar
getTyVar msg ty = case getTyVar_maybe ty of
		    Just tv -> tv
		    Nothing -> panic ("getTyVar: " ++ msg)

isTyVarTy :: Type -> Bool
isTyVarTy ty = isJust (getTyVar_maybe ty)

-- | Attempts to obtain the type variable underlying a 'Type'
getTyVar_maybe :: Type -> Maybe TyVar
getTyVar_maybe ty | Just ty' <- coreView ty = getTyVar_maybe ty'
getTyVar_maybe (TyVarTy tv) 	 	    = Just tv  
getTyVar_maybe _                            = Nothing

\end{code}


---------------------------------------------------------------------
				AppTy
				~~~~~
We need to be pretty careful with AppTy to make sure we obey the 
invariant that a TyConApp is always visibly so.  mkAppTy maintains the
invariant: use it.

\begin{code}
-- | Applies a type to another, as in e.g. @k a@
mkAppTy :: Type -> Type -> Type
mkAppTy orig_ty1 orig_ty2
  = mk_app orig_ty1
  where
    mk_app (TyConApp tc tys) = mkTyConApp tc (tys ++ [orig_ty2])
    mk_app _                 = AppTy orig_ty1 orig_ty2
	-- Note that the TyConApp could be an 
	-- under-saturated type synonym.  GHC allows that; e.g.
	--	type Foo k = k a -> k a
	--	type Id x = x
	--	foo :: Foo Id -> Foo Id
	--
	-- Here Id is partially applied in the type sig for Foo,
	-- but once the type synonyms are expanded all is well

mkAppTys :: Type -> [Type] -> Type
mkAppTys orig_ty1 []	    = orig_ty1
	-- This check for an empty list of type arguments
	-- avoids the needless loss of a type synonym constructor.
	-- For example: mkAppTys Rational []
	--   returns to (Ratio Integer), which has needlessly lost
	--   the Rational part.
mkAppTys orig_ty1 orig_tys2
  = mk_app orig_ty1
  where
    mk_app (TyConApp tc tys) = mkTyConApp tc (tys ++ orig_tys2)
				-- mkTyConApp: see notes with mkAppTy
    mk_app _                 = foldl AppTy orig_ty1 orig_tys2

-------------
splitAppTy_maybe :: Type -> Maybe (Type, Type)
-- ^ Attempt to take a type application apart, whether it is a
-- function, type constructor, or plain type application. Note
-- that type family applications are NEVER unsaturated by this!
splitAppTy_maybe ty | Just ty' <- coreView ty
		    = splitAppTy_maybe ty'
splitAppTy_maybe ty = repSplitAppTy_maybe ty

-------------
repSplitAppTy_maybe :: Type -> Maybe (Type,Type)
-- ^ Does the AppTy split as in 'splitAppTy_maybe', but assumes that 
-- any Core view stuff is already done
repSplitAppTy_maybe (FunTy ty1 ty2)   = Just (TyConApp funTyCon [ty1], ty2)
repSplitAppTy_maybe (AppTy ty1 ty2)   = Just (ty1, ty2)
repSplitAppTy_maybe (TyConApp tc tys) 
  | isDecomposableTyCon tc || tys `lengthExceeds` tyConArity tc 
  , Just (tys', ty') <- snocView tys
  = Just (TyConApp tc tys', ty')    -- Never create unsaturated type family apps!
repSplitAppTy_maybe _other = Nothing
-------------
splitAppTy :: Type -> (Type, Type)
-- ^ Attempts to take a type application apart, as in 'splitAppTy_maybe',
-- and panics if this is not possible
splitAppTy ty = case splitAppTy_maybe ty of
			Just pr -> pr
			Nothing -> panic "splitAppTy"

-------------
splitAppTys :: Type -> (Type, [Type])
-- ^ Recursively splits a type as far as is possible, leaving a residual
-- type being applied to and the type arguments applied to it. Never fails,
-- even if that means returning an empty list of type applications.
splitAppTys ty = split ty ty []
  where
    split orig_ty ty args | Just ty' <- coreView ty = split orig_ty ty' args
    split _       (AppTy ty arg)        args = split ty ty (arg:args)
    split _       (TyConApp tc tc_args) args
      = let -- keep type families saturated
            n | isDecomposableTyCon tc = 0
              | otherwise              = tyConArity tc
            (tc_args1, tc_args2) = splitAt n tc_args
        in
        (TyConApp tc tc_args1, tc_args2 ++ args)
    split _       (FunTy ty1 ty2)       args = ASSERT( null args )
					       (TyConApp funTyCon [], [ty1,ty2])
    split orig_ty _                     args = (orig_ty, args)

\end{code}


---------------------------------------------------------------------
				FunTy
				~~~~~

\begin{code}
mkFunTy :: Type -> Type -> Type
-- ^ Creates a function type from the given argument and result type
mkFunTy arg res = FunTy arg res

mkFunTys :: [Type] -> Type -> Type
mkFunTys tys ty = foldr mkFunTy ty tys

isFunTy :: Type -> Bool 
isFunTy ty = isJust (splitFunTy_maybe ty)

splitFunTy :: Type -> (Type, Type)
-- ^ Attempts to extract the argument and result types from a type, and
-- panics if that is not possible. See also 'splitFunTy_maybe'
splitFunTy ty | Just ty' <- coreView ty = splitFunTy ty'
splitFunTy (FunTy arg res)   = (arg, res)
splitFunTy other	     = pprPanic "splitFunTy" (ppr other)

splitFunTy_maybe :: Type -> Maybe (Type, Type)
-- ^ Attempts to extract the argument and result types from a type
splitFunTy_maybe ty | Just ty' <- coreView ty = splitFunTy_maybe ty'
splitFunTy_maybe (FunTy arg res)   = Just (arg, res)
splitFunTy_maybe _                 = Nothing

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = split [] ty ty
  where
    split args orig_ty ty | Just ty' <- coreView ty = split args orig_ty ty'
    split args _       (FunTy arg res)   = split (arg:args) res res
    split args orig_ty _                 = (reverse args, orig_ty)

splitFunTysN :: Int -> Type -> ([Type], Type)
-- ^ Split off exactly the given number argument types, and panics if that is not possible
splitFunTysN 0 ty = ([], ty)
splitFunTysN n ty = ASSERT2( isFunTy ty, int n <+> ppr ty )
                    case splitFunTy ty of { (arg, res) ->
		    case splitFunTysN (n-1) res of { (args, res) ->
		    (arg:args, res) }}

-- | Splits off argument types from the given type and associating
-- them with the things in the input list from left to right. The
-- final result type is returned, along with the resulting pairs of
-- objects and types, albeit with the list of pairs in reverse order.
-- Panics if there are not enough argument types for the input list.
zipFunTys :: Outputable a => [a] -> Type -> ([(a, Type)], Type)
zipFunTys orig_xs orig_ty = split [] orig_xs orig_ty orig_ty
  where
    split acc []     nty _                 = (reverse acc, nty)
    split acc xs     nty ty 
	  | Just ty' <- coreView ty 	   = split acc xs nty ty'
    split acc (x:xs) _   (FunTy arg res)   = split ((x,arg):acc) xs res res
    split _   _      _   _                 = pprPanic "zipFunTys" (ppr orig_xs <+> ppr orig_ty)
    
funResultTy :: Type -> Type
-- ^ Extract the function result type and panic if that is not possible
funResultTy ty | Just ty' <- coreView ty = funResultTy ty'
funResultTy (FunTy _arg res)  = res
funResultTy ty                = pprPanic "funResultTy" (ppr ty)

funArgTy :: Type -> Type
-- ^ Extract the function argument type and panic if that is not possible
funArgTy ty | Just ty' <- coreView ty = funArgTy ty'
funArgTy (FunTy arg _res)  = arg
funArgTy ty                = pprPanic "funArgTy" (ppr ty)
\end{code}

---------------------------------------------------------------------
				TyConApp
				~~~~~~~~

\begin{code}
-- splitTyConApp "looks through" synonyms, because they don't
-- mean a distinct type, but all other type-constructor applications
-- including functions are returned as Just ..

-- | The same as @fst . splitTyConApp@
tyConAppTyCon_maybe :: Type -> Maybe TyCon
tyConAppTyCon_maybe ty | Just ty' <- coreView ty = tyConAppTyCon_maybe ty'
tyConAppTyCon_maybe (TyConApp tc _) = Just tc
tyConAppTyCon_maybe (FunTy {})      = Just funTyCon
tyConAppTyCon_maybe _               = Nothing

tyConAppTyCon :: Type -> TyCon
tyConAppTyCon ty = tyConAppTyCon_maybe ty `orElse` pprPanic "tyConAppTyCon" (ppr ty)

-- | The same as @snd . splitTyConApp@
tyConAppArgs_maybe :: Type -> Maybe [Type]
tyConAppArgs_maybe ty | Just ty' <- coreView ty = tyConAppArgs_maybe ty'
tyConAppArgs_maybe (TyConApp _ tys) = Just tys
tyConAppArgs_maybe (FunTy arg res)  = Just [arg,res]
tyConAppArgs_maybe _                = Nothing


tyConAppArgs :: Type -> [Type]
tyConAppArgs ty = tyConAppArgs_maybe ty `orElse` pprPanic "tyConAppArgs" (ppr ty)

tyConAppArgN :: Int -> Type -> Type
-- Executing Nth
tyConAppArgN n ty 
  = case tyConAppArgs_maybe ty of
      Just tys -> ASSERT2( n < length tys, ppr n <+> ppr tys ) tys !! n
      Nothing  -> pprPanic "tyConAppArgN" (ppr n <+> ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor. Panics if that is not possible.
-- See also 'splitTyConApp_maybe'
splitTyConApp :: Type -> (TyCon, [Type])
splitTyConApp ty = case splitTyConApp_maybe ty of
			Just stuff -> stuff
			Nothing	   -> pprPanic "splitTyConApp" (ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor
splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
splitTyConApp_maybe ty | Just ty' <- coreView ty = splitTyConApp_maybe ty'
splitTyConApp_maybe (TyConApp tc tys) = Just (tc, tys)
splitTyConApp_maybe (FunTy arg res)   = Just (funTyCon, [arg,res])
splitTyConApp_maybe _                 = Nothing

newTyConInstRhs :: TyCon -> [Type] -> Type
-- ^ Unwrap one 'layer' of newtype on a type constructor and its arguments, using an 
-- eta-reduced version of the @newtype@ if possible
newTyConInstRhs tycon tys 
    = ASSERT2( equalLength tvs tys1, ppr tycon $$ ppr tys $$ ppr tvs )
      mkAppTys (substTyWith tvs tys1 ty) tys2
  where
    (tvs, ty)    = newTyConEtadRhs tycon
    (tys1, tys2) = splitAtList tvs tys
\end{code}


---------------------------------------------------------------------
				SynTy
				~~~~~

Notes on type synonyms
~~~~~~~~~~~~~~~~~~~~~~
The various "split" functions (splitFunTy, splitRhoTy, splitForAllTy) try
to return type synonyms whereever possible. Thus

	type Foo a = a -> a

we want 
	splitFunTys (a -> Foo a) = ([a], Foo a)
not			           ([a], a -> a)

The reason is that we then get better (shorter) type signatures in 
interfaces.  Notably this plays a role in tcTySigs in TcBinds.lhs.


Note [Expanding newtypes]
~~~~~~~~~~~~~~~~~~~~~~~~~
When expanding a type to expose a data-type constructor, we need to be
careful about newtypes, lest we fall into an infinite loop. Here are
the key examples:

  newtype Id  x = MkId x
  newtype Fix f = MkFix (f (Fix f))
  newtype T     = MkT (T -> T) 
  
  Type	         Expansion
 --------------------------
  T		 T -> T
  Fix Maybe      Maybe (Fix Maybe)
  Id (Id Int)    Int
  Fix Id         NO NO NO

Notice that we can expand T, even though it's recursive.
And we can expand Id (Id Int), even though the Id shows up
twice at the outer level.  

So, when expanding, we keep track of when we've seen a recursive
newtype at outermost level; and bale out if we see it again.


		Representation types
		~~~~~~~~~~~~~~~~~~~~

\begin{code}
-- | Looks through:
--
--	1. For-alls
--	2. Synonyms
--	3. Predicates
--	4. All newtypes, including recursive ones, but not newtype families
--
-- It's useful in the back end of the compiler.
repType :: Type -> Type
repType ty
  = go emptyNameSet ty
  where
    go :: NameSet -> Type -> Type
    go rec_nts ty    	  		-- Expand predicates and synonyms
      | Just ty' <- coreView ty
      = go rec_nts ty'

    go rec_nts (ForAllTy _ ty)		-- Drop foralls
	= go rec_nts ty

    go rec_nts (TyConApp tc tys)	-- Expand newtypes
      | Just (rec_nts', ty') <- carefullySplitNewType_maybe rec_nts tc tys
      = go rec_nts' ty'

    go _ ty = ty

deepRepType :: Type -> Type
-- Same as repType, but looks recursively
deepRepType ty
  = go emptyNameSet ty
  where
    go rec_nts ty    	  		-- Expand predicates and synonyms
      | Just ty' <- coreView ty
      = go rec_nts ty'

    go rec_nts (ForAllTy _ ty)		-- Drop foralls
	= go rec_nts ty

    go rec_nts (TyConApp tc tys)	-- Expand newtypes
      | Just (rec_nts', ty') <- carefullySplitNewType_maybe rec_nts tc tys
      = go rec_nts' ty'

      -- Apply recursively; this is the "deep" bit
    go rec_nts (TyConApp tc tys) = TyConApp tc (map (go rec_nts) tys)
    go rec_nts (AppTy ty1 ty2)   = mkAppTy (go rec_nts ty1) (go rec_nts ty2)
    go rec_nts (FunTy ty1 ty2)   = FunTy   (go rec_nts ty1) (go rec_nts ty2)

    go _ ty = ty

carefullySplitNewType_maybe :: NameSet -> TyCon -> [Type] -> Maybe (NameSet,Type)
-- Return the representation of a newtype, unless 
-- we've seen it already: see Note [Expanding newtypes]
-- Assumes the newtype is saturated
carefullySplitNewType_maybe rec_nts tc tys
  | isNewTyCon tc
  , tys `lengthAtLeast` tyConArity tc
  , not (tc_name `elemNameSet` rec_nts) = Just (rec_nts', newTyConInstRhs tc tys)
  | otherwise	   	                = Nothing
  where
    tc_name = tyConName tc
    rec_nts' | isRecursiveTyCon tc = addOneToNameSet rec_nts tc_name
	     | otherwise	   = rec_nts


-- ToDo: this could be moved to the code generator, using splitTyConApp instead
-- of inspecting the type directly.

-- | Discovers the primitive representation of a more abstract 'Type'
typePrimRep :: Type -> PrimRep
typePrimRep ty = case repType ty of
		   TyConApp tc _ -> tyConPrimRep tc
		   FunTy _ _	 -> PtrRep
		   AppTy _ _	 -> PtrRep	-- See note below
		   TyVarTy _	 -> PtrRep
		   _             -> pprPanic "typePrimRep" (ppr ty)
	-- Types of the form 'f a' must be of kind *, not *#, so
	-- we are guaranteed that they are represented by pointers.
	-- The reason is that f must have kind *->*, not *->*#, because
	-- (we claim) there is no way to constrain f's kind any other
	-- way.
\end{code}


---------------------------------------------------------------------
				ForAllTy
				~~~~~~~~

\begin{code}
mkForAllTy :: TyVar -> Type -> Type
mkForAllTy tyvar ty
  = ForAllTy tyvar ty

-- | Wraps foralls over the type using the provided 'TyVar's from left to right
mkForAllTys :: [TyVar] -> Type -> Type
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

mkPiKinds :: [TyVar] -> Kind -> Kind
-- mkPiKinds [k1, k2, (a:k1 -> *)] k2
-- returns forall k1 k2. (k1 -> *) -> k2
mkPiKinds [] res = res
mkPiKinds (tv:tvs) res 
  | isKiVar tv = ForAllTy tv          (mkPiKinds tvs res)
  | otherwise  = FunTy (tyVarKind tv) (mkPiKinds tvs res)

mkPiType  :: Var -> Type -> Type
-- ^ Makes a @(->)@ type or a forall type, depending
-- on whether it is given a type variable or a term variable.
mkPiTypes :: [Var] -> Type -> Type
-- ^ 'mkPiType' for multiple type or value arguments

mkPiType v ty
   | isId v    = mkFunTy (varType v) ty
   | otherwise = mkForAllTy v ty

mkPiTypes vs ty = foldr mkPiType ty vs

isForAllTy :: Type -> Bool
isForAllTy (ForAllTy _ _) = True
isForAllTy _              = False

-- | Attempts to take a forall type apart, returning the bound type variable
-- and the remainder of the type
splitForAllTy_maybe :: Type -> Maybe (TyVar, Type)
splitForAllTy_maybe ty = splitFAT_m ty
  where
    splitFAT_m ty | Just ty' <- coreView ty = splitFAT_m ty'
    splitFAT_m (ForAllTy tyvar ty)	    = Just(tyvar, ty)
    splitFAT_m _			    = Nothing

-- | Attempts to take a forall type apart, returning all the immediate such bound
-- type variables and the remainder of the type. Always suceeds, even if that means
-- returning an empty list of 'TyVar's
splitForAllTys :: Type -> ([TyVar], Type)
splitForAllTys ty = split ty ty []
   where
     split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
     split _       (ForAllTy tv ty)  tvs = split ty ty (tv:tvs)
     split orig_ty _                 tvs = (reverse tvs, orig_ty)

-- | Equivalent to @snd . splitForAllTys@
dropForAlls :: Type -> Type
dropForAlls ty = snd (splitForAllTys ty)
\end{code}

-- (mkPiType now in CoreUtils)

applyTy, applyTys
~~~~~~~~~~~~~~~~~

\begin{code}
-- | Instantiate a forall type with one or more type arguments.
-- Used when we have a polymorphic function applied to type args:
--
-- > f t1 t2
--
-- We use @applyTys type-of-f [t1,t2]@ to compute the type of the expression.
-- Panics if no application is possible.
applyTy :: Type -> KindOrType -> Type
applyTy ty arg | Just ty' <- coreView ty = applyTy ty' arg
applyTy (ForAllTy tv ty) arg = substTyWith [tv] [arg] ty
applyTy _                _   = panic "applyTy"

applyTys :: Type -> [KindOrType] -> Type
-- ^ This function is interesting because:
--
--	1. The function may have more for-alls than there are args
--
--	2. Less obviously, it may have fewer for-alls
--
-- For case 2. think of:
--
-- > applyTys (forall a.a) [forall b.b, Int]
--
-- This really can happen, but only (I think) in situations involving
-- undefined.  For example:
--       undefined :: forall a. a
-- Term: undefined @(forall b. b->b) @Int 
-- This term should have type (Int -> Int), but notice that
-- there are more type args than foralls in 'undefined's type.

applyTys ty args = applyTysD empty ty args

applyTysD :: SDoc -> Type -> [Type] -> Type	-- Debug version
applyTysD _   orig_fun_ty []      = orig_fun_ty
applyTysD doc orig_fun_ty arg_tys 
  | n_tvs == n_args 	-- The vastly common case
  = substTyWith tvs arg_tys rho_ty
  | n_tvs > n_args 	-- Too many for-alls
  = substTyWith (take n_args tvs) arg_tys 
		(mkForAllTys (drop n_args tvs) rho_ty)
  | otherwise		-- Too many type args
  = ASSERT2( n_tvs > 0, doc $$ ppr orig_fun_ty )	-- Zero case gives infnite loop!
    applyTysD doc (substTyWith tvs (take n_tvs arg_tys) rho_ty)
	          (drop n_tvs arg_tys)
  where
    (tvs, rho_ty) = splitForAllTys orig_fun_ty 
    n_tvs = length tvs
    n_args = length arg_tys     
\end{code}


%************************************************************************
%*									*
                         Pred
%*									*
%************************************************************************

Predicates on PredType

\begin{code}
noParenPred :: PredType -> Bool
-- A predicate that can appear without parens before a "=>"
--       C a => a -> a
--       a~b => a -> b
-- But   (?x::Int) => Int -> Int
noParenPred p = isClassPred p || isEqPred p

isPredTy :: Type -> Bool
isPredTy ty
  | isSuperKind ty = False
  | otherwise = typeKind ty `eqKind` constraintKind

isKindTy :: Type -> Bool
isKindTy = isSuperKind . typeKind

isClassPred, isEqPred, isIPPred :: PredType -> Bool
isClassPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon | isClassTyCon tyCon -> True
    _                               -> False
isEqPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon -> tyCon `hasKey` eqTyConKey
    _          -> False
isIPPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon | Just _ <- tyConIP_maybe tyCon -> True
    _                                          -> False
\end{code}

Make PredTypes

--------------------- Equality types ---------------------------------
\begin{code}
-- | Creates a type equality predicate
mkEqPred :: (Type, Type) -> PredType
mkEqPred (ty1, ty2)
  -- IA0_TODO: The caller should give the kind.
  = WARN ( not (k `eqKind` defaultKind k), ppr (k, ty1, ty2) )
    TyConApp eqTyCon [k, ty1, ty2]
  where k = defaultKind (typeKind ty1)
--  where k = typeKind ty1

mkPrimEqType :: (Type, Type) -> Type
mkPrimEqType (ty1, ty2)
  -- IA0_TODO: The caller should give the kind.
  = WARN ( not (k `eqKind` defaultKind k), ppr (k, ty1, ty2) )
    TyConApp eqPrimTyCon [k, ty1, ty2]
  where k = defaultKind (typeKind ty1)
--  where k = typeKind ty1
\end{code}

--------------------- Implicit parameters ---------------------------------

\begin{code}
mkIPPred :: IPName Name -> Type -> PredType
mkIPPred ip ty = TyConApp (ipTyCon ip) [ty]
\end{code}

--------------------- Dictionary types ---------------------------------
\begin{code}
mkClassPred :: Class -> [Type] -> PredType
mkClassPred clas tys = TyConApp (classTyCon clas) tys

isDictTy :: Type -> Bool
isDictTy = isClassPred

isDictLikeTy :: Type -> Bool
-- Note [Dictionary-like types]
isDictLikeTy ty | Just ty' <- coreView ty = isDictLikeTy ty'
isDictLikeTy ty = case splitTyConApp_maybe ty of
	Just (tc, tys) | isClassTyCon tc -> True
	 			   | isTupleTyCon tc -> all isDictLikeTy tys
	_other                           -> False
\end{code}

Note [Dictionary-like types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Being "dictionary-like" means either a dictionary type or a tuple thereof.
In GHC 6.10 we build implication constraints which construct such tuples,
and if we land up with a binding
    t :: (C [a], Eq [a])
    t = blah
then we want to treat t as cheap under "-fdicts-cheap" for example.
(Implication constraints are normally inlined, but sadly not if the
occurrence is itself inside an INLINE function!  Until we revise the 
handling of implication constraints, that is.)  This turned out to
be important in getting good arities in DPH code.  Example:

    class C a
    class D a where { foo :: a -> a }
    instance C a => D (Maybe a) where { foo x = x }

    bar :: (C a, C b) => a -> b -> (Maybe a, Maybe b)
    {-# INLINE bar #-}
    bar x y = (foo (Just x), foo (Just y))

Then 'bar' should jolly well have arity 4 (two dicts, two args), but
we ended up with something like
   bar = __inline_me__ (\d1,d2. let t :: (D (Maybe a), D (Maybe b)) = ...
                                in \x,y. <blah>)

This is all a bit ad-hoc; eg it relies on knowing that implication
constraints build tuples.


Decomposing PredType

\begin{code}
data PredTree = ClassPred Class [Type]
              | EqPred Type Type
              | IPPred (IPName Name) Type
              | TuplePred [PredType]
              | IrredPred PredType

predTreePredType :: PredTree -> PredType
predTreePredType (ClassPred clas tys) = mkClassPred clas tys
predTreePredType (EqPred ty1 ty2)     = mkEqPred (ty1, ty2)
predTreePredType (IPPred ip ty)       = mkIPPred ip ty
predTreePredType (TuplePred tys)      = mkBoxedTupleTy tys
predTreePredType (IrredPred ty)       = ty

classifyPredType :: PredType -> PredTree
classifyPredType ev_ty = case splitTyConApp_maybe ev_ty of
    Just (tc, tys) | Just clas <- tyConClass_maybe tc
                   -> ClassPred clas tys
    Just (tc, tys) | tc `hasKey` eqTyConKey
                   , let [_, ty1, ty2] = tys
                   -> EqPred ty1 ty2
    Just (tc, tys) | Just ip <- tyConIP_maybe tc
                   , let [ty] = tys
                   -> IPPred ip ty
    Just (tc, tys) | isTupleTyCon tc
                   -> TuplePred tys
    _ -> IrredPred ev_ty
\end{code}

\begin{code}
getClassPredTys :: PredType -> (Class, [Type])
getClassPredTys ty = case getClassPredTys_maybe ty of
        Just (clas, tys) -> (clas, tys)
        Nothing          -> pprPanic "getClassPredTys" (ppr ty)

getClassPredTys_maybe :: PredType -> Maybe (Class, [Type])
getClassPredTys_maybe ty = case splitTyConApp_maybe ty of 
        Just (tc, tys) | Just clas <- tyConClass_maybe tc -> Just (clas, tys)
        _ -> Nothing

getEqPredTys :: PredType -> (Type, Type)
getEqPredTys ty = case getEqPredTys_maybe ty of
        Just (ty1, ty2) -> (ty1, ty2)
        Nothing         -> pprPanic "getEqPredTys" (ppr ty)

getEqPredTys_maybe :: PredType -> Maybe (Type, Type)
getEqPredTys_maybe ty = case splitTyConApp_maybe ty of 
        Just (tc, [_, ty1, ty2]) | tc `hasKey` eqTyConKey -> Just (ty1, ty2)
        _ -> Nothing

getIPPredTy_maybe :: PredType -> Maybe (IPName Name, Type)
getIPPredTy_maybe ty = case splitTyConApp_maybe ty of 
        Just (tc, [ty1]) | Just ip <- tyConIP_maybe tc -> Just (ip, ty1)
        _ -> Nothing
\end{code}

%************************************************************************
%*									*
                   Size									
%*									*
%************************************************************************

\begin{code}
typeSize :: Type -> Int
typeSize (TyVarTy _)     = 1
typeSize (AppTy t1 t2)   = typeSize t1 + typeSize t2
typeSize (FunTy t1 t2)   = typeSize t1 + typeSize t2
typeSize (ForAllTy _ t)  = 1 + typeSize t
typeSize (TyConApp _ ts) = 1 + sum (map typeSize ts)

varSetElemsKvsFirst :: VarSet -> [TyVar]
-- {k1,a,k2,b} --> [k1,k2,a,b]
varSetElemsKvsFirst set = uncurry (++) $ partitionKiTyVars (varSetElems set)

sortQuantVars :: [Var] -> [Var]
-- Sort the variables so the true kind then type variables come first
sortQuantVars = sortLe le
  where
    v1 `le` v2 = case (is_tv v1, is_tv v2) of
                   (True, False)  -> True
                   (False, True)  -> False
                   (True, True)   ->
                     case (is_kv v1, is_kv v2) of
                       (True, False) -> True
                       (False, True) -> False
                       _             -> v1 <= v2  -- Same family
                   (False, False) -> v1 <= v2
    is_tv v = isTyVar v
    is_kv v = isSuperKind (tyVarKind v)
\end{code}


%************************************************************************
%*									*
\subsection{Type families}
%*									*
%************************************************************************

\begin{code}
mkFamilyTyConApp :: TyCon -> [Type] -> Type
-- ^ Given a family instance TyCon and its arg types, return the
-- corresponding family type.  E.g:
--
-- > data family T a
-- > data instance T (Maybe b) = MkT b
--
-- Where the instance tycon is :RTL, so:
--
-- > mkFamilyTyConApp :RTL Int  =  T (Maybe Int)
mkFamilyTyConApp tc tys
  | Just (fam_tc, fam_tys) <- tyConFamInst_maybe tc
  , let fam_subst = zipTopTvSubst (tyConTyVars tc) tys
  = mkTyConApp fam_tc (substTys fam_subst fam_tys)
  | otherwise
  = mkTyConApp tc tys

-- | Pretty prints a 'TyCon', using the family instance in case of a
-- representation tycon.  For example:
--
-- > data T [a] = ...
--
-- In that case we want to print @T [a]@, where @T@ is the family 'TyCon'
pprSourceTyCon :: TyCon -> SDoc
pprSourceTyCon tycon 
  | Just (fam_tc, tys) <- tyConFamInst_maybe tycon
  = ppr $ fam_tc `TyConApp` tys	       -- can't be FunTyCon
  | otherwise
  = ppr tycon
\end{code}

%************************************************************************
%*									*
\subsection{Liftedness}
%*									*
%************************************************************************

\begin{code}
-- | See "Type#type_classification" for what an unlifted type is
isUnLiftedType :: Type -> Bool
	-- isUnLiftedType returns True for forall'd unlifted types:
	--	x :: forall a. Int#
	-- I found bindings like these were getting floated to the top level.
	-- They are pretty bogus types, mind you.  It would be better never to
	-- construct them

isUnLiftedType ty | Just ty' <- coreView ty = isUnLiftedType ty'
isUnLiftedType (ForAllTy _ ty)      = isUnLiftedType ty
isUnLiftedType (TyConApp tc _)      = isUnLiftedTyCon tc
isUnLiftedType _                    = False

isUnboxedTupleType :: Type -> Bool
isUnboxedTupleType ty = case tyConAppTyCon_maybe ty of
                           Just tc -> isUnboxedTupleTyCon tc
                           _       -> False

-- | See "Type#type_classification" for what an algebraic type is.
-- Should only be applied to /types/, as opposed to e.g. partially
-- saturated type constructors
isAlgType :: Type -> Bool
isAlgType ty 
  = case splitTyConApp_maybe ty of
      Just (tc, ty_args) -> ASSERT( ty_args `lengthIs` tyConArity tc )
			    isAlgTyCon tc
      _other	         -> False

-- | See "Type#type_classification" for what an algebraic type is.
-- Should only be applied to /types/, as opposed to e.g. partially
-- saturated type constructors. Closed type constructors are those
-- with a fixed right hand side, as opposed to e.g. associated types
isClosedAlgType :: Type -> Bool
isClosedAlgType ty
  = case splitTyConApp_maybe ty of
      Just (tc, ty_args) | isAlgTyCon tc && not (isFamilyTyCon tc)
             -> ASSERT2( ty_args `lengthIs` tyConArity tc, ppr ty ) True
      _other -> False
\end{code}

\begin{code}
-- | Computes whether an argument (or let right hand side) should
-- be computed strictly or lazily, based only on its type.
-- Works just like 'isUnLiftedType', except that it has a special case 
-- for dictionaries (i.e. does not work purely on representation types)

-- Since it takes account of class 'PredType's, you might think
-- this function should be in 'TcType', but 'isStrictType' is used by 'DataCon',
-- which is below 'TcType' in the hierarchy, so it's convenient to put it here.
--
-- We may be strict in dictionary types, but only if it 
-- has more than one component.
--
-- (Being strict in a single-component dictionary risks
--  poking the dictionary component, which is wrong.)
isStrictType :: Type -> Bool
isStrictType ty | Just ty' <- coreView ty = isStrictType ty'
isStrictType (ForAllTy _ ty)   = isStrictType ty
isStrictType (TyConApp tc _)
 | isUnLiftedTyCon tc               = True
 | isClassTyCon tc, opt_DictsStrict = True
isStrictType _                      = False
\end{code}

\begin{code}
isPrimitiveType :: Type -> Bool
-- ^ Returns true of types that are opaque to Haskell.
-- Most of these are unlifted, but now that we interact with .NET, we
-- may have primtive (foreign-imported) types that are lifted
isPrimitiveType ty = case splitTyConApp_maybe ty of
			Just (tc, ty_args) -> ASSERT( ty_args `lengthIs` tyConArity tc )
					      isPrimTyCon tc
			_                  -> False
\end{code}


%************************************************************************
%*									*
\subsection{Sequencing on types}
%*									*
%************************************************************************

\begin{code}
seqType :: Type -> ()
seqType (TyVarTy tv) 	  = tv `seq` ()
seqType (AppTy t1 t2) 	  = seqType t1 `seq` seqType t2
seqType (FunTy t1 t2) 	  = seqType t1 `seq` seqType t2
seqType (TyConApp tc tys) = tc `seq` seqTypes tys
seqType (ForAllTy tv ty)  = tv `seq` seqType ty

seqTypes :: [Type] -> ()
seqTypes []       = ()
seqTypes (ty:tys) = seqType ty `seq` seqTypes tys
\end{code}


%************************************************************************
%*									*
		Comparision for types 
	(We don't use instances so that we know where it happens)
%*									*
%************************************************************************

\begin{code}
eqKind :: Kind -> Kind -> Bool
eqKind = eqType

eqType :: Type -> Type -> Bool
-- ^ Type equality on source types. Does not look through @newtypes@ or 
-- 'PredType's, but it does look through type synonyms.
eqType t1 t2 = isEqual $ cmpType t1 t2

eqTypeX :: RnEnv2 -> Type -> Type -> Bool
eqTypeX env t1 t2 = isEqual $ cmpTypeX env t1 t2

eqTypes :: [Type] -> [Type] -> Bool
eqTypes tys1 tys2 = isEqual $ cmpTypes tys1 tys2

eqPred :: PredType -> PredType -> Bool
eqPred = eqType

eqPredX :: RnEnv2 -> PredType -> PredType -> Bool
eqPredX env p1 p2 = isEqual $ cmpTypeX env p1 p2
\end{code}

Now here comes the real worker

\begin{code}
cmpType :: Type -> Type -> Ordering
cmpType t1 t2 = cmpTypeX rn_env t1 t2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyVarsOfType t1 `unionVarSet` tyVarsOfType t2))

cmpTypes :: [Type] -> [Type] -> Ordering
cmpTypes ts1 ts2 = cmpTypesX rn_env ts1 ts2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyVarsOfTypes ts1 `unionVarSet` tyVarsOfTypes ts2))

cmpPred :: PredType -> PredType -> Ordering
cmpPred p1 p2 = cmpTypeX rn_env p1 p2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyVarsOfType p1 `unionVarSet` tyVarsOfType p2))

cmpTypeX :: RnEnv2 -> Type -> Type -> Ordering	-- Main workhorse
cmpTypeX env t1 t2 | Just t1' <- coreView t1 = cmpTypeX env t1' t2
		   | Just t2' <- coreView t2 = cmpTypeX env t1 t2'
-- We expand predicate types, because in Core-land we have
-- lots of definitions like
--      fOrdBool :: Ord Bool
--      fOrdBool = D:Ord .. .. ..
-- So the RHS has a data type

cmpTypeX env (TyVarTy tv1)       (TyVarTy tv2)       = rnOccL env tv1 `compare` rnOccR env tv2
cmpTypeX env (ForAllTy tv1 t1)   (ForAllTy tv2 t2)   = cmpTypeX (rnBndr2 env tv1 tv2) t1 t2
cmpTypeX env (AppTy s1 t1)       (AppTy s2 t2)       = cmpTypeX env s1 s2 `thenCmp` cmpTypeX env t1 t2
cmpTypeX env (FunTy s1 t1)       (FunTy s2 t2)       = cmpTypeX env s1 s2 `thenCmp` cmpTypeX env t1 t2
cmpTypeX env (TyConApp tc1 tys1) (TyConApp tc2 tys2) = (tc1 `compare` tc2) `thenCmp` cmpTypesX env tys1 tys2

    -- Deal with the rest: TyVarTy < AppTy < FunTy < TyConApp < ForAllTy < PredTy
cmpTypeX _ (AppTy _ _)    (TyVarTy _)    = GT

cmpTypeX _ (FunTy _ _)    (TyVarTy _)    = GT
cmpTypeX _ (FunTy _ _)    (AppTy _ _)    = GT

cmpTypeX _ (TyConApp _ _) (TyVarTy _)    = GT
cmpTypeX _ (TyConApp _ _) (AppTy _ _)    = GT
cmpTypeX _ (TyConApp _ _) (FunTy _ _)    = GT

cmpTypeX _ (ForAllTy _ _) (TyVarTy _)    = GT
cmpTypeX _ (ForAllTy _ _) (AppTy _ _)    = GT
cmpTypeX _ (ForAllTy _ _) (FunTy _ _)    = GT
cmpTypeX _ (ForAllTy _ _) (TyConApp _ _) = GT

cmpTypeX _ _              _              = LT

-------------
cmpTypesX :: RnEnv2 -> [Type] -> [Type] -> Ordering
cmpTypesX _   []        []        = EQ
cmpTypesX env (t1:tys1) (t2:tys2) = cmpTypeX env t1 t2 `thenCmp` cmpTypesX env tys1 tys2
cmpTypesX _   []        _         = LT
cmpTypesX _   _         []        = GT
\end{code}

Note [cmpTypeX]
~~~~~~~~~~~~~~~

When we compare foralls, we should look at the kinds. But if we do so,
we get a corelint error like the following (in
libraries/ghc-prim/GHC/PrimopWrappers.hs):

    Binder's type: forall (o_abY :: *).
                   o_abY
                   -> GHC.Prim.State# GHC.Prim.RealWorld
                   -> GHC.Prim.State# GHC.Prim.RealWorld
    Rhs type: forall (a_12 :: ?).
              a_12
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> GHC.Prim.State# GHC.Prim.RealWorld

This is why we don't look at the kind. Maybe we should look if the
kinds are compatible.

-- cmpTypeX env (ForAllTy tv1 t1)   (ForAllTy tv2 t2)
--   = cmpTypeX env (tyVarKind tv1) (tyVarKind tv2) `thenCmp`
--     cmpTypeX (rnBndr2 env tv1 tv2) t1 t2

%************************************************************************
%*									*
		Type substitutions
%*									*
%************************************************************************

\begin{code}
emptyTvSubstEnv :: TvSubstEnv
emptyTvSubstEnv = emptyVarEnv

composeTvSubst :: InScopeSet -> TvSubstEnv -> TvSubstEnv -> TvSubstEnv
-- ^ @(compose env1 env2)(x)@ is @env1(env2(x))@; i.e. apply @env2@ then @env1@.
-- It assumes that both are idempotent.
-- Typically, @env1@ is the refinement to a base substitution @env2@
composeTvSubst in_scope env1 env2
  = env1 `plusVarEnv` mapVarEnv (substTy subst1) env2
	-- First apply env1 to the range of env2
	-- Then combine the two, making sure that env1 loses if
	-- both bind the same variable; that's why env1 is the
	--  *left* argument to plusVarEnv, because the right arg wins
  where
    subst1 = TvSubst in_scope env1

emptyTvSubst :: TvSubst
emptyTvSubst = TvSubst emptyInScopeSet emptyTvSubstEnv

isEmptyTvSubst :: TvSubst -> Bool
	 -- See Note [Extending the TvSubstEnv]
isEmptyTvSubst (TvSubst _ tenv) = isEmptyVarEnv tenv

mkTvSubst :: InScopeSet -> TvSubstEnv -> TvSubst
mkTvSubst = TvSubst

getTvSubstEnv :: TvSubst -> TvSubstEnv
getTvSubstEnv (TvSubst _ env) = env

getTvInScope :: TvSubst -> InScopeSet
getTvInScope (TvSubst in_scope _) = in_scope

isInScope :: Var -> TvSubst -> Bool
isInScope v (TvSubst in_scope _) = v `elemInScopeSet` in_scope

notElemTvSubst :: CoVar -> TvSubst -> Bool
notElemTvSubst v (TvSubst _ tenv) = not (v `elemVarEnv` tenv)

setTvSubstEnv :: TvSubst -> TvSubstEnv -> TvSubst
setTvSubstEnv (TvSubst in_scope _) tenv = TvSubst in_scope tenv

zapTvSubstEnv :: TvSubst -> TvSubst
zapTvSubstEnv (TvSubst in_scope _) = TvSubst in_scope emptyVarEnv

extendTvInScope :: TvSubst -> Var -> TvSubst
extendTvInScope (TvSubst in_scope tenv) var = TvSubst (extendInScopeSet in_scope var) tenv

extendTvInScopeList :: TvSubst -> [Var] -> TvSubst
extendTvInScopeList (TvSubst in_scope tenv) vars = TvSubst (extendInScopeSetList in_scope vars) tenv

extendTvSubst :: TvSubst -> TyVar -> Type -> TvSubst
extendTvSubst (TvSubst in_scope tenv) tv ty = TvSubst in_scope (extendVarEnv tenv tv ty)

extendTvSubstList :: TvSubst -> [TyVar] -> [Type] -> TvSubst
extendTvSubstList (TvSubst in_scope tenv) tvs tys 
  = TvSubst in_scope (extendVarEnvList tenv (tvs `zip` tys))

unionTvSubst :: TvSubst -> TvSubst -> TvSubst
-- Works when the ranges are disjoint
unionTvSubst (TvSubst in_scope1 tenv1) (TvSubst in_scope2 tenv2)
  = ASSERT( not (tenv1 `intersectsVarEnv` tenv2) )
    TvSubst (in_scope1 `unionInScope` in_scope2)
            (tenv1     `plusVarEnv`   tenv2)

-- mkOpenTvSubst and zipOpenTvSubst generate the in-scope set from
-- the types given; but it's just a thunk so with a bit of luck
-- it'll never be evaluated

-- Note [Generating the in-scope set for a substitution]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- If we want to substitute [a -> ty1, b -> ty2] I used to 
-- think it was enough to generate an in-scope set that includes
-- fv(ty1,ty2).  But that's not enough; we really should also take the
-- free vars of the type we are substituting into!  Example:
--	(forall b. (a,b,x)) [a -> List b]
-- Then if we use the in-scope set {b}, there is a danger we will rename
-- the forall'd variable to 'x' by mistake, getting this:
--	(forall x. (List b, x, x)
-- Urk!  This means looking at all the calls to mkOpenTvSubst....


-- | Generates the in-scope set for the 'TvSubst' from the types in the incoming
-- environment, hence "open"
mkOpenTvSubst :: TvSubstEnv -> TvSubst
mkOpenTvSubst tenv = TvSubst (mkInScopeSet (tyVarsOfTypes (varEnvElts tenv))) tenv

-- | Generates the in-scope set for the 'TvSubst' from the types in the incoming
-- environment, hence "open"
zipOpenTvSubst :: [TyVar] -> [Type] -> TvSubst
zipOpenTvSubst tyvars tys 
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipOpenTvSubst" (ppr tyvars $$ ppr tys) emptyTvSubst
  | otherwise
  = TvSubst (mkInScopeSet (tyVarsOfTypes tys)) (zipTyEnv tyvars tys)

-- | Called when doing top-level substitutions. Here we expect that the 
-- free vars of the range of the substitution will be empty.
mkTopTvSubst :: [(TyVar, Type)] -> TvSubst
mkTopTvSubst prs = TvSubst emptyInScopeSet (mkVarEnv prs)

zipTopTvSubst :: [TyVar] -> [Type] -> TvSubst
zipTopTvSubst tyvars tys 
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipTopTvSubst" (ppr tyvars $$ ppr tys) emptyTvSubst
  | otherwise
  = TvSubst emptyInScopeSet (zipTyEnv tyvars tys)

zipTyEnv :: [TyVar] -> [Type] -> TvSubstEnv
zipTyEnv tyvars tys
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipTyEnv" (ppr tyvars $$ ppr tys) emptyVarEnv
  | otherwise
  = zip_ty_env tyvars tys emptyVarEnv

-- Later substitutions in the list over-ride earlier ones, 
-- but there should be no loops
zip_ty_env :: [TyVar] -> [Type] -> TvSubstEnv -> TvSubstEnv
zip_ty_env []       []       env = env
zip_ty_env (tv:tvs) (ty:tys) env = zip_ty_env tvs tys (extendVarEnv env tv ty)
	-- There used to be a special case for when 
	--	ty == TyVarTy tv
	-- (a not-uncommon case) in which case the substitution was dropped.
	-- But the type-tidier changes the print-name of a type variable without
	-- changing the unique, and that led to a bug.   Why?  Pre-tidying, we had 
	-- a type {Foo t}, where Foo is a one-method class.  So Foo is really a newtype.
	-- And it happened that t was the type variable of the class.  Post-tiding, 
	-- it got turned into {Foo t2}.  The ext-core printer expanded this using
	-- sourceTypeRep, but that said "Oh, t == t2" because they have the same unique,
	-- and so generated a rep type mentioning t not t2.  
	--
	-- Simplest fix is to nuke the "optimisation"
zip_ty_env tvs      tys      env   = pprTrace "Var/Type length mismatch: " (ppr tvs $$ ppr tys) env
-- zip_ty_env _ _ env = env

instance Outputable TvSubst where
  ppr (TvSubst ins tenv)
    = brackets $ sep[ ptext (sLit "TvSubst"),
		      nest 2 (ptext (sLit "In scope:") <+> ppr ins), 
		      nest 2 (ptext (sLit "Type env:") <+> ppr tenv) ]
\end{code}

%************************************************************************
%*									*
		Performing type or kind substitutions
%*									*
%************************************************************************

\begin{code}
-- | Type substitution making use of an 'TvSubst' that
-- is assumed to be open, see 'zipOpenTvSubst'
substTyWith :: [TyVar] -> [Type] -> Type -> Type
substTyWith tvs tys = ASSERT( length tvs == length tys )
		      substTy (zipOpenTvSubst tvs tys)

substKiWith :: [KindVar] -> [Kind] -> Kind -> Kind
substKiWith = substTyWith

-- | Type substitution making use of an 'TvSubst' that
-- is assumed to be open, see 'zipOpenTvSubst'
substTysWith :: [TyVar] -> [Type] -> [Type] -> [Type]
substTysWith tvs tys = ASSERT( length tvs == length tys )
		       substTys (zipOpenTvSubst tvs tys)

substKisWith :: [KindVar] -> [Kind] -> [Kind] -> [Kind]
substKisWith = substTysWith

-- | Substitute within a 'Type'
substTy :: TvSubst -> Type  -> Type
substTy subst ty | isEmptyTvSubst subst = ty
		 | otherwise	        = subst_ty subst ty

-- | Substitute within several 'Type's
substTys :: TvSubst -> [Type] -> [Type]
substTys subst tys | isEmptyTvSubst subst = tys
	           | otherwise	          = map (subst_ty subst) tys

-- | Substitute within a 'ThetaType'
substTheta :: TvSubst -> ThetaType -> ThetaType
substTheta subst theta
  | isEmptyTvSubst subst = theta
  | otherwise	         = map (substTy subst) theta

-- | Remove any nested binders mentioning the 'TyVar's in the 'TyVarSet'
deShadowTy :: TyVarSet -> Type -> Type
deShadowTy tvs ty 
  = subst_ty (mkTvSubst in_scope emptyTvSubstEnv) ty
  where
    in_scope = mkInScopeSet tvs

subst_ty :: TvSubst -> Type -> Type
-- subst_ty is the main workhorse for type substitution
--
-- Note that the in_scope set is poked only if we hit a forall
-- so it may often never be fully computed 
subst_ty subst ty
   = go ty
  where
    go (TyVarTy tv)      = substTyVar subst tv
    go (TyConApp tc tys) = let args = map go tys
                           in  args `seqList` TyConApp tc args

    go (FunTy arg res)   = (FunTy $! (go arg)) $! (go res)
    go (AppTy fun arg)   = mkAppTy (go fun) $! (go arg)
                -- The mkAppTy smart constructor is important
                -- we might be replacing (a Int), represented with App
                -- by [Int], represented with TyConApp
    go (ForAllTy tv ty)  = case substTyVarBndr subst tv of
                              (subst', tv') ->
                                 ForAllTy tv' $! (subst_ty subst' ty)

substTyVar :: TvSubst -> TyVar  -> Type
substTyVar (TvSubst _ tenv) tv
  | Just ty  <- lookupVarEnv tenv tv      = ty  -- See Note [Apply Once]
  | otherwise = ASSERT( isTyVar tv ) TyVarTy tv
  -- We do not require that the tyvar is in scope
  -- Reason: we do quite a bit of (substTyWith [tv] [ty] tau)
  -- and it's a nuisance to bring all the free vars of tau into
  -- scope --- and then force that thunk at every tyvar
  -- Instead we have an ASSERT in substTyVarBndr to check for capture

substTyVars :: TvSubst -> [TyVar] -> [Type]
substTyVars subst tvs = map (substTyVar subst) tvs

lookupTyVar :: TvSubst -> TyVar  -> Maybe Type
	-- See Note [Extending the TvSubst]
lookupTyVar (TvSubst _ tenv) tv = lookupVarEnv tenv tv

substTyVarBndr :: TvSubst -> TyVar -> (TvSubst, TyVar)
substTyVarBndr subst@(TvSubst in_scope tenv) old_var
  = ASSERT2( _no_capture, ppr old_var $$ ppr subst ) 
    (TvSubst (in_scope `extendInScopeSet` new_var) new_env, new_var)
  where
    new_env | no_change = delVarEnv tenv old_var
	    | otherwise = extendVarEnv tenv old_var (TyVarTy new_var)

    _no_capture = not (new_var `elemVarSet` tyVarsOfTypes (varEnvElts tenv))
    -- Assertion check that we are not capturing something in the substitution

    old_ki = tyVarKind old_var
    no_kind_change = isEmptyVarSet (tyVarsOfType old_ki) -- verify that kind is closed
    no_change = no_kind_change && (new_var == old_var)
	-- no_change means that the new_var is identical in
	-- all respects to the old_var (same unique, same kind)
	-- See Note [Extending the TvSubst]
	--
	-- In that case we don't need to extend the substitution
	-- to map old to new.  But instead we must zap any 
	-- current substitution for the variable. For example:
	--	(\x.e) with id_subst = [x |-> e']
	-- Here we must simply zap the substitution for x

    new_var | no_kind_change = uniqAway in_scope old_var
            | otherwise = uniqAway in_scope $ updateTyVarKind (substTy subst) old_var
	-- The uniqAway part makes sure the new variable is not already in scope

cloneTyVarBndr :: TvSubst -> TyVar -> Unique -> (TvSubst, TyVar)
cloneTyVarBndr (TvSubst in_scope tv_env) tv uniq
  = (TvSubst (extendInScopeSet in_scope tv')
             (extendVarEnv tv_env tv (mkTyVarTy tv')), tv')
  where
    tv' = setVarUnique tv uniq	-- Simply set the unique; the kind
    	  	       	  	-- has no type variables to worry about
\end{code}

----------------------------------------------------
-- Kind Stuff

Kinds
~~~~~

For the description of subkinding in GHC, see
  http://hackage.haskell.org/trac/ghc/wiki/Commentary/Compiler/TypeType#Kinds

\begin{code}
type MetaKindVar = TyVar  -- invariant: MetaKindVar will always be a
                          -- TcTyVar with details MetaTv TauTv ...
-- meta kind var constructors and functions are in TcType

type SimpleKind = Kind
\end{code}

%************************************************************************
%*                                                                      *
        The kind of a type
%*                                                                      *
%************************************************************************

\begin{code}
typeKind :: Type -> Kind
typeKind (TyConApp tc tys)
  | isPromotedTypeTyCon tc
  = ASSERT( tyConArity tc == length tys ) tySuperKind
  | otherwise
  = kindAppResult (tyConKind tc) tys

typeKind (AppTy fun arg)      = kindAppResult (typeKind fun) [arg]
typeKind (ForAllTy _ ty)      = typeKind ty
typeKind (TyVarTy tyvar)      = tyVarKind tyvar
typeKind (FunTy _arg res)
    -- Hack alert.  The kind of (Int -> Int#) is liftedTypeKind (*), 
    --              not unliftedTypKind (#)
    -- The only things that can be after a function arrow are
    --   (a) types (of kind openTypeKind or its sub-kinds)
    --   (b) kinds (of super-kind TY) (e.g. * -> (* -> *))
    | isSuperKind k         = k
    | otherwise             = ASSERT( isSubOpenTypeKind k ) liftedTypeKind
    where
      k = typeKind res

\end{code}

Kind inference
~~~~~~~~~~~~~~
During kind inference, a kind variable unifies only with 
a "simple kind", sk
	sk ::= * | sk1 -> sk2
For example 
	data T a = MkT a (T Int#)
fails.  We give T the kind (k -> *), and the kind variable k won't unify
with # (the kind of Int#).

Type inference
~~~~~~~~~~~~~~
When creating a fresh internal type variable, we give it a kind to express 
constraints on it.  E.g. in (\x->e) we make up a fresh type variable for x, 
with kind ??.  

During unification we only bind an internal type variable to a type
whose kind is lower in the sub-kind hierarchy than the kind of the tyvar.

When unifying two internal type variables, we collect their kind constraints by
finding the GLB of the two.  Since the partial order is a tree, they only
have a glb if one is a sub-kind of the other.  In that case, we bind the
less-informative one to the more informative one.  Neat, eh?
