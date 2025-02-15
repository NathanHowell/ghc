 | %
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1998
%
\section[TypeRep]{Type - friends' interface}

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

-- We expose the relevant stuff from this module via the Type module
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module TypeRep (
	TyThing(..),
	Type(..),
        KindOrType, Kind, SuperKind,
        PredType, ThetaType,      -- Synonyms

        -- Functions over types
        mkTyConApp, mkTyConTy, mkTyVarTy, mkTyVarTys,
        isLiftedTypeKind,
        
        -- Pretty-printing
	pprType, pprParendType, pprTypeApp,
	pprTyThing, pprTyThingCategory, 
	pprEqPred, pprTheta, pprForAll, pprThetaArrowTy, pprClassPred,
        pprKind, pprParendKind,
	Prec(..), maybeParen, pprTcApp, pprTypeNameApp, 
        pprPrefixApp, pprArrowChain, ppr_type,

        -- Free variables
        tyVarsOfType, tyVarsOfTypes,

        -- Substitutions
        TvSubst(..), TvSubstEnv
    ) where

#include "HsVersions.h"

import {-# SOURCE #-} DataCon( DataCon, dataConName )
import {-# SOURCE #-} Type( noParenPred, isPredTy ) -- Transitively pulls in a LOT of stuff, better to break the loop

-- friends:
import Var
import VarEnv
import VarSet
import Name
import BasicTypes
import TyCon
import Class

-- others
import PrelNames
import Outputable
import FastString
import Pair

-- libraries
import qualified Data.Data        as Data hiding ( TyCon )
\end{code}

	----------------------
	A note about newtypes
	----------------------

Consider
	newtype N = MkN Int

Then we want N to be represented as an Int, and that's what we arrange.
The front end of the compiler [TcType.lhs] treats N as opaque, 
the back end treats it as transparent [Type.lhs].

There's a bit of a problem with recursive newtypes
	newtype P = MkP P
	newtype Q = MkQ (Q->Q)

Here the 'implicit expansion' we get from treating P and Q as transparent
would give rise to infinite types, which in turn makes eqType diverge.
Similarly splitForAllTys and splitFunTys can get into a loop.  

Solution: 

* Newtypes are always represented using TyConApp.

* For non-recursive newtypes, P, treat P just like a type synonym after 
  type-checking is done; i.e. it's opaque during type checking (functions
  from TcType) but transparent afterwards (functions from Type).  
  "Treat P as a type synonym" means "all functions expand NewTcApps 
  on the fly".

  Applications of the data constructor P simply vanish:
	P x = x
  

* For recursive newtypes Q, treat the Q and its representation as 
  distinct right through the compiler.  Applications of the data consructor
  use a coerce:
	Q = \(x::Q->Q). coerce Q x
  They are rare, so who cares if they are a tiny bit less efficient.

The typechecker (TcTyDecls) identifies enough type construtors as 'recursive'
to cut all loops.  The other members of the loop may be marked 'non-recursive'.


%************************************************************************
%*									*
\subsection{The data type}
%*									*
%************************************************************************


\begin{code}
-- | The key representation of types within the compiler
data Type
  = TyVarTy Var	-- ^ Vanilla type or kind variable (*never* a coercion variable)

  | AppTy
	Type
	Type		-- ^ Type application to something other than a 'TyCon'. Parameters:
	                --
                        --  1) Function: must /not/ be a 'TyConApp',
                        --     must be another 'AppTy', or 'TyVarTy'
	                --
	                --  2) Argument type

  | TyConApp
	TyCon
	[KindOrType]	-- ^ Application of a 'TyCon', including newtypes /and/ synonyms.
	                -- Invariant: saturated appliations of 'FunTyCon' must
	                -- use 'FunTy' and saturated synonyms must use their own
                        -- constructors. However, /unsaturated/ 'FunTyCon's
                        -- do appear as 'TyConApp's.
	                -- Parameters:
	                --
	                -- 1) Type constructor being applied to.
	                --
                        -- 2) Type arguments. Might not have enough type arguments
                        --    here to saturate the constructor.
                        --    Even type synonyms are not necessarily saturated;
                        --    for example unsaturated type synonyms
	                --    can appear as the right hand side of a type synonym.

  | FunTy
	Type		
	Type		-- ^ Special case of 'TyConApp': @TyConApp FunTyCon [t1, t2]@
			-- See Note [Equality-constrained types]

  | ForAllTy
	Var         -- Type or kind variable
	Type	        -- ^ A polymorphic type

  deriving (Data.Data, Data.Typeable)

type KindOrType = Type -- See Note [Arguments to type constructors]

-- | The key type representing kinds in the compiler.
-- Invariant: a kind is always in one of these forms:
--
-- > FunTy k1 k2
-- > TyConApp PrimTyCon [...]
-- > TyVar kv   -- (during inference only)
-- > ForAll ... -- (for top-level coercions)
type Kind = Type

-- | "Super kinds", used to help encode 'Kind's as types.
-- Invariant: a super kind is always of this form:
--
-- > TyConApp SuperKindTyCon ...
type SuperKind = Type
\end{code}


Note [Arguments to type constructors]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because of kind polymorphism, in addition to type application we now
have kind instantiation. We reuse the same notations to do so.

For example:

  Just (* -> *) Maybe
  Right * Nat Zero

are represented by:

  TyConApp (PromotedDataCon Just) [* -> *, Maybe]
  TyConApp (PromotedDataCon Right) [*, Nat, (PromotedDataCon Zero)]

Important note: Nat is used as a *kind* and not as a type. This can be
confusing, since type-level Nat and kind-level Nat are identical. We
use the kind of (PromotedDataCon Right) to know if its arguments are
kinds or types.

This kind instantiation only happens in TyConApp currently.


Note [Equality-constrained types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The type   forall ab. (a ~ [b]) => blah
is encoded like this:

   ForAllTy (a:*) $ ForAllTy (b:*) $
   FunTy (TyConApp (~) [a, [b]]) $
   blah

-------------------------------------
 		Note [PredTy]

\begin{code}
-- | A type of the form @p@ of kind @Constraint@ represents a value whose type is
-- the Haskell predicate @p@, where a predicate is what occurs before 
-- the @=>@ in a Haskell type.
--
-- We use 'PredType' as documentation to mark those types that we guarantee to have
-- this kind.
--
-- It can be expanded into its representation, but: 
--
-- * The type checker must treat it as opaque
--
-- * The rest of the compiler treats it as transparent
--
-- Consider these examples:
--
-- > f :: (Eq a) => a -> Int
-- > g :: (?x :: Int -> Int) => a -> Int
-- > h :: (r\l) => {r} => {l::Int | r}
--
-- Here the @Eq a@ and @?x :: Int -> Int@ and @r\l@ are all called \"predicates\"
type PredType = Type

-- | A collection of 'PredType's
type ThetaType = [PredType]
\end{code}

(We don't support TREX records yet, but the setup is designed
to expand to allow them.)

A Haskell qualified type, such as that for f,g,h above, is
represented using 
	* a FunTy for the double arrow
	* with a type of kind Constraint as the function argument

The predicate really does turn into a real extra argument to the
function.  If the argument has type (p :: Constraint) then the predicate p is
represented by evidence of type p.

%************************************************************************
%*									*
            Simple constructors
%*									*
%************************************************************************

These functions are here so that they can be used by TysPrim,
which in turn is imported by Type

\begin{code}
mkTyVarTy  :: TyVar   -> Type
mkTyVarTy  = TyVarTy

mkTyVarTys :: [TyVar] -> [Type]
mkTyVarTys = map mkTyVarTy -- a common use of mkTyVarTy

-- | A key function: builds a 'TyConApp' or 'FunTy' as apppropriate to its arguments.
-- Applies its arguments to the constructor from left to right
mkTyConApp :: TyCon -> [Type] -> Type
mkTyConApp tycon tys
  | isFunTyCon tycon, [ty1,ty2] <- tys
  = FunTy ty1 ty2

  | otherwise
  = TyConApp tycon tys

-- | Create the plain type constructor type which has been applied to no type arguments at all.
mkTyConTy :: TyCon -> Type
mkTyConTy tycon = mkTyConApp tycon []

isLiftedTypeKind :: Kind -> Bool
-- This function is here because it's used in the pretty printer
isLiftedTypeKind (TyConApp tc []) = tc `hasKey` liftedTypeKindTyConKey
isLiftedTypeKind _                = False
\end{code}


%************************************************************************
%*									*
			Free variables of types and coercions
%*									*
%************************************************************************

\begin{code}
tyVarsOfType :: Type -> VarSet
-- ^ NB: for type synonyms tyVarsOfType does /not/ expand the synonym
-- tyVarsOfType returns only the free *type* variables of a type
-- For example, tyVarsOfType (a::k) returns {a}, not including the
-- kind variable {k}
tyVarsOfType (TyVarTy v)         = unitVarSet v
tyVarsOfType (TyConApp _ tys)    = tyVarsOfTypes tys
tyVarsOfType (FunTy arg res)     = tyVarsOfType arg `unionVarSet` tyVarsOfType res
tyVarsOfType (AppTy fun arg)     = tyVarsOfType fun `unionVarSet` tyVarsOfType arg
tyVarsOfType (ForAllTy tyvar ty) = delVarSet (tyVarsOfType ty) tyvar

tyVarsOfTypes :: [Type] -> TyVarSet
tyVarsOfTypes tys = foldr (unionVarSet . tyVarsOfType) emptyVarSet tys
\end{code}

%************************************************************************
%*									*
			TyThing
%*									*
%************************************************************************

Despite the fact that DataCon has to be imported via a hi-boot route, 
this module seems the right place for TyThing, because it's needed for
funTyCon and all the types in TysPrim.

Note [ATyCon for classes]
~~~~~~~~~~~~~~~~~~~~~~~~~
Both classes and type constructors are represented in the type environment
as ATyCon.  You can tell the difference, and get to the class, with
   isClassTyCon :: TyCon -> Bool
   tyConClass_maybe :: TyCon -> Maybe Class
The Class and its associated TyCon have the same Name.

\begin{code}
-- | A typecheckable-thing, essentially anything that has a name
data TyThing 
  = AnId     Id
  | ADataCon DataCon
  | ATyCon   TyCon       -- TyCons and classes; see Note [ATyCon for classes]
  | ACoAxiom CoAxiom
  deriving (Eq, Ord)

instance Outputable TyThing where 
  ppr = pprTyThing

pprTyThing :: TyThing -> SDoc
pprTyThing thing = pprTyThingCategory thing <+> quotes (ppr (getName thing))

pprTyThingCategory :: TyThing -> SDoc
pprTyThingCategory (ATyCon tc)
  | isClassTyCon tc = ptext (sLit "Class")
  | otherwise       = ptext (sLit "Type constructor")
pprTyThingCategory (ACoAxiom _) = ptext (sLit "Coercion axiom")
pprTyThingCategory (AnId   _)   = ptext (sLit "Identifier")
pprTyThingCategory (ADataCon _) = ptext (sLit "Data constructor")


instance NamedThing TyThing where	-- Can't put this with the type
  getName (AnId id)     = getName id	-- decl, because the DataCon instance
  getName (ATyCon tc)   = getName tc	-- isn't visible there
  getName (ACoAxiom cc) = getName cc
  getName (ADataCon dc) = dataConName dc

\end{code}


%************************************************************************
%*									*
			Substitutions
      Data type defined here to avoid unnecessary mutual recursion
%*									*
%************************************************************************

\begin{code}
-- | Type substitution
--
-- #tvsubst_invariant#
-- The following invariants must hold of a 'TvSubst':
-- 
-- 1. The in-scope set is needed /only/ to
-- guide the generation of fresh uniques
--
-- 2. In particular, the /kind/ of the type variables in 
-- the in-scope set is not relevant
--
-- 3. The substition is only applied ONCE! This is because
-- in general such application will not reached a fixed point.
data TvSubst 		
  = TvSubst InScopeSet 	-- The in-scope type and kind variables
	    TvSubstEnv  -- Substitutes both type and kind variables
	-- See Note [Apply Once]
	-- and Note [Extending the TvSubstEnv]

-- | A substitition of 'Type's for 'TyVar's
--                 and 'Kind's for 'KindVar's
type TvSubstEnv = TyVarEnv Type
	-- A TvSubstEnv is used both inside a TvSubst (with the apply-once
	-- invariant discussed in Note [Apply Once]), and also independently
	-- in the middle of matching, and unification (see Types.Unify)
	-- So you have to look at the context to know if it's idempotent or
	-- apply-once or whatever
\end{code}

Note [Apply Once]
~~~~~~~~~~~~~~~~~
We use TvSubsts to instantiate things, and we might instantiate
	forall a b. ty
\with the types
	[a, b], or [b, a].
So the substition might go [a->b, b->a].  A similar situation arises in Core
when we find a beta redex like
	(/\ a /\ b -> e) b a
Then we also end up with a substition that permutes type variables. Other
variations happen to; for example [a -> (a, b)].  

	***************************************************
	*** So a TvSubst must be applied precisely once ***
	***************************************************

A TvSubst is not idempotent, but, unlike the non-idempotent substitution
we use during unifications, it must not be repeatedly applied.

Note [Extending the TvSubst]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
See #tvsubst_invariant# for the invariants that must hold.

This invariant allows a short-cut when the TvSubstEnv is empty:
if the TvSubstEnv is empty --- i.e. (isEmptyTvSubt subst) holds ---
then (substTy subst ty) does nothing.

For example, consider:
	(/\a. /\b:(a~Int). ...b..) Int
We substitute Int for 'a'.  The Unique of 'b' does not change, but
nevertheless we add 'b' to the TvSubstEnv, because b's kind does change

This invariant has several crucial consequences:

* In substTyVarBndr, we need extend the TvSubstEnv 
	- if the unique has changed
	- or if the kind has changed

* In substTyVar, we do not need to consult the in-scope set;
  the TvSubstEnv is enough

* In substTy, substTheta, we can short-circuit when the TvSubstEnv is empty



%************************************************************************
%*									*
                   Pretty-printing types

       Defined very early because of debug printing in assertions
%*                                                                      *
%************************************************************************

@pprType@ is the standard @Type@ printer; the overloaded @ppr@ function is
defined to use this.  @pprParendType@ is the same, except it puts
parens around the type, except for the atomic cases.  @pprParendType@
works just by setting the initial context precedence very high.

\begin{code}
data Prec = TopPrec 	-- No parens
	  | FunPrec 	-- Function args; no parens for tycon apps
	  | TyConPrec 	-- Tycon args; no parens for atomic
	  deriving( Eq, Ord )

maybeParen :: Prec -> Prec -> SDoc -> SDoc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise		   = parens pretty

------------------
pprType, pprParendType :: Type -> SDoc
pprType       ty = ppr_type TopPrec ty
pprParendType ty = ppr_type TyConPrec ty

pprKind, pprParendKind :: Kind -> SDoc
pprKind       = pprType
pprParendKind = pprParendType

------------------
pprEqPred :: Pair Type -> SDoc
-- NB: Maybe move to Coercion? It's only called after coercionKind anyway. 
pprEqPred (Pair ty1 ty2) 
  = sep [ ppr_type FunPrec ty1
        , nest 2 (ptext (sLit "~#"))
        , ppr_type FunPrec ty2]
    -- Precedence looks like (->) so that we get
    --    Maybe a ~ Bool
    --    (a->a) ~ Bool
    -- Note parens on the latter!

------------
pprClassPred :: Class -> [Type] -> SDoc
pprClassPred = ppr_class_pred ppr_type

ppr_class_pred :: (Prec -> a -> SDoc) -> Class -> [a] -> SDoc
ppr_class_pred pp clas tys = pprTypeNameApp TopPrec pp (getName clas) tys

------------
pprTheta :: ThetaType -> SDoc
-- pprTheta [pred] = pprPred pred	 -- I'm in two minds about this
pprTheta theta  = parens (sep (punctuate comma (map (ppr_type TopPrec) theta)))

pprThetaArrowTy :: ThetaType -> SDoc
pprThetaArrowTy []      = empty
pprThetaArrowTy [pred]
      | noParenPred pred = ppr_type TopPrec pred <+> darrow
pprThetaArrowTy preds   = parens (fsep (punctuate comma (map (ppr_type TopPrec) preds)))
                            <+> darrow
    -- Notice 'fsep' here rather that 'sep', so that
    -- type contexts don't get displayed in a giant column
    -- Rather than
    --  instance (Eq a,
    --            Eq b,
    --            Eq c,
    --            Eq d,
    --            Eq e,
    --            Eq f,
    --            Eq g,
    --            Eq h,
    --            Eq i,
    --            Eq j,
    --            Eq k,
    --            Eq l) =>
    --           Eq (a, b, c, d, e, f, g, h, i, j, k, l)
    -- we get
    --
    --  instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i,
    --            Eq j, Eq k, Eq l) =>
    --           Eq (a, b, c, d, e, f, g, h, i, j, k, l)

------------------
instance Outputable Type where
    ppr ty = pprType ty

instance Outputable name => OutputableBndr (IPName name) where
    pprBndr _ n = ppr n	-- Simple for now

------------------
	-- OK, here's the main printer

ppr_type :: Prec -> Type -> SDoc
ppr_type _ (TyVarTy tv)	      = ppr_tvar tv
ppr_type p (TyConApp tc tys)  = pprTcApp p ppr_type tc tys

ppr_type p (AppTy t1 t2) = maybeParen p TyConPrec $
			   pprType t1 <+> ppr_type TyConPrec t2

ppr_type p ty@(ForAllTy {})        = ppr_forall_type p ty
ppr_type p fun_ty@(FunTy ty1 ty2)
  | isPredTy ty1
  = ppr_forall_type p fun_ty
  | otherwise
  = pprArrowChain p (ppr_type FunPrec ty1 : ppr_fun_tail ty2)
  where
    -- We don't want to lose synonyms, so we mustn't use splitFunTys here.
    ppr_fun_tail (FunTy ty1 ty2)
      | not (isPredTy ty1) = ppr_type FunPrec ty1 : ppr_fun_tail ty2
    ppr_fun_tail other_ty = [ppr_type TopPrec other_ty]

ppr_forall_type :: Prec -> Type -> SDoc
ppr_forall_type p ty
  = maybeParen p FunPrec $
    sep [pprForAll tvs, pprThetaArrowTy ctxt, pprType tau]
  where
    (tvs,  rho) = split1 [] ty
    (ctxt, tau) = split2 [] rho

    split1 tvs (ForAllTy tv ty) = split1 (tv:tvs) ty
    split1 tvs ty          = (reverse tvs, ty)
 
    split2 ps (ty1 `FunTy` ty2) | isPredTy ty1 = split2 (ty1:ps) ty2
    split2 ps ty                               = (reverse ps, ty)

ppr_tvar :: TyVar -> SDoc
ppr_tvar tv  -- Note [Infix type variables]
  = parenSymOcc (getOccName tv) (ppr tv)

-------------------
pprForAll :: [TyVar] -> SDoc
pprForAll []  = empty
pprForAll tvs = ptext (sLit "forall") <+> sep (map pprTvBndr tvs) <> dot

pprTvBndr :: TyVar -> SDoc
pprTvBndr tv 
  | isLiftedTypeKind kind = ppr_tvar tv
  | otherwise	          = parens (ppr_tvar tv <+> dcolon <+> pprKind kind)
	     where
	       kind = tyVarKind tv
\end{code}

Note [Infix type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
With TypeOperators you can say

   f :: (a ~> b) -> b

and the (~>) is considered a type variable.  However, the type
pretty-printer in this module will just see (a ~> b) as

   App (App (TyVarTy "~>") (TyVarTy "a")) (TyVarTy "b")

So it'll print the type in prefix form.  To avoid confusion we must
remember to parenthesise the operator, thus

   (~>) a b -> b

See Trac #2766.

\begin{code}
pprTcApp :: Prec -> (Prec -> a -> SDoc) -> TyCon -> [a] -> SDoc
pprTcApp _ _ tc []      -- No brackets for SymOcc
  = pp_nt_debug <> ppr tc
  where
   pp_nt_debug | isNewTyCon tc = ifPprDebug (if isRecursiveTyCon tc 
				             then ptext (sLit "<recnt>")
					     else ptext (sLit "<nt>"))
	       | otherwise     = empty

pprTcApp _ pp tc [ty]
  | tc `hasKey` listTyConKey = brackets (pp TopPrec ty)
  | tc `hasKey` parrTyConKey = ptext (sLit "[:") <> pp TopPrec ty <> ptext (sLit ":]")
  | tc `hasKey` liftedTypeKindTyConKey   = ptext (sLit "*")
  | tc `hasKey` unliftedTypeKindTyConKey = ptext (sLit "#")
  | tc `hasKey` openTypeKindTyConKey     = ptext (sLit "OpenKind")
  | tc `hasKey` ubxTupleKindTyConKey     = ptext (sLit "(#)")
  | tc `hasKey` argTypeKindTyConKey      = ptext (sLit "ArgKind")
  | Just n <- tyConIP_maybe tc           = ppr n <> ptext (sLit "::") <> pp TopPrec ty

pprTcApp p pp tc tys
  | isTupleTyCon tc && tyConArity tc == length tys
  = tupleParens (tupleTyConSort tc) (sep (punctuate comma (map (pp TopPrec) tys)))
  | tc `hasKey` eqTyConKey -- We need to special case the type equality TyCon because
                           -- its not a SymOcc so won't get printed infix
  , [_, ty1,ty2] <- tys
  = pprInfixApp p pp (getName tc) ty1 ty2
  | otherwise
  = pprTypeNameApp p pp (getName tc) tys

----------------
pprTypeApp :: NamedThing a => a -> [Type] -> SDoc
-- The first arg is the tycon, or sometimes class
-- Print infix if the tycon/class looks like an operator
pprTypeApp tc tys = pprTypeNameApp TopPrec ppr_type (getName tc) tys

pprTypeNameApp :: Prec -> (Prec -> a -> SDoc) -> Name -> [a] -> SDoc
-- Used for classes and coercions as well as types; that's why it's separate from pprTcApp
pprTypeNameApp p pp tc tys
  | is_sym_occ           -- Print infix if possible
  , [ty1,ty2] <- tys  -- We know nothing of precedence though
  = pprInfixApp p pp tc ty1 ty2
  | otherwise
  = pprPrefixApp p (pprPrefixVar is_sym_occ (ppr tc)) (map (pp TyConPrec) tys)
  where
    is_sym_occ = isSymOcc (getOccName tc)

----------------
pprInfixApp :: Prec -> (Prec -> a -> SDoc) -> Name -> a -> a -> SDoc
pprInfixApp p pp tc ty1 ty2
  = maybeParen p FunPrec $
    sep [pp FunPrec ty1, pprInfixVar True (ppr tc) <+> pp FunPrec ty2]

pprPrefixApp :: Prec -> SDoc -> [SDoc] -> SDoc
pprPrefixApp p pp_fun pp_tys = maybeParen p TyConPrec $
                               hang pp_fun 2 (sep pp_tys)

----------------
pprArrowChain :: Prec -> [SDoc] -> SDoc
-- pprArrowChain p [a,b,c]  generates   a -> b -> c
pprArrowChain _ []         = empty
pprArrowChain p (arg:args) = maybeParen p FunPrec $
                             sep [arg, sep (map (arrow <+>) args)]
\end{code}

