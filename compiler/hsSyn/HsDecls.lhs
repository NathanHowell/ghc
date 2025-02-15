%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%

\begin{code}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Abstract syntax of global declarations.
--
-- Definitions for: @TyDecl@ and @ConDecl@, @ClassDecl@,
-- @InstDecl@, @DefaultDecl@ and @ForeignDecl@.
module HsDecls (
  -- * Toplevel declarations
  HsDecl(..), LHsDecl,
  -- ** Class or type declarations
  TyClDecl(..), LTyClDecl, TyClGroup,
  isClassDecl, isSynDecl, isDataDecl, isTypeDecl, isFamilyDecl,
  isFamInstDecl, tcdName, tyClDeclTyVars,
  countTyClDecls,
  -- ** Instance declarations
  InstDecl(..), LInstDecl, NewOrData(..), FamilyFlavour(..),
  instDeclATs,
  -- ** Standalone deriving declarations
  DerivDecl(..), LDerivDecl,
  -- ** @RULE@ declarations
  RuleDecl(..), LRuleDecl, RuleBndr(..),
  collectRuleBndrSigTys,
  -- ** @VECTORISE@ declarations
  VectDecl(..), LVectDecl,
  lvectDeclName, lvectInstDecl,
  -- ** @default@ declarations
  DefaultDecl(..), LDefaultDecl,
  -- ** Top-level template haskell splice
  SpliceDecl(..),
  -- ** Foreign function interface declarations
  ForeignDecl(..), LForeignDecl, ForeignImport(..), ForeignExport(..),
  noForeignImportCoercionYet, noForeignExportCoercionYet,
  CImportSpec(..),
  -- ** Data-constructor declarations
  ConDecl(..), LConDecl, ResType(..), 
  HsConDeclDetails, hsConDeclArgTys, 
  -- ** Document comments
  DocDecl(..), LDocDecl, docDeclDoc,
  -- ** Deprecations
  WarnDecl(..),  LWarnDecl,
  -- ** Annotations
  AnnDecl(..), LAnnDecl, 
  AnnProvenance(..), annProvenanceName_maybe, modifyAnnProvenanceNameM,

  -- * Grouping
  HsGroup(..),  emptyRdrGroup, emptyRnGroup, appendGroups
    ) where

-- friends:
import {-# SOURCE #-}   HsExpr( LHsExpr, HsExpr, pprExpr )
        -- Because Expr imports Decls via HsBracket

import HsBinds
import HsPat
import HsTypes
import HsDoc
import TyCon
import NameSet
import Name
import BasicTypes
import Coercion
import ForeignCall

-- others:
import InstEnv
import Class
import Outputable       
import Util
import SrcLoc
import FastString

import Bag
import Control.Monad    ( liftM )
import Data.Data        hiding (TyCon)
import Data.Maybe       ( isJust )
\end{code}

%************************************************************************
%*                                                                      *
\subsection[HsDecl]{Declarations}
%*                                                                      *
%************************************************************************

\begin{code}
type LHsDecl id = Located (HsDecl id)

-- | A Haskell Declaration
data HsDecl id
  = TyClD       (TyClDecl id)     -- ^ A type or class declaration.
  | InstD       (InstDecl  id)    -- ^ An instance declaration.
  | DerivD      (DerivDecl id)
  | ValD        (HsBind id)
  | SigD        (Sig id)
  | DefD        (DefaultDecl id)
  | ForD        (ForeignDecl id)
  | WarningD    (WarnDecl id)
  | AnnD        (AnnDecl id)
  | RuleD       (RuleDecl id)
  | VectD       (VectDecl id)
  | SpliceD     (SpliceDecl id)
  | DocD        (DocDecl)
  | QuasiQuoteD (HsQuasiQuote id)
  deriving (Data, Typeable)


-- NB: all top-level fixity decls are contained EITHER
-- EITHER SigDs
-- OR     in the ClassDecls in TyClDs
--
-- The former covers
--      a) data constructors
--      b) class methods (but they can be also done in the
--              signatures of class decls)
--      c) imported functions (that have an IfacSig)
--      d) top level decls
--
-- The latter is for class methods only

-- | A 'HsDecl' is categorised into a 'HsGroup' before being
-- fed to the renamer.
data HsGroup id
  = HsGroup {
        hs_valds  :: HsValBinds id,

        hs_tyclds :: [[LTyClDecl id]],  
                -- A list of mutually-recursive groups
                -- Parser generates a singleton list;
                -- renamer does dependency analysis

        hs_instds :: [LInstDecl id],
        hs_derivds :: [LDerivDecl id],

        hs_fixds  :: [LFixitySig id],
                -- Snaffled out of both top-level fixity signatures,
                -- and those in class declarations

        hs_defds  :: [LDefaultDecl id],
        hs_fords  :: [LForeignDecl id],
        hs_warnds :: [LWarnDecl id],
        hs_annds  :: [LAnnDecl id],
        hs_ruleds :: [LRuleDecl id],
        hs_vects  :: [LVectDecl id],

        hs_docs   :: [LDocDecl]
  } deriving (Data, Typeable)

emptyGroup, emptyRdrGroup, emptyRnGroup :: HsGroup a
emptyRdrGroup = emptyGroup { hs_valds = emptyValBindsIn }
emptyRnGroup  = emptyGroup { hs_valds = emptyValBindsOut }

emptyGroup = HsGroup { hs_tyclds = [], hs_instds = [], hs_derivds = [],
                       hs_fixds = [], hs_defds = [], hs_annds = [],
                       hs_fords = [], hs_warnds = [], hs_ruleds = [], hs_vects = [],
                       hs_valds = error "emptyGroup hs_valds: Can't happen",
                       hs_docs = [] }

appendGroups :: HsGroup a -> HsGroup a -> HsGroup a
appendGroups 
    HsGroup { 
        hs_valds  = val_groups1,
        hs_tyclds = tyclds1, 
        hs_instds = instds1,
        hs_derivds = derivds1,
        hs_fixds  = fixds1, 
        hs_defds  = defds1,
        hs_annds  = annds1,
        hs_fords  = fords1, 
        hs_warnds = warnds1,
        hs_ruleds = rulds1,
        hs_vects = vects1,
  hs_docs   = docs1 }
    HsGroup { 
        hs_valds  = val_groups2,
        hs_tyclds = tyclds2, 
        hs_instds = instds2,
        hs_derivds = derivds2,
        hs_fixds  = fixds2, 
        hs_defds  = defds2,
        hs_annds  = annds2,
        hs_fords  = fords2, 
        hs_warnds = warnds2,
        hs_ruleds = rulds2,
        hs_vects  = vects2,
        hs_docs   = docs2 }
  = 
    HsGroup { 
        hs_valds  = val_groups1 `plusHsValBinds` val_groups2,
        hs_tyclds = tyclds1 ++ tyclds2, 
        hs_instds = instds1 ++ instds2,
        hs_derivds = derivds1 ++ derivds2,
        hs_fixds  = fixds1 ++ fixds2,
        hs_annds  = annds1 ++ annds2,
        hs_defds  = defds1 ++ defds2,
        hs_fords  = fords1 ++ fords2, 
        hs_warnds = warnds1 ++ warnds2,
        hs_ruleds = rulds1 ++ rulds2,
        hs_vects  = vects1 ++ vects2,
        hs_docs   = docs1  ++ docs2 }
\end{code}

\begin{code}
instance OutputableBndr name => Outputable (HsDecl name) where
    ppr (TyClD dcl)             = ppr dcl
    ppr (ValD binds)            = ppr binds
    ppr (DefD def)              = ppr def
    ppr (InstD inst)            = ppr inst
    ppr (DerivD deriv)          = ppr deriv
    ppr (ForD fd)               = ppr fd
    ppr (SigD sd)               = ppr sd
    ppr (RuleD rd)              = ppr rd
    ppr (VectD vect)            = ppr vect
    ppr (WarningD wd)           = ppr wd
    ppr (AnnD ad)               = ppr ad
    ppr (SpliceD dd)            = ppr dd
    ppr (DocD doc)              = ppr doc
    ppr (QuasiQuoteD qq)        = ppr qq

instance OutputableBndr name => Outputable (HsGroup name) where
    ppr (HsGroup { hs_valds  = val_decls,
                   hs_tyclds = tycl_decls,
                   hs_instds = inst_decls,
                   hs_derivds = deriv_decls,
                   hs_fixds  = fix_decls,
                   hs_warnds = deprec_decls,
                   hs_annds  = ann_decls,
                   hs_fords  = foreign_decls,
                   hs_defds  = default_decls,
                   hs_ruleds = rule_decls,
                   hs_vects  = vect_decls })
        = vcat_mb empty 
            [ppr_ds fix_decls, ppr_ds default_decls, 
             ppr_ds deprec_decls, ppr_ds ann_decls,
             ppr_ds rule_decls,
             ppr_ds vect_decls,
             if isEmptyValBinds val_decls 
                then Nothing 
                else Just (ppr val_decls),
             ppr_ds (concat tycl_decls), 
             ppr_ds inst_decls,
             ppr_ds deriv_decls,
             ppr_ds foreign_decls]
        where
          ppr_ds :: Outputable a => [a] -> Maybe SDoc
          ppr_ds [] = Nothing
          ppr_ds ds = Just (vcat (map ppr ds))

          vcat_mb :: SDoc -> [Maybe SDoc] -> SDoc
          -- Concatenate vertically with white-space between non-blanks
          vcat_mb _    []             = empty
          vcat_mb gap (Nothing : ds) = vcat_mb gap ds
          vcat_mb gap (Just d  : ds) = gap $$ d $$ vcat_mb blankLine ds

data SpliceDecl id 
  = SpliceDecl                  -- Top level splice
        (Located (HsExpr id))
        HsExplicitFlag          -- Explicit <=> $(f x y)
                                -- Implicit <=> f x y,  i.e. a naked top level expression
    deriving (Data, Typeable)

instance OutputableBndr name => Outputable (SpliceDecl name) where
   ppr (SpliceDecl e _) = ptext (sLit "$") <> parens (pprExpr (unLoc e))
\end{code}


%************************************************************************
%*                                                                      *
\subsection[TyDecl]{@data@, @newtype@ or @type@ (synonym) type declaration}
%*                                                                      *
%************************************************************************

                --------------------------------
                        THE NAMING STORY
                --------------------------------

Here is the story about the implicit names that go with type, class,
and instance decls.  It's a bit tricky, so pay attention!

"Implicit" (or "system") binders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  Each data type decl defines 
        a worker name for each constructor
        to-T and from-T convertors
  Each class decl defines
        a tycon for the class
        a data constructor for that tycon
        the worker for that constructor
        a selector for each superclass

All have occurrence names that are derived uniquely from their parent
declaration.

None of these get separate definitions in an interface file; they are
fully defined by the data or class decl.  But they may *occur* in
interface files, of course.  Any such occurrence must haul in the
relevant type or class decl.

Plan of attack:
 - Ensure they "point to" the parent data/class decl 
   when loading that decl from an interface file
   (See RnHiFiles.getSysBinders)

 - When typechecking the decl, we build the implicit TyCons and Ids.
   When doing so we look them up in the name cache (RnEnv.lookupSysName),
   to ensure correct module and provenance is set

These are the two places that we have to conjure up the magic derived
names.  (The actual magic is in OccName.mkWorkerOcc, etc.)

Default methods
~~~~~~~~~~~~~~~
 - Occurrence name is derived uniquely from the method name
   E.g. $dmmax

 - If there is a default method name at all, it's recorded in
   the ClassOpSig (in HsBinds), in the DefMeth field.
   (DefMeth is defined in Class.lhs)

Source-code class decls and interface-code class decls are treated subtly
differently, which has given me a great deal of confusion over the years.
Here's the deal.  (We distinguish the two cases because source-code decls
have (Just binds) in the tcdMeths field, whereas interface decls have Nothing.

In *source-code* class declarations:

 - When parsing, every ClassOpSig gets a DefMeth with a suitable RdrName
   This is done by RdrHsSyn.mkClassOpSigDM

 - The renamer renames it to a Name

 - During typechecking, we generate a binding for each $dm for 
   which there's a programmer-supplied default method:
        class Foo a where
          op1 :: <type>
          op2 :: <type>
          op1 = ...
   We generate a binding for $dmop1 but not for $dmop2.
   The Class for Foo has a NoDefMeth for op2 and a DefMeth for op1.
   The Name for $dmop2 is simply discarded.

In *interface-file* class declarations:
  - When parsing, we see if there's an explicit programmer-supplied default method
    because there's an '=' sign to indicate it:
        class Foo a where
          op1 = :: <type>       -- NB the '='
          op2   :: <type>
    We use this info to generate a DefMeth with a suitable RdrName for op1,
    and a NoDefMeth for op2
  - The interface file has a separate definition for $dmop1, with unfolding etc.
  - The renamer renames it to a Name.
  - The renamer treats $dmop1 as a free variable of the declaration, so that
    the binding for $dmop1 will be sucked in.  (See RnHsSyn.tyClDeclFVs)  
    This doesn't happen for source code class decls, because they *bind* the default method.

Dictionary functions
~~~~~~~~~~~~~~~~~~~~
Each instance declaration gives rise to one dictionary function binding.

The type checker makes up new source-code instance declarations
(e.g. from 'deriving' or generic default methods --- see
TcInstDcls.tcInstDecls1).  So we can't generate the names for
dictionary functions in advance (we don't know how many we need).

On the other hand for interface-file instance declarations, the decl
specifies the name of the dictionary function, and it has a binding elsewhere
in the interface file:
        instance {Eq Int} = dEqInt
        dEqInt :: {Eq Int} <pragma info>

So again we treat source code and interface file code slightly differently.

Source code:
  - Source code instance decls have a Nothing in the (Maybe name) field
    (see data InstDecl below)

  - The typechecker makes up a Local name for the dict fun for any source-code
    instance decl, whether it comes from a source-code instance decl, or whether
    the instance decl is derived from some other construct (e.g. 'deriving').

  - The occurrence name it chooses is derived from the instance decl (just for 
    documentation really) --- e.g. dNumInt.  Two dict funs may share a common
    occurrence name, but will have different uniques.  E.g.
        instance Foo [Int]  where ...
        instance Foo [Bool] where ...
    These might both be dFooList

  - The CoreTidy phase externalises the name, and ensures the occurrence name is
    unique (this isn't special to dict funs).  So we'd get dFooList and dFooList1.

  - We can take this relaxed approach (changing the occurrence name later) 
    because dict fun Ids are not captured in a TyCon or Class (unlike default
    methods, say).  Instead, they are kept separately in the InstEnv.  This
    makes it easy to adjust them after compiling a module.  (Once we've finished
    compiling that module, they don't change any more.)


Interface file code:
  - The instance decl gives the dict fun name, so the InstDecl has a (Just name)
    in the (Maybe name) field.

  - RnHsSyn.instDeclFVs treats the dict fun name as free in the decl, so that we
    suck in the dfun binding


\begin{code}
-- Representation of indexed types
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Family kind signatures are represented by the variant `TyFamily'.  It
-- covers "type family", "newtype family", and "data family" declarations,
-- distinguished by the value of the field `tcdFlavour'.
--
-- Indexed types are represented by 'TyData' and 'TySynonym' using the field
-- 'tcdTyPats::Maybe [LHsType name]', with the following meaning:
--
--   * If it is 'Nothing', we have a *vanilla* data type declaration or type
--     synonym declaration and 'tcdVars' contains the type parameters of the
--     type constructor.
--
--   * If it is 'Just pats', we have the definition of an indexed type.  Then,
--     'pats' are type patterns for the type-indexes of the type constructor
--     and 'tcdTyVars' are the variables in those patterns.  Hence, the arity of
--     the indexed type (ie, the number of indexes) is 'length tcdTyPats' and
--     *not* 'length tcdVars'.
--
-- In both cases, 'tcdVars' collects all variables we need to quantify over.

type LTyClDecl name = Located (TyClDecl name)
type TyClGroup name = [LTyClDecl name]  -- this is used in TcTyClsDecls to represent
                                        -- strongly connected components of decls

-- | A type or class declaration.
data TyClDecl name
  = ForeignType { 
                tcdLName    :: Located name,
                tcdExtName  :: Maybe FastString
    }


  | -- | @type/data family T :: *->*@
    TyFamily {  tcdFlavour:: FamilyFlavour,             -- type or data
                tcdLName  :: Located name,              -- type constructor
                tcdTyVars :: [LHsTyVarBndr name],       -- type variables
                tcdKind   :: Maybe (LHsKind name)       -- result kind
    }


  | -- | Declares a data type or newtype, giving its construcors
    -- @
    --  data/newtype T a = <constrs>
    --  data/newtype instance T [a] = <constrs>
    -- @
    TyData {    tcdND     :: NewOrData,
                tcdCtxt   :: LHsContext name,           -- ^ Context
                tcdLName  :: Located name,              -- ^ Type constructor

                tcdTyVars :: [LHsTyVarBndr name],       -- ^ Type variables
                tcdTyPats :: Maybe [LHsType name],      -- ^ Type patterns.
                  -- See Note [tcdTyVars and tcdTyPats] 

                tcdKindSig:: Maybe (LHsKind name),
                        -- ^ Optional kind signature.
                        --
                        -- @(Just k)@ for a GADT-style @data@, or @data
                        -- instance@ decl with explicit kind sig

                tcdCons   :: [LConDecl name],
                        -- ^ Data constructors
                        --
                        -- For @data T a = T1 | T2 a@
                        --   the 'LConDecl's all have 'ResTyH98'.
                        -- For @data T a where { T1 :: T a }@
                        --   the 'LConDecls' all have 'ResTyGADT'.

                tcdDerivs :: Maybe [LHsType name]
                        -- ^ Derivings; @Nothing@ => not specified,
                        --              @Just []@ => derive exactly what is asked
                        --
                        -- These "types" must be of form
                        -- @
                        --      forall ab. C ty1 ty2
                        -- @
                        -- Typically the foralls and ty args are empty, but they
                        -- are non-empty for the newtype-deriving case
    }

  | TySynonym { tcdLName  :: Located name,              -- ^ type constructor
                tcdTyVars :: [LHsTyVarBndr name],       -- ^ type variables
                tcdTyPats :: Maybe [LHsType name],      -- ^ Type patterns
                  -- See Note [tcdTyVars and tcdTyPats] 

                tcdSynRhs :: LHsType name               -- ^ synonym expansion
    }

  | ClassDecl { tcdCtxt    :: LHsContext name,          -- ^ Context...
                tcdLName   :: Located name,             -- ^ Name of the class
                tcdTyVars  :: [LHsTyVarBndr name],      -- ^ Class type variables
                tcdFDs     :: [Located (FunDep name)],  -- ^ Functional deps
                tcdSigs    :: [LSig name],              -- ^ Methods' signatures
                tcdMeths   :: LHsBinds name,            -- ^ Default methods
                tcdATs     :: [LTyClDecl name],         -- ^ Associated types; ie
                                                        --   only 'TyFamily'
                tcdATDefs  :: [LTyClDecl name],         -- ^ Associated type defaults; ie
                                                        --   only 'TySynonym'
                tcdDocs    :: [LDocDecl]                -- ^ Haddock docs
    }
  deriving (Data, Typeable)

data NewOrData
  = NewType                     -- ^ @newtype Blah ...@
  | DataType                    -- ^ @data Blah ...@
  deriving( Eq, Data, Typeable )                -- Needed because Demand derives Eq

data FamilyFlavour
  = TypeFamily                  -- ^ @type family ...@
  | DataFamily                  -- ^ @data family ...@
  deriving (Data, Typeable)
\end{code}

Note [tcdTyVars and tcdTyPats] 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We use TyData and TySynonym both for vanilla data/type declarations
     type T a = Int
AND for data/type family instance declarations
     type instance F [a] = (a,Int)

tcdTyPats = Nothing
   This is a vanilla data type or type synonym
   tcdTyVars are the quantified type variables

tcdTyPats = Just tys
   This is a data/type family instance declaration
   tcdTyVars are fv(tys)

   Eg   class C s t where
          type F t p :: *
        instance C w (a,b) where
          type F (a,b) x = x->a
   The tcdTyVars of the F decl are {a,b,x}, even though the F decl
   is nested inside the 'instance' decl. 

   However after the renamer, the uniques will match up:
        instance C w7 (a8,b9) where
          type F (a8,b9) x10 = x10->a8
   so that we can compare the type patter in the 'instance' decl and
   in the associated 'type' decl

------------------------------
Simple classifiers

\begin{code}
-- | @True@ <=> argument is a @data@\/@newtype@ or @data@\/@newtype instance@
-- declaration.
isDataDecl :: TyClDecl name -> Bool
isDataDecl (TyData {}) = True
isDataDecl _other      = False

-- | type or type instance declaration
isTypeDecl :: TyClDecl name -> Bool
isTypeDecl (TySynonym {}) = True
isTypeDecl _other         = False

-- | vanilla Haskell type synonym (ie, not a type instance)
isSynDecl :: TyClDecl name -> Bool
isSynDecl (TySynonym {tcdTyPats = Nothing}) = True
isSynDecl _other                            = False

-- | type class
isClassDecl :: TyClDecl name -> Bool
isClassDecl (ClassDecl {}) = True
isClassDecl _              = False

-- | type family declaration
isFamilyDecl :: TyClDecl name -> Bool
isFamilyDecl (TyFamily {}) = True
isFamilyDecl _other        = False

-- | family instance (types, newtypes, and data types)
isFamInstDecl :: TyClDecl name -> Bool
isFamInstDecl tydecl
   | isTypeDecl tydecl
     || isDataDecl tydecl = isJust (tcdTyPats tydecl)
   | otherwise            = False
\end{code}

Dealing with names

\begin{code}
tcdName :: TyClDecl name -> name
tcdName decl = unLoc (tcdLName decl)

tyClDeclTyVars :: TyClDecl name -> [LHsTyVarBndr name]
tyClDeclTyVars (TyFamily    {tcdTyVars = tvs}) = tvs
tyClDeclTyVars (TySynonym   {tcdTyVars = tvs}) = tvs
tyClDeclTyVars (TyData      {tcdTyVars = tvs}) = tvs
tyClDeclTyVars (ClassDecl   {tcdTyVars = tvs}) = tvs
tyClDeclTyVars (ForeignType {})                = []
\end{code}

\begin{code}
countTyClDecls :: [TyClDecl name] -> (Int, Int, Int, Int, Int, Int)
        -- class, synonym decls, data, newtype, family decls, family instances
countTyClDecls decls 
 = (count isClassDecl    decls,
    count isSynDecl      decls,  -- excluding...
    count isDataTy       decls,  -- ...family...
    count isNewTy        decls,  -- ...instances
    count isFamilyDecl   decls,
    count isFamInstDecl  decls)
 where
   isDataTy TyData{tcdND = DataType, tcdTyPats = Nothing} = True
   isDataTy _                                             = False
   
   isNewTy TyData{tcdND = NewType, tcdTyPats = Nothing} = True
   isNewTy _                                            = False
\end{code}

\begin{code}
instance OutputableBndr name
              => Outputable (TyClDecl name) where

    ppr (ForeignType {tcdLName = ltycon})
        = hsep [ptext (sLit "foreign import type dotnet"), ppr ltycon]

    ppr (TyFamily {tcdFlavour = flavour, tcdLName = ltycon, 
                   tcdTyVars = tyvars, tcdKind = mb_kind})
      = pp_flavour <+> pp_decl_head [] ltycon tyvars Nothing <+> pp_kind
        where
          pp_flavour = case flavour of
                         TypeFamily -> ptext (sLit "type family")
                         DataFamily -> ptext (sLit "data family")

          pp_kind = case mb_kind of
                      Nothing   -> empty
                      Just kind -> dcolon <+> ppr kind

    ppr (TySynonym {tcdLName = ltycon, tcdTyVars = tyvars, tcdTyPats = typats,
                    tcdSynRhs = mono_ty})
      = hang (ptext (sLit "type") <+> 
              (if isJust typats then ptext (sLit "instance") else empty) <+>
              pp_decl_head [] ltycon tyvars typats <+> 
              equals)
             4 (ppr mono_ty)

    ppr (TyData {tcdND = new_or_data, tcdCtxt = context, tcdLName = ltycon,
                 tcdTyVars = tyvars, tcdTyPats = typats, tcdKindSig = mb_sig, 
                 tcdCons = condecls, tcdDerivs = derivings})
      = pp_tydecl (null condecls && isJust mb_sig) 
                  (ppr new_or_data <+> 
                   (if isJust typats then ptext (sLit "instance") else empty) <+>
                   pp_decl_head (unLoc context) ltycon tyvars typats <+> 
                   ppr_sigx mb_sig)
                  (pp_condecls condecls)
                  derivings
      where
        ppr_sigx Nothing     = empty
        ppr_sigx (Just kind) = dcolon <+> ppr kind

    ppr (ClassDecl {tcdCtxt = context, tcdLName = lclas, tcdTyVars = tyvars, 
                    tcdFDs  = fds,
                    tcdSigs = sigs, tcdMeths = methods,
                    tcdATs = ats, tcdATDefs = at_defs})
      | null sigs && isEmptyBag methods && null ats && null at_defs -- No "where" part
      = top_matter

      | otherwise       -- Laid out
      = vcat [ top_matter <+> ptext (sLit "where")
             , nest 2 $ pprDeclList (map ppr ats ++
                                     map ppr at_defs ++
                                     pprLHsBindsForUser methods sigs) ]
      where
        top_matter = ptext (sLit "class") 
                     <+> pp_decl_head (unLoc context) lclas tyvars Nothing
                     <+> pprFundeps (map unLoc fds)

pp_decl_head :: OutputableBndr name
   => HsContext name
   -> Located name
   -> [LHsTyVarBndr name]
   -> Maybe [LHsType name]
   -> SDoc
pp_decl_head context thing tyvars Nothing       -- no explicit type patterns
  = hsep [pprHsContext context, ppr thing, interppSP tyvars]
pp_decl_head context thing _      (Just typats) -- explicit type patterns
  = hsep [ pprHsContext context, ppr thing
         , hsep (map (pprParendHsType.unLoc) typats)]

pp_condecls :: OutputableBndr name => [LConDecl name] -> SDoc
pp_condecls cs@(L _ ConDecl{ con_res = ResTyGADT _ } : _) -- In GADT syntax
  = hang (ptext (sLit "where")) 2 (vcat (map ppr cs))
pp_condecls cs                    -- In H98 syntax
  = equals <+> sep (punctuate (ptext (sLit " |")) (map ppr cs))

pp_tydecl :: OutputableBndr name => Bool -> SDoc -> SDoc -> Maybe [LHsType name] -> SDoc
pp_tydecl True  pp_head _ _
  = pp_head
pp_tydecl False pp_head pp_decl_rhs derivings
  = hang pp_head 4 (sep [
      pp_decl_rhs,
      case derivings of
        Nothing -> empty
        Just ds -> hsep [ptext (sLit "deriving"), parens (interpp'SP ds)]
    ])

instance Outputable NewOrData where
  ppr NewType  = ptext (sLit "newtype")
  ppr DataType = ptext (sLit "data")
\end{code}


%************************************************************************
%*                                                                      *
\subsection[ConDecl]{A data-constructor declaration}
%*                                                                      *
%************************************************************************

\begin{code}
type LConDecl name = Located (ConDecl name)

-- data T b = forall a. Eq a => MkT a b
--   MkT :: forall b a. Eq a => MkT a b

-- data T b where
--      MkT1 :: Int -> T Int

-- data T = Int `MkT` Int
--        | MkT2

-- data T a where
--      Int `MkT` Int :: T Int

data ConDecl name
  = ConDecl
    { con_name      :: Located name
        -- ^ Constructor name.  This is used for the DataCon itself, and for
        -- the user-callable wrapper Id.

    , con_explicit  :: HsExplicitFlag
        -- ^ Is there an user-written forall? (cf. 'HsTypes.HsForAllTy')

    , con_qvars     :: [LHsTyVarBndr name]
        -- ^ Type variables.  Depending on 'con_res' this describes the
        -- following entities
        --
        --  - ResTyH98:  the constructor's *existential* type variables
        --  - ResTyGADT: *all* the constructor's quantified type variables
        --
        -- If con_explicit is Implicit, then con_qvars is irrelevant
        -- until after renaming.  

    , con_cxt       :: LHsContext name
        -- ^ The context.  This /does not/ include the \"stupid theta\" which
        -- lives only in the 'TyData' decl.

    , con_details   :: HsConDeclDetails name
        -- ^ The main payload

    , con_res       :: ResType name
        -- ^ Result type of the constructor

    , con_doc       :: Maybe LHsDocString
        -- ^ A possible Haddock comment.

    , con_old_rec :: Bool   
        -- ^ TEMPORARY field; True <=> user has employed now-deprecated syntax for
        --                             GADT-style record decl   C { blah } :: T a b
        -- Remove this when we no longer parse this stuff, and hence do not
        -- need to report decprecated use
    } deriving (Data, Typeable)

type HsConDeclDetails name = HsConDetails (LBangType name) [ConDeclField name]

hsConDeclArgTys :: HsConDeclDetails name -> [LBangType name]
hsConDeclArgTys (PrefixCon tys)    = tys
hsConDeclArgTys (InfixCon ty1 ty2) = [ty1,ty2]
hsConDeclArgTys (RecCon flds)      = map cd_fld_type flds

data ResType name
   = ResTyH98           -- Constructor was declared using Haskell 98 syntax
   | ResTyGADT (LHsType name)   -- Constructor was declared using GADT-style syntax,
                                --      and here is its result type
   deriving (Data, Typeable)

instance OutputableBndr name => Outputable (ResType name) where
         -- Debugging only
   ppr ResTyH98 = ptext (sLit "ResTyH98")
   ppr (ResTyGADT ty) = ptext (sLit "ResTyGADT") <+> pprParendHsType (unLoc ty)
\end{code}


\begin{code}
instance (OutputableBndr name) => Outputable (ConDecl name) where
    ppr = pprConDecl

pprConDecl :: OutputableBndr name => ConDecl name -> SDoc
pprConDecl (ConDecl { con_name = con, con_explicit = expl, con_qvars = tvs
                    , con_cxt = cxt, con_details = details
                    , con_res = ResTyH98, con_doc = doc })
  = sep [ppr_mbDoc doc, pprHsForAll expl tvs cxt, ppr_details details]
  where
    ppr_details (InfixCon t1 t2) = hsep [ppr t1, pprHsInfix con, ppr t2]
    ppr_details (PrefixCon tys)  = hsep (pprHsVar con : map ppr tys)
    ppr_details (RecCon fields)  = ppr con <+> pprConDeclFields fields

pprConDecl (ConDecl { con_name = con, con_explicit = expl, con_qvars = tvs
                    , con_cxt = cxt, con_details = PrefixCon arg_tys
                    , con_res = ResTyGADT res_ty })
  = ppr con <+> dcolon <+> 
    sep [pprHsForAll expl tvs cxt, ppr (foldr mk_fun_ty res_ty arg_tys)]
  where
    mk_fun_ty a b = noLoc (HsFunTy a b)

pprConDecl (ConDecl { con_name = con, con_explicit = expl, con_qvars = tvs
                    , con_cxt = cxt, con_details = RecCon fields, con_res = ResTyGADT res_ty })
  = sep [ppr con <+> dcolon <+> pprHsForAll expl tvs cxt, 
         pprConDeclFields fields <+> arrow <+> ppr res_ty]

pprConDecl (ConDecl {con_name = con, con_details = InfixCon {}, con_res = ResTyGADT {} })
  = pprPanic "pprConDecl" (ppr con)
        -- In GADT syntax we don't allow infix constructors
\end{code}

%************************************************************************
%*                                                                      *
\subsection[InstDecl]{An instance declaration}
%*                                                                      *
%************************************************************************

\begin{code}
type LInstDecl name = Located (InstDecl name)

data InstDecl name
  = InstDecl    (LHsType name)  -- Context => Class Instance-type
                                -- Using a polytype means that the renamer conveniently
                                -- figures out the quantified type variables for us.
                (LHsBinds name)
                [LSig name]     -- User-supplied pragmatic info
                [LTyClDecl name]-- Associated types (ie, 'TyData' and
                                -- 'TySynonym' only)
  deriving (Data, Typeable)

instance (OutputableBndr name) => Outputable (InstDecl name) where
    ppr (InstDecl inst_ty binds sigs ats)
      | null sigs && null ats && isEmptyBag binds  -- No "where" part
      = top_matter

      | otherwise       -- Laid out
      = vcat [ top_matter <+> ptext (sLit "where")
             , nest 2 $ pprDeclList (map ppr ats ++
                                     pprLHsBindsForUser binds sigs) ]
      where
        top_matter = ptext (sLit "instance") <+> ppr inst_ty

-- Extract the declarations of associated types from an instance
--
instDeclATs :: [LInstDecl name] -> [LTyClDecl name]
instDeclATs inst_decls = [at | L _ (InstDecl _ _ _ ats) <- inst_decls, at <- ats]
\end{code}

%************************************************************************
%*                                                                      *
\subsection[DerivDecl]{A stand-alone instance deriving declaration}
%*                                                                      *
%************************************************************************

\begin{code}
type LDerivDecl name = Located (DerivDecl name)

data DerivDecl name = DerivDecl { deriv_type :: LHsType name }
  deriving (Data, Typeable)

instance (OutputableBndr name) => Outputable (DerivDecl name) where
    ppr (DerivDecl ty) 
        = hsep [ptext (sLit "deriving instance"), ppr ty]
\end{code}

%************************************************************************
%*                                                                      *
\subsection[DefaultDecl]{A @default@ declaration}
%*                                                                      *
%************************************************************************

There can only be one default declaration per module, but it is hard
for the parser to check that; we pass them all through in the abstract
syntax, and that restriction must be checked in the front end.

\begin{code}
type LDefaultDecl name = Located (DefaultDecl name)

data DefaultDecl name
  = DefaultDecl [LHsType name]
  deriving (Data, Typeable)

instance (OutputableBndr name)
              => Outputable (DefaultDecl name) where

    ppr (DefaultDecl tys)
      = ptext (sLit "default") <+> parens (interpp'SP tys)
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Foreign function interface declaration}
%*                                                                      *
%************************************************************************

\begin{code}

-- foreign declarations are distinguished as to whether they define or use a
-- Haskell name
--
--  * the Boolean value indicates whether the pre-standard deprecated syntax
--   has been used
--
type LForeignDecl name = Located (ForeignDecl name)

data ForeignDecl name
  = ForeignImport (Located name) -- defines this name
                  (LHsType name) -- sig_ty
                  Coercion       -- rep_ty ~ sig_ty
                  ForeignImport
  | ForeignExport (Located name) -- uses this name
                  (LHsType name) -- sig_ty
                  Coercion       -- sig_ty ~ rep_ty
                  ForeignExport
  deriving (Data, Typeable)
{-
    In both ForeignImport and ForeignExport:
        sig_ty is the type given in the Haskell code
        rep_ty is the representation for this type, i.e. with newtypes
               coerced away and type functions evaluated.
    Thus if the declaration is valid, then rep_ty will only use types
    such as Int and IO that we know how to make foreign calls with.
-}

noForeignImportCoercionYet :: Coercion
noForeignImportCoercionYet
    = panic "ForeignImport coercion evaluated before typechecking"

noForeignExportCoercionYet :: Coercion
noForeignExportCoercionYet
    = panic "ForeignExport coercion evaluated before typechecking"

-- Specification Of an imported external entity in dependence on the calling
-- convention 
--
data ForeignImport = -- import of a C entity
                     --
                     --  * the two strings specifying a header file or library
                     --   may be empty, which indicates the absence of a
                     --   header or object specification (both are not used
                     --   in the case of `CWrapper' and when `CFunction'
                     --   has a dynamic target)
                     --
                     --  * the calling convention is irrelevant for code
                     --   generation in the case of `CLabel', but is needed
                     --   for pretty printing 
                     --
                     --  * `Safety' is irrelevant for `CLabel' and `CWrapper'
                     --
                     CImport  CCallConv       -- ccall or stdcall
                              Safety          -- interruptible, safe or unsafe
                              FastString      -- name of C header
                              CImportSpec     -- details of the C entity
  deriving (Data, Typeable)

-- details of an external C entity
--
data CImportSpec = CLabel    CLabelString     -- import address of a C label
                 | CFunction CCallTarget      -- static or dynamic function
                 | CWrapper                   -- wrapper to expose closures
                                              -- (former f.e.d.)
  deriving (Data, Typeable)

-- specification of an externally exported entity in dependence on the calling
-- convention
--
data ForeignExport = CExport  CExportSpec    -- contains the calling convention
  deriving (Data, Typeable)

-- pretty printing of foreign declarations
--

instance OutputableBndr name => Outputable (ForeignDecl name) where
  ppr (ForeignImport n ty _ fimport) =
    hang (ptext (sLit "foreign import") <+> ppr fimport <+> ppr n)
       2 (dcolon <+> ppr ty)
  ppr (ForeignExport n ty _ fexport) =
    hang (ptext (sLit "foreign export") <+> ppr fexport <+> ppr n)
       2 (dcolon <+> ppr ty)

instance Outputable ForeignImport where
  ppr (CImport  cconv safety header spec) =
    ppr cconv <+> ppr safety <+> 
    char '"' <> pprCEntity spec <> char '"'
    where
      pp_hdr = if nullFS header then empty else ftext header

      pprCEntity (CLabel lbl) = 
        ptext (sLit "static") <+> pp_hdr <+> char '&' <> ppr lbl
      pprCEntity (CFunction (StaticTarget lbl _)) = 
        ptext (sLit "static") <+> pp_hdr <+> ppr lbl
      pprCEntity (CFunction (DynamicTarget)) =
        ptext (sLit "dynamic")
      pprCEntity (CWrapper) = ptext (sLit "wrapper")

instance Outputable ForeignExport where
  ppr (CExport  (CExportStatic lbl cconv)) = 
    ppr cconv <+> char '"' <> ppr lbl <> char '"'
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Transformation rules}
%*                                                                      *
%************************************************************************

\begin{code}
type LRuleDecl name = Located (RuleDecl name)

data RuleDecl name
  = HsRule                      -- Source rule
        RuleName                -- Rule name
        Activation
        [RuleBndr name]         -- Forall'd vars; after typechecking this includes tyvars
        (Located (HsExpr name)) -- LHS
        NameSet                 -- Free-vars from the LHS
        (Located (HsExpr name)) -- RHS
        NameSet                 -- Free-vars from the RHS
  deriving (Data, Typeable)

data RuleBndr name
  = RuleBndr (Located name)
  | RuleBndrSig (Located name) (LHsType name)
  deriving (Data, Typeable)

collectRuleBndrSigTys :: [RuleBndr name] -> [LHsType name]
collectRuleBndrSigTys bndrs = [ty | RuleBndrSig _ ty <- bndrs]

instance OutputableBndr name => Outputable (RuleDecl name) where
  ppr (HsRule name act ns lhs _fv_lhs rhs _fv_rhs)
        = sep [text "{-# RULES" <+> doubleQuotes (ftext name) <+> ppr act,
               nest 4 (pp_forall <+> pprExpr (unLoc lhs)), 
               nest 4 (equals <+> pprExpr (unLoc rhs) <+> text "#-}") ]
        where
          pp_forall | null ns   = empty
                    | otherwise = text "forall" <+> fsep (map ppr ns) <> dot

instance OutputableBndr name => Outputable (RuleBndr name) where
   ppr (RuleBndr name) = ppr name
   ppr (RuleBndrSig name ty) = ppr name <> dcolon <> ppr ty
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Vectorisation declarations}
%*                                                                      *
%************************************************************************

A vectorisation pragma, one of

  {-# VECTORISE f = closure1 g (scalar_map g) #-}
  {-# VECTORISE SCALAR f #-}
  {-# NOVECTORISE f #-}

  {-# VECTORISE type T = ty #-}
  {-# VECTORISE SCALAR type T #-}
  
\begin{code}
type LVectDecl name = Located (VectDecl name)

data VectDecl name
  = HsVect
      (Located name)
      (Maybe (LHsExpr name))    -- 'Nothing' => SCALAR declaration
  | HsNoVect
      (Located name)
  | HsVectTypeIn                -- pre type-checking
      Bool                      -- 'TRUE' => SCALAR declaration
      (Located name)
      (Maybe (Located name))    -- 'Nothing' => no right-hand side
  | HsVectTypeOut               -- post type-checking
      Bool                      -- 'TRUE' => SCALAR declaration
      TyCon
      (Maybe TyCon)             -- 'Nothing' => no right-hand side
  | HsVectClassIn               -- pre type-checking
      (Located name)
  | HsVectClassOut              -- post type-checking
      Class
  | HsVectInstIn                -- pre type-checking (always SCALAR)
      (LHsType name)
  | HsVectInstOut               -- post type-checking (always SCALAR)
      Instance
  deriving (Data, Typeable)

lvectDeclName :: NamedThing name => LVectDecl name -> Name
lvectDeclName (L _ (HsVect         (L _ name) _))   = getName name
lvectDeclName (L _ (HsNoVect       (L _ name)))     = getName name
lvectDeclName (L _ (HsVectTypeIn   _ (L _ name) _)) = getName name
lvectDeclName (L _ (HsVectTypeOut  _ tycon _))      = getName tycon
lvectDeclName (L _ (HsVectClassIn  (L _ name)))     = getName name
lvectDeclName (L _ (HsVectClassOut cls))            = getName cls
lvectDeclName (L _ (HsVectInstIn   _))              = panic "HsDecls.lvectDeclName: HsVectInstIn"
lvectDeclName (L _ (HsVectInstOut  _))              = panic "HsDecls.lvectDeclName: HsVectInstOut"

lvectInstDecl :: LVectDecl name -> Bool
lvectInstDecl (L _ (HsVectInstIn _))  = True
lvectInstDecl (L _ (HsVectInstOut _)) = True
lvectInstDecl _                       = False

instance OutputableBndr name => Outputable (VectDecl name) where
  ppr (HsVect v Nothing)
    = sep [text "{-# VECTORISE SCALAR" <+> ppr v <+> text "#-}" ]
  ppr (HsVect v (Just rhs))
    = sep [text "{-# VECTORISE" <+> ppr v,
           nest 4 $ 
             pprExpr (unLoc rhs) <+> text "#-}" ]
  ppr (HsNoVect v)
    = sep [text "{-# NOVECTORISE" <+> ppr v <+> text "#-}" ]
  ppr (HsVectTypeIn False t Nothing)
    = sep [text "{-# VECTORISE type" <+> ppr t <+> text "#-}" ]
  ppr (HsVectTypeIn False t (Just t'))
    = sep [text "{-# VECTORISE type" <+> ppr t, text "=", ppr t', text "#-}" ]
  ppr (HsVectTypeIn True t Nothing)
    = sep [text "{-# VECTORISE SCALAR type" <+> ppr t <+> text "#-}" ]
  ppr (HsVectTypeIn True t (Just t'))
    = sep [text "{-# VECTORISE SCALAR type" <+> ppr t, text "=", ppr t', text "#-}" ]
  ppr (HsVectTypeOut False t Nothing)
    = sep [text "{-# VECTORISE type" <+> ppr t <+> text "#-}" ]
  ppr (HsVectTypeOut False t (Just t'))
    = sep [text "{-# VECTORISE type" <+> ppr t, text "=", ppr t', text "#-}" ]
  ppr (HsVectTypeOut True t Nothing)
    = sep [text "{-# VECTORISE SCALAR type" <+> ppr t <+> text "#-}" ]
  ppr (HsVectTypeOut True t (Just t'))
    = sep [text "{-# VECTORISE SCALAR type" <+> ppr t, text "=", ppr t', text "#-}" ]
  ppr (HsVectClassIn c)
    = sep [text "{-# VECTORISE class" <+> ppr c <+> text "#-}" ]
  ppr (HsVectClassOut c)
    = sep [text "{-# VECTORISE class" <+> ppr c <+> text "#-}" ]
  ppr (HsVectInstIn ty)
    = sep [text "{-# VECTORISE SCALAR instance" <+> ppr ty <+> text "#-}" ]
  ppr (HsVectInstOut i)
    = sep [text "{-# VECTORISE SCALAR instance" <+> ppr i <+> text "#-}" ]
\end{code}

%************************************************************************
%*                                                                      *
\subsection[DocDecl]{Document comments}
%*                                                                      *
%************************************************************************

\begin{code}

type LDocDecl = Located (DocDecl)

data DocDecl
  = DocCommentNext HsDocString
  | DocCommentPrev HsDocString
  | DocCommentNamed String HsDocString
  | DocGroup Int HsDocString
  deriving (Data, Typeable)
 
-- Okay, I need to reconstruct the document comments, but for now:
instance Outputable DocDecl where
  ppr _ = text "<document comment>"

docDeclDoc :: DocDecl -> HsDocString
docDeclDoc (DocCommentNext d) = d
docDeclDoc (DocCommentPrev d) = d
docDeclDoc (DocCommentNamed _ d) = d
docDeclDoc (DocGroup _ d) = d

\end{code}

%************************************************************************
%*                                                                      *
\subsection[DeprecDecl]{Deprecations}
%*                                                                      *
%************************************************************************

We use exported entities for things to deprecate.

\begin{code}
type LWarnDecl name = Located (WarnDecl name)

data WarnDecl name = Warning name WarningTxt
  deriving (Data, Typeable)

instance OutputableBndr name => Outputable (WarnDecl name) where
    ppr (Warning thing txt)
      = hsep [text "{-# DEPRECATED", ppr thing, doubleQuotes (ppr txt), text "#-}"]
\end{code}

%************************************************************************
%*                                                                      *
\subsection[AnnDecl]{Annotations}
%*                                                                      *
%************************************************************************

\begin{code}
type LAnnDecl name = Located (AnnDecl name)

data AnnDecl name = HsAnnotation (AnnProvenance name) (Located (HsExpr name))
  deriving (Data, Typeable)

instance (OutputableBndr name) => Outputable (AnnDecl name) where
    ppr (HsAnnotation provenance expr) 
      = hsep [text "{-#", pprAnnProvenance provenance, pprExpr (unLoc expr), text "#-}"]


data AnnProvenance name = ValueAnnProvenance name
                        | TypeAnnProvenance name
                        | ModuleAnnProvenance
  deriving (Data, Typeable)

annProvenanceName_maybe :: AnnProvenance name -> Maybe name
annProvenanceName_maybe (ValueAnnProvenance name) = Just name
annProvenanceName_maybe (TypeAnnProvenance name)  = Just name
annProvenanceName_maybe ModuleAnnProvenance       = Nothing

-- TODO: Replace with Traversable instance when GHC bootstrap version rises high enough
modifyAnnProvenanceNameM :: Monad m => (before -> m after) -> AnnProvenance before -> m (AnnProvenance after)
modifyAnnProvenanceNameM fm prov =
    case prov of
            ValueAnnProvenance name -> liftM ValueAnnProvenance (fm name)
            TypeAnnProvenance name -> liftM TypeAnnProvenance (fm name)
            ModuleAnnProvenance -> return ModuleAnnProvenance

pprAnnProvenance :: OutputableBndr name => AnnProvenance name -> SDoc
pprAnnProvenance ModuleAnnProvenance       = ptext (sLit "ANN module")
pprAnnProvenance (ValueAnnProvenance name) = ptext (sLit "ANN") <+> ppr name
pprAnnProvenance (TypeAnnProvenance name)  = ptext (sLit "ANN type") <+> ppr name
\end{code}
