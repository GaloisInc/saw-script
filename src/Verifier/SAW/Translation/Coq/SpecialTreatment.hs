{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Translation.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq.SpecialTreatment where

import           Control.Lens                       (_1, _2, over)
import           Control.Monad.Reader               (ask)
import qualified Data.Map                           as Map
import           Data.String.Interpolate            (i)
import           Prelude                            hiding (fail)
import qualified Data.Text as Text

import qualified Language.Coq.AST                   as Coq
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Translation.Coq.Monad
import           Verifier.SAW.Term.Functor

data SpecialTreatment = SpecialTreatment
  { moduleRenaming        :: Map.Map ModuleName String
  , identSpecialTreatment :: Map.Map ModuleName (Map.Map String IdentSpecialTreatment)
  }

data DefSiteTreatment
  = DefPreserve
  | DefRename   (Maybe ModuleName) String -- optional module rename, then identifier itself
  | DefReplace  String
  | DefSkip

data UseSiteTreatment
  = UsePreserve
  | UseRename   (Maybe ModuleName) String
  | UseReplaceDropArgs  Int Coq.Term

data IdentSpecialTreatment = IdentSpecialTreatment
  { atDefSite :: DefSiteTreatment
  , atUseSite :: UseSiteTreatment
  }

moduleRenamingMap :: Map.Map ModuleName ModuleName
moduleRenamingMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  over _2 (mkModuleName . (: [])) <$>
  [ ("Cryptol", "CryptolPrimitives")
  , ("Prelude", "SAWCorePrelude")
  ]

translateModuleName :: ModuleName -> ModuleName
translateModuleName mn =
  Map.findWithDefault mn mn moduleRenamingMap

findSpecialTreatment ::
  TranslationConfigurationMonad m =>
  Ident -> m IdentSpecialTreatment
findSpecialTreatment ident = do
  configuration <- ask
  let moduleMap =
        Map.findWithDefault Map.empty (identModule ident) (specialTreatmentMap configuration)
  let defaultTreatment =
        IdentSpecialTreatment
        { atDefSite = DefPreserve
        , atUseSite = UsePreserve
        }
  pure $ Map.findWithDefault defaultTreatment (identName ident) moduleMap

-- Use `mapsTo` for identifiers whose definition has a matching definition
-- already on the Coq side.  As such, their definition can be skipped, and use
-- sites can be replaced by the appropriate call.
mapsTo :: ModuleName -> String -> IdentSpecialTreatment
mapsTo targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName
  }

-- Use `realize` for axioms that can be realized, or for primitives that must be
-- realized.  While some primitives can be written directly in a standalone Coq
-- module, some primitives depend on code from the extracted module, and are
-- depended upon by following code in the same module.  Such primitives can
-- therefore *neither* be defined a priori, *nor* a posteriori, and must be
-- realized where they were originally declared.
realize :: String -> IdentSpecialTreatment
realize code = IdentSpecialTreatment
  { atDefSite = DefReplace code
  , atUseSite = UsePreserve
  }

-- Use `rename` for identifiers whose definition can be translated, but has to
-- be renamed.  This is useful for certain definitions whose name on the
-- SAWCore/Cryptol side clashes with names on the Coq side.  For instance, `at`
-- is a reserved Coq keyword, but is used as a function name in SAWCore Prelude.
-- Also useful for translation notations, until they are better supported.
rename :: String -> IdentSpecialTreatment
rename ident = IdentSpecialTreatment
  { atDefSite = DefRename Nothing ident
  , atUseSite = UseRename Nothing ident
  }

-- Replace any occurrences of identifier applied to @n@ arguments with the
-- supplied Coq term. If @n=0@ and the supplied Coq term is an identifier then
-- this is the same as 'rename'.
replaceDropArgs :: Int -> Coq.Term -> IdentSpecialTreatment
replaceDropArgs n term = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseReplaceDropArgs n term
  }

-- A version of 'replaceDropArgs' that drops no arguments; i.e., just replaces
-- an identifier with the supplied Coq term
replace :: Coq.Term -> IdentSpecialTreatment
replace = replaceDropArgs 0


-- Use `skip` for identifiers that are already defined in the appropriate module
-- on the Coq side.
skip :: IdentSpecialTreatment
skip = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UsePreserve
  }

sawDefinitionsModule :: ModuleName
sawDefinitionsModule = mkModuleName ["SAWCoreScaffolding"]

compMModule :: ModuleName
compMModule = mkModuleName ["CompM"]

sawVectorDefinitionsModule :: TranslationConfiguration -> ModuleName
sawVectorDefinitionsModule (TranslationConfiguration {..}) =
  mkModuleName [vectorModule]

cryptolPrimitivesModule :: ModuleName
cryptolPrimitivesModule = mkModuleName ["CryptolPrimitives"]

sawCoreScaffoldingModule :: ModuleName
sawCoreScaffoldingModule = mkModuleName ["SAWCoreScaffolding"]

cryptolPreludeSpecialTreatmentMap :: Map.Map String IdentSpecialTreatment
cryptolPreludeSpecialTreatmentMap = Map.fromList $ []

  ++
  [ ("Num_rec",               mapsTo cryptolPrimitivesModule "Num_rect") -- automatically defined
  , ("unsafeAssert_same_Num", skip) -- unsafe and unused
  ]

specialTreatmentMap :: TranslationConfiguration -> Map.Map ModuleName (Map.Map String IdentSpecialTreatment)
specialTreatmentMap configuration = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  [ ("Cryptol", cryptolPreludeSpecialTreatmentMap)
  , ("Prelude", sawCorePreludeSpecialTreatmentMap configuration)
  ]

-- NOTE: while I initially did the mapping from SAW core names to the
-- corresponding Coq construct here, it makes the job of translating SAW core
-- axioms into Coq theorems much more annoying, because one needs to manually
-- rename every constant mentioned in the statement to its Coq counterpart.
-- Instead, I am now trying to keep the names the same as much as possible
-- during this translation (it is sometimes impossible, for instance, `at` is a
-- reserved keyword in Coq), so that primitives' and axioms' types can be
-- copy-pasted as is on the Coq side.
sawCorePreludeSpecialTreatmentMap :: TranslationConfiguration -> Map.Map String IdentSpecialTreatment
sawCorePreludeSpecialTreatmentMap configuration =
  let vectorsModule = sawVectorDefinitionsModule configuration in
  Map.fromList $ []

  -- Unsafe SAW features
  ++
  [ ("error",             mapsTo sawDefinitionsModule "error")
  , ("fix",               skip)
  , ("unsafeAssert",      replaceDropArgs 3 $ Coq.Ltac "solveUnsafeAssert")
  , ("unsafeCoerce",      skip)
  , ("unsafeCoerce_same", skip)
  ]

  -- coercions
  ++
  [ ("coerce",      mapsTo sawDefinitionsModule "coerce")
  , ("coerce__def", skip)
  , ("coerce__eq",  skip)
  , ("rcoerce",     skip)
  ]

  -- Unit
  ++
  [ ("Unit",          mapsTo sawDefinitionsModule "Unit")
  , ("UnitType",      mapsTo sawDefinitionsModule "UnitType")
  , ("UnitType__rec", mapsTo sawDefinitionsModule "UnitType__rec")
  ]

  -- Records
  ++
  [ ("EmptyType",       skip)
  , ("EmptyType__rec",  skip)
  , ("RecordType",      skip)
  , ("RecordType__rec", skip)
  ]

  -- Decidable equality, does not make sense in Coq unless turned into a type
  -- class
  -- Apparently, this is not used much for Cryptol, so we can skip it.
  ++
  [ ("eq",            skip) -- MapsTo $ mkCoqIdent sawDefinitionsModule "eq")
  , ("eq_bitvector",  skip)
  , ("eq_Bool",       skip) -- MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "eq_Bool")
  , ("eq_Nat",        skip)
  , ("eq_refl",       skip) -- MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "eq_refl")
  , ("eq_VecBool",    skip)
  , ("eq_VecVec",     skip)
  , ("ite_eq_cong_1", skip)
  , ("ite_eq_cong_2", skip)
  ]

  -- Boolean
  ++
  [ ("and",           mapsTo sawDefinitionsModule "and")
  , ("and__eq",       mapsTo sawDefinitionsModule "and__eq")
  , ("Bool",          mapsTo sawDefinitionsModule "Bool")
  , ("boolEq",        mapsTo sawDefinitionsModule "boolEq")
  , ("boolEq__eq",    mapsTo sawDefinitionsModule "boolEq__eq")
  , ("False",         mapsTo sawDefinitionsModule "false")
  , ("ite",           mapsTo sawDefinitionsModule "ite")
  , ("iteDep",        mapsTo sawDefinitionsModule "iteDep")
  , ("iteDep_True",   mapsTo sawDefinitionsModule "iteDep_True")
  , ("iteDep_False",  mapsTo sawDefinitionsModule "iteDep_False")
  , ("ite_bit",       skip) -- FIXME: change this
  , ("ite_eq_iteDep", mapsTo sawDefinitionsModule "ite_eq_iteDep")
  , ("not",           mapsTo sawDefinitionsModule "not")
  , ("not__eq",       mapsTo sawDefinitionsModule "not__eq")
  , ("or",            mapsTo sawDefinitionsModule "or")
  , ("or__eq",        mapsTo sawDefinitionsModule "or__eq")
  , ("True",          mapsTo sawDefinitionsModule "true")
  , ("xor",           mapsTo sawDefinitionsModule "xor")
  , ("xor__eq",       mapsTo sawDefinitionsModule "xor__eq")
  ]

  -- Pairs
  ++
  [ ("PairType",  mapsTo sawDefinitionsModule "PairType")
  , ("PairValue", mapsTo sawDefinitionsModule "PairValue")
  , ("Pair__rec", mapsTo sawDefinitionsModule "Pair__rec")
  , ("fst",       mapsTo sawDefinitionsModule "fst")
  , ("snd",       mapsTo sawDefinitionsModule "snd")
  ]

  -- Equality
  ++
  [ ("Eq",      mapsTo sawDefinitionsModule "Eq")
  , ("Eq__rec", mapsTo sawDefinitionsModule "Eq__rec")
  , ("Refl",    mapsTo sawDefinitionsModule "Refl")
  , ("EqP",      mapsTo sawDefinitionsModule "EqP")
  , ("EqP__rec", mapsTo sawDefinitionsModule "EqP__rec")
  , ("ReflP",    mapsTo sawDefinitionsModule "ReflP")
  ]

  -- Strings
  ++
  [ ("String", mapsTo sawDefinitionsModule "String")
  , ("equalString", mapsTo sawDefinitionsModule "equalString")
  , ("appendString", mapsTo sawDefinitionsModule "appendString")
  ]

  -- Utility functions
  ++
  [ ("id", mapsTo sawDefinitionsModule "id")
  ]

  -- Natural numbers
  ++
  [ ("divModNat", mapsTo sawDefinitionsModule "divModNat")
  , ("Nat",       mapsTo sawDefinitionsModule "Nat")
  , ("widthNat",  mapsTo sawDefinitionsModule "widthNat")
  , ("Zero",      mapsTo sawCoreScaffoldingModule   "Zero")
  , ("Succ",      mapsTo sawCoreScaffoldingModule   "Succ")
  ]

  -- Vectors
  ++
  [ ("EmptyVec",      mapsTo vectorsModule "EmptyVec")
  , ("at",            rename "sawAt") -- `at` is a reserved keyword in Coq
  , ("atWithDefault", mapsTo vectorsModule "atWithDefault")
  , ("at_single",     skip) -- is boring, could be proved on the Coq side
  , ("bvAdd",         mapsTo vectorsModule "bvAdd")
  , ("bvLg2",         mapsTo vectorsModule "bvLg2")
  , ("bvMul",         mapsTo vectorsModule "bvMul")
  , ("bvNat",         mapsTo vectorsModule "bvNat")
  , ("bvNeg",         mapsTo vectorsModule "bvNeg")
  , ("bvSDiv",        mapsTo vectorsModule "bvSDiv")
  , ("bvSRem",        mapsTo vectorsModule "bvSRem")
  , ("bvSShr",        mapsTo vectorsModule "bvSShr")
  , ("bvSub",         mapsTo vectorsModule "bvSub")
  , ("bvToNat",       mapsTo vectorsModule "bvToNat")
  , ("bvUDiv",        mapsTo vectorsModule "bvUDiv")
  , ("bvURem",        mapsTo vectorsModule "bvURem")
  , ("bvsge",         mapsTo vectorsModule "bvsge")
  , ("bvsgt",         mapsTo vectorsModule "bvsgt")
  , ("bvsle",         mapsTo vectorsModule "bvsle")
  , ("bvslt",         mapsTo vectorsModule "bvslt")
  , ("bvult",         mapsTo vectorsModule "bvult")
  , ("bvule",         mapsTo vectorsModule "bvule")
  , ("coerceVec",     mapsTo vectorsModule "coerceVec")
  , ("eq_Vec",        skip)
  , ("foldr",         mapsTo vectorsModule "foldr")
  , ("gen",           mapsTo vectorsModule "gen")
  , ("rotateL",       mapsTo vectorsModule "rotateL")
  , ("rotateR",       mapsTo vectorsModule "rotateR")
  , ("shiftL",        mapsTo vectorsModule "shiftL")
  , ("shiftR",        mapsTo vectorsModule "shiftR")
  , ("take0",         skip)
  -- zip must be realized in-place because it both depends on definitions and is
  -- used by other definitions in the same file, so it can neither be pre- nor
  -- post-defined.
  , ("zip",           realize zipSnippet)
  -- cannot map directly to Vector.t because arguments are in a different order
  , ("Vec",           mapsTo vectorsModule "Vec")
  ]

  -- Integers
  ++
  [ ("Integer",  mapsTo sawDefinitionsModule "Integer")
  , ("intAdd",   mapsTo sawDefinitionsModule "intAdd")
  , ("intSub",   mapsTo sawDefinitionsModule "intSub")
  , ("intMul",   mapsTo sawDefinitionsModule "intMul")
  , ("intDiv",   mapsTo sawDefinitionsModule "intDiv")
  , ("intMod",   mapsTo sawDefinitionsModule "intMod")
  , ("intMin",   mapsTo sawDefinitionsModule "intMin")
  , ("intMax",   mapsTo sawDefinitionsModule "intMax")
  , ("intNeg",   mapsTo sawDefinitionsModule "intNeg")
  , ("intAbs",   mapsTo sawDefinitionsModule "intAbs")
  , ("intEq",    mapsTo sawDefinitionsModule "intEq")
  , ("intLe",    mapsTo sawDefinitionsModule "intLe")
  , ("intLt",    mapsTo sawDefinitionsModule "intLt")
  , ("intToNat", mapsTo sawDefinitionsModule "intToNat")
  , ("natToInt", mapsTo sawDefinitionsModule "natToInt")
  , ("intToBv",  mapsTo vectorsModule "intToBv")
  , ("bvToInt",  mapsTo vectorsModule "bvToInt")
  , ("sbvToInt", mapsTo vectorsModule "sbvToInt")
  ]

  -- Modular integers
  ++
  [ ("IntMod",     mapsTo sawDefinitionsModule "IntMod")
  , ("toIntMod",   mapsTo sawDefinitionsModule "toIntMod")
  , ("fromIntMod", mapsTo sawDefinitionsModule "fromIntMod")
  , ("intModEq",   mapsTo sawDefinitionsModule "intModEq")
  , ("intModAdd",  mapsTo sawDefinitionsModule "intModAdd")
  , ("intModSub",  mapsTo sawDefinitionsModule "intModSub")
  , ("intModMul",  mapsTo sawDefinitionsModule "intModMul")
  , ("intModNeg",  mapsTo sawDefinitionsModule "intModNeg")
  ]

  -- Axioms currently skipped
  ++
  [ ("drop0",                skip)
  , ("bvugt",                skip)
  , ("bvuge",                skip)
  , ("bvPopcount",           skip)
  , ("bvCountLeadingZeros",  skip)
  , ("bvCountTrailingZeros", skip)
  , ("bvForall",             skip)
  , ("bvAddZeroL",           skip)
  , ("bvAddZeroR",           skip)
  , ("bvShl",                skip)
  , ("bvShr",                skip)
  , ("bvShiftL_bvShl",       skip)
  , ("bvShiftR_bvShr",       skip)
  , ("bvEq_refl",            skip)
  , ("equalNat_bv",          skip)
  , ("Float",                skip)
  , ("mkFloat",              skip)
  , ("Double",               skip)
  , ("mkDouble",             skip)
  , ("bveq_sameL",           skip)
  , ("bveq_sameR",           skip)
  , ("bveq_same2",           skip)
  , ("bvNat_bvToNat",        skip)
  , ("ite_split_cong",       skip)
  , ("ite_join_cong",        skip)
  , ("map_map",              skip)
  , ("test_fun0",            skip)
  , ("test_fun1",            skip)
  , ("test_fun2",            skip)
  , ("test_fun3",            skip)
  , ("test_fun4",            skip)
  , ("test_fun5",            skip)
  , ("test_fun6",            skip)
  ]

  -- The computation monad
  ++
  [ ("CompM",                replace (Coq.Var "CompM"))
  , ("returnM",              replace (Coq.App (Coq.Var "@returnM")
                                       [Coq.Var "CompM", Coq.Var "_"]))
  , ("bindM",                replace (Coq.App (Coq.Var "@bindM")
                                       [Coq.Var "CompM", Coq.Var "_"]))
  , ("errorM",               replace (Coq.App (Coq.Var "@errorM")
                                       [Coq.Var "CompM", Coq.Var "_"]))
  , ("catchM",               skip)
  , ("fixM",                 replace (Coq.App (Coq.Var "@fixM")
                                       [Coq.Var "CompM", Coq.Var "_"]))
  , ("fixM",                 replace (Coq.App (Coq.Var "@fixM")
                                       [Coq.Var "CompM", Coq.Var "_"]))
  , ("LetRecType",           mapsTo compMModule "LetRecType")
  , ("LRT_Ret",              mapsTo compMModule "LRT_Ret")
  , ("LRT_Fun",              mapsTo compMModule "LRT_Fun")
  , ("lrtToType",            mapsTo compMModule "lrtToType")
  , ("LetRecTypes",          mapsTo compMModule "LetRecTypes")
  , ("LRT_Cons",             mapsTo compMModule "LRT_Cons")
  , ("LRT_Nil",              mapsTo compMModule "LRT_Nil")
  , ("lrtPi",                mapsTo compMModule "lrtPi")
  , ("lrtTupleType",         mapsTo compMModule "lrtTupleType")
  , ("multiFixM",            mapsTo compMModule "multiFixM")
  , ("letRecM",              mapsTo compMModule "letRecM")
  ]

  -- Dependent pairs
  ++
  [ ("Sigma", replace (Coq.Var "@sigT"))
  , ("exists", replace (Coq.Var "@existT"))
  , ("Sigma__rec", replace (Coq.Var "@sigT_rect"))
  , ("Sigma_proj1", replace (Coq.Var "@projT1"))
  , ("Sigma_proj2", replace (Coq.Var "@projT2"))
  ]

  -- Lists
  ++
  [ ("List", replace (Coq.Var "@Datatypes.list"))
  , ("Nil", replace (Coq.Var "@Datatypes.nil"))
  , ("Cons", replace (Coq.Var "@Datatypes.cons"))
  , ("List__rec", replace (Coq.Var "@Datatypes.list_rect"))
  ]

  -- Definitions that depend on axioms currently skipped
  ++
  [ ("composeM",   skip)
  , ("letRecFuns", skip)
  ]

constantsRenamingMap :: [(String, String)] -> Map.Map String String
constantsRenamingMap notations = Map.fromList notations

-- TODO: Now that ExtCns contains a unique identifier, it might make sense
-- to check those here to avoid some captures?
translateConstant :: [(String, String)] -> ExtCns e -> String
translateConstant notations (EC {..}) =
  Map.findWithDefault
    (Text.unpack (toShortName ecName))
    (Text.unpack (toShortName ecName))
    (constantsRenamingMap notations) -- TODO short name doesn't seem right

zipSnippet :: String
zipSnippet = [i|
Fixpoint zip (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b)
  : Vec (minNat m n) (a * b) :=
  match
    xs in Vector.t _ m'
    return Vector.t _ (minNat m' n)
  with
  | Vector.nil => Vector.nil _
  | Vector.cons x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (minNat (S pm) n')
    with
    | Vector.nil => Vector.nil _
    | Vector.cons y pm' ys => Vector.cons _ (x, y) _ (zip _ _ _ _ xs ys)
    end
  end
.
|]
