{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWCoreLean.SpecialTreatment
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Per-identifier treatment table: how to translate specific SAWCore
constants when they appear at a definition site or a use site.

Near-mirror of "SAWCoreRocq.SpecialTreatment", with Lean-target names.
The table itself (see 'specialTreatmentMap') starts empty and fills
incrementally as the Phase-1 Lean-side support library grows.
-}

module SAWCoreLean.SpecialTreatment
  ( DefSiteTreatment(..)
  , UseSiteTreatment(..)
  , IdentSpecialTreatment(..)
  , translateModuleName
  , findSpecialTreatment'
  , findSpecialTreatment
  , escapeIdent
    -- * Combinators for building 'IdentSpecialTreatment' values
  , mapsTo
  , mapsToExpl
  , mapsToCore
  , mapsToCoreExpl
  , rename
  , realize
  , replace
  , replaceDropArgs
  , skip
    -- * Named target modules on the Lean side
  , sawScaffoldingModule
  , sawVectorsModule
  , sawBitvectorsModule
  , sawCorePreludeExtraModule
  , sawCorePrimitivesModule
  ) where

import           Control.Lens            (_1, _2, over)
import           Control.Monad.Reader    (asks)
import           Data.Char               (isAlphaNum)
import qualified Data.Map                as Map
import           Data.Map                (Map)
import           Prelude                 hiding (fail)
import           Text.Encoding.Z         (zEncodeString)

import qualified Language.Lean.AST       as Lean

import           SAWCore.Name

import           SAWCoreLean.Monad

-- | How to handle a SAWCore identifier at its definition site.
data DefSiteTreatment
  = -- | Translate the identifier unchanged, and directly translate the
    --   associated SAWCore declaration.
    DefPreserve
  | -- | Translate the identifier into the given Lean identifier, and
    --   otherwise directly translate the associated SAWCore declaration.
    DefRename Lean.Ident
  | -- | Replace the declaration of the identifier with the given text
    --   verbatim (emitted as a 'Lean.Snippet').
    DefReplace String
  | -- | Skip the declaration of the identifier altogether (the Lean side
    --   is expected to define it independently).
    DefSkip

-- | How to translate a SAWCore identifier at its use sites.
data UseSiteTreatment
  = -- | Translate the identifier unchanged.
    UsePreserve
    -- | Rename the identifier to the given (optionally qualified) Lean
    --   identifier. When the 'Bool' is 'True' the use site is emitted
    --   with a leading @\@@, forcing all implicit arguments to be
    --   supplied explicitly.
  | UseRename (Maybe ModuleName) Lean.Ident Bool
    -- | Apply a macro function to the translations of the first @n@
    --   SAWCore arguments of this identifier. Used for things like
    --   collapsing Cryptol's binary numeric encoding (@TCNum (NatPos
    --   (Bit0 (Bit0 One)))@) into a plain 'Lean.NatLit' at translation
    --   time.
  | UseMacro Int ([Lean.Term] -> Lean.Term)

data IdentSpecialTreatment = IdentSpecialTreatment
  { atDefSite :: DefSiteTreatment
  , atUseSite :: UseSiteTreatment
  }

-- | SAWCore module names get remapped to their Lean-support-library
-- counterparts.
moduleRenamingMap :: Map ModuleName ModuleName
moduleRenamingMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  over _2 mkModuleName <$>
  [ ("Cryptol", ["CryptolToLean", "CryptolPrimitivesForSAWCore"])
  , ("Prelude", ["CryptolToLean", "SAWCorePrelude"])
  ]

translateModuleName :: ModuleName -> ModuleName
translateModuleName mn =
  Map.findWithDefault mn mn moduleRenamingMap

findSpecialTreatment' ::
  TranslationConfigurationMonad r m =>
  NameInfo -> m IdentSpecialTreatment
findSpecialTreatment' nmi =
  case nmi of
    ModuleIdentifier ident -> findSpecialTreatment ident
    ImportedName{} -> pure (IdentSpecialTreatment DefPreserve UsePreserve)

findSpecialTreatment ::
  TranslationConfigurationMonad r m =>
  Ident -> m IdentSpecialTreatment
findSpecialTreatment ident = do
  configuration <- asks translationConfiguration
  let moduleMap = Map.findWithDefault Map.empty (identModule ident)
                    (specialTreatmentMap configuration)
  let defaultTreatment = IdentSpecialTreatment
        { atDefSite = DefPreserve
        , atUseSite = UsePreserve
        }
  pure $ Map.findWithDefault defaultTreatment (identName ident) moduleMap

-- | Use 'mapsTo' for identifiers whose definition has a matching
-- definition already on the Lean side. Skips the SAWCore-side
-- definition; use sites are rewritten to point at the provided target.
mapsTo :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsTo targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName False
  }

-- | Like 'mapsTo' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly.
mapsToExpl :: ModuleName -> Lean.Ident -> IdentSpecialTreatment
mapsToExpl targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName True
  }

-- | Maps a SAWCore identifier to a Lean-core name (no module prefix).
-- Used for primitives that resolve directly in Lean's prelude
-- (@Bool@, @Nat@, @Int@, …).
mapsToCore :: Lean.Ident -> IdentSpecialTreatment
mapsToCore targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename Nothing targetName False
  }

-- | Like 'mapsToCore' but emits @\@name@ at use sites, forcing all
-- implicit arguments to be supplied explicitly. Needed for names like
-- Lean's @Eq@ where the type parameter is implicit in Lean but
-- SAWCore supplies it explicitly.
mapsToCoreExpl :: Lean.Ident -> IdentSpecialTreatment
mapsToCoreExpl targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename Nothing targetName True
  }

-- | Use 'realize' for axioms or primitives that must be realized
-- where they were originally declared. Emits the supplied verbatim
-- Lean text at the def site; use sites are left unchanged.
realize :: String -> IdentSpecialTreatment
realize code = IdentSpecialTreatment
  { atDefSite = DefReplace code
  , atUseSite = UsePreserve
  }

-- | Rename a SAWCore identifier whose definition can be translated
-- but whose name clashes with Lean's. (For example, SAWCore's @at@
-- would collide with Lean-idiomatic uses; Rocq also uses this
-- combinator for exactly this case.)
rename :: Lean.Ident -> IdentSpecialTreatment
rename ident = IdentSpecialTreatment
  { atDefSite = DefRename ident
  , atUseSite = UseRename Nothing ident False
  }

-- | Replace any occurrence of the identifier applied to @n@ arguments
-- with the supplied Lean term.
replaceDropArgs :: Int -> Lean.Term -> IdentSpecialTreatment
replaceDropArgs n term = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseMacro n (const term)
  }

-- | A version of 'replaceDropArgs' that drops no arguments.
replace :: Lean.Term -> IdentSpecialTreatment
replace = replaceDropArgs 0

-- | For identifiers that are already defined in the Lean-side support
-- library under the same name — skip the SAWCore-side definition and
-- emit the short name unchanged at use sites.
skip :: IdentSpecialTreatment
skip = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UsePreserve
  }

-- | The handwritten Lean-side support modules. Use these as the
-- 'ModuleName' argument to 'mapsTo' / 'mapsToExpl'.
sawScaffoldingModule, sawVectorsModule, sawBitvectorsModule,
  sawCorePreludeExtraModule, sawCorePrimitivesModule :: ModuleName
sawScaffoldingModule      = mkModuleName ["CryptolToLean", "SAWCoreScaffolding"]
sawVectorsModule          = mkModuleName ["CryptolToLean", "SAWCoreVectors"]
sawBitvectorsModule       = mkModuleName ["CryptolToLean", "SAWCoreBitvectors"]
sawCorePreludeExtraModule = mkModuleName ["CryptolToLean", "SAWCorePreludeExtra"]
sawCorePrimitivesModule   = mkModuleName ["CryptolToLean", "SAWCorePrimitives"]

-- | The per-SAWCore-module treatment tables. Starts empty; entries
-- accumulate here as the Lean-side support library grows. Compare
-- 'SAWCoreRocq.SpecialTreatment.specialTreatmentMap' (which is
-- ~500 lines) — the Lean-side analog fills in gradually over Phase 1.
specialTreatmentMap :: TranslationConfiguration ->
                       Map ModuleName (Map String IdentSpecialTreatment)
specialTreatmentMap _configuration = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  [ ("Cryptol", cryptolPreludeSpecialTreatmentMap)
  , ("Prelude", sawCorePreludeSpecialTreatmentMap)
  ]

-- | Cryptol-side treatment entries. The Cryptol @Num@ inductive and
-- its constructors are declared in 'CryptolToLean.SAWCorePrimitives'
-- so translated output has something to reference.
cryptolPreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
cryptolPreludeSpecialTreatmentMap = Map.fromList
  [ ("Num",   mapsTo sawCorePrimitivesModule "Num")
  , ("TCNum", mapsTo sawCorePrimitivesModule "Num.TCNum")
  , ("TCInf", mapsTo sawCorePrimitivesModule "Num.TCInf")
  ]

-- | Seed entries for 'Prelude.*' primitives whose Lean realisation is
-- already in scope (via Lean's core or the handwritten support lib).
-- Every entry here replaces an otherwise-unresolvable qualified
-- reference like @CryptolToLean.SAWCorePrelude.Bool@.
sawCorePreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
sawCorePreludeSpecialTreatmentMap = Map.fromList
  -- Lean core
  [ ("Bool",    mapsToCore "Bool")
    -- Under specialization, SAWCore's 'Nat' ('Zero | NatPos Pos',
    -- binary-positive) is mapped to Lean's native 'Nat' ('zero |
    -- succ Nat', unary). The constructor-level UseMacro entries
    -- below collapse @NatPos (Bit0 (Bit0 One))@ chains to numeric
    -- literals at translation time, giving clean Lean-side output.
    -- This would silently change the semantics of a 'Nat#rec'
    -- elimination — but 'scNormalize' reduces concrete 'Nat#rec'
    -- calls away before the translator sees them. Residual 'Nat#rec'
    -- on a symbolic argument would still be unsound; if that ever
    -- surfaces we'll need a handwritten 'Nat#rec' wrapper with the
    -- SAW-matching argument order. The polymorphism-residual check
    -- in 'writeLeanTerm' will catch most such cases upstream.
  , ("Nat",     mapsToCore "Nat")
  , ("Integer", mapsToCore "Int")
  , ("String",  mapsToCore "String")
  , ("True",    mapsToCore "Bool.true")
  , ("False",   mapsToCore "Bool.false")
  , ("Eq",      mapsToCoreExpl "Eq")
    -- SAWCore's Eq takes the type explicitly; Lean's Eq takes it
    -- implicitly, so we need @Eq to force the application through.

    -- SAWCore's UnitType translates as a native inductive under
    -- CryptolToLean.SAWCorePrelude (so the auto-generated
    -- @UnitType.rec@ exists — Lean's core @Unit@ is an @abbrev@ for
    -- @PUnit.{1}@ and has no @.rec@). The 'Unit' constructor
    -- conflicts with Lean core's @Unit : Type@ at bare-name use
    -- sites; rename it to @TTUnit@ so both are unambiguous.
  , ("Unit",     rename "TTUnit")

  -- SAWCore capitalizes constructor names; Lean's core @Eq@ uses
  -- lower-case @Eq.refl@. The 'mapsToCoreExpl' flag forces @\@Eq.refl@
  -- to be emitted so all implicit parameters are supplied positionally
  -- — SAWCore always gives them explicitly.
  , ("Refl", mapsToCoreExpl "Eq.refl")

    -- SAWCore's Bool eliminator primitives (iteDep, ite, and their
    -- reduction rules) have the True case before the False case;
    -- Lean's Bool.rec is the opposite. Routing through handwritten
    -- wrappers in SAWCorePreludeExtra permutes the arguments so the
    -- elimination stays faithful to SAW semantics. (Using a direct
    -- mapsTo to Lean's Bool.rec would silently swap the cases at
    -- every use site.)
  , ("iteDep",        mapsTo sawCorePreludeExtraModule "iteDep")
  , ("iteDep_True",   mapsTo sawCorePreludeExtraModule "iteDep_True")
  , ("iteDep_False",  mapsTo sawCorePreludeExtraModule "iteDep_False")
  , ("ite",           mapsTo sawCorePreludeExtraModule "ite")
  , ("ite_eq_iteDep", mapsTo sawCorePreludeExtraModule "ite_eq_iteDep")

  -- Support lib
  , ("Bit",       mapsTo sawScaffoldingModule "Bit")
  , ("Vec",       mapsTo sawVectorsModule     "Vec")
  , ("bitvector", mapsTo sawBitvectorsModule  "bitvector")

    -- Nat / Pos constructors — collapse binary-positive chains to
    -- Lean numeric literals when the argument is already a 'NatLit'.
    -- Non-literal inputs build up @Nat@ arithmetic via a fallback
    -- expression so partial or symbolic applications still
    -- elaborate. 'NatPos' and 'Succ' fall through to plain
    -- wrappers; under the SAW-Nat-to-Lean-Nat mapping 'NatPos' is
    -- the identity on a 'Pos' that is itself a Lean 'Nat'.
  , ("Zero",   replaceDropArgs 0 (Lean.NatLit 0))
  , ("One",    replaceDropArgs 0 (Lean.NatLit 1))
  , ("Succ",   replace (Lean.Var (Lean.Ident "Nat.succ")))
  , ("Bit0",   replace (Lean.Var (Lean.Ident "CryptolToLean.SAWCorePrimitives.bit0_macro")))
  , ("Bit1",   replace (Lean.Var (Lean.Ident "CryptolToLean.SAWCorePrimitives.bit1_macro")))
  , ("NatPos", replace (Lean.Var (Lean.Ident "id")))

    -- SAWCorePrimitives — axioms, inductives, and recursors that
    -- survive 'scNormalize' and for which the handwritten
    -- CryptolToLean.SAWCorePrimitives provides a realisation.
  , ("Either",        mapsTo sawCorePrimitivesModule "Either")
    -- Constructors: SAWCore supplies both type parameters explicitly
    -- at every use site; Lean makes them implicit. Force the @-form
    -- so the two positional arguments resolve correctly.
  , ("Left",          mapsToExpl sawCorePrimitivesModule "Either.Left")
  , ("Right",         mapsToExpl sawCorePrimitivesModule "Either.Right")
  , ("Stream",        mapsTo sawCorePrimitivesModule "Stream")
  , ("MkStream",      mapsToExpl sawCorePrimitivesModule "Stream.MkStream")
  , ("EmptyType",     mapsTo sawCorePrimitivesModule "EmptyType")
  , ("Empty",         mapsTo sawCorePrimitivesModule "EmptyType.Empty")
  , ("RecordType",    mapsTo sawCorePrimitivesModule "RecordType")
  , ("RecordValue",   mapsToExpl sawCorePrimitivesModule "RecordType.RecordValue")
  , ("subNat",        mapsTo sawCorePrimitivesModule "subNat")
  , ("addNat",        mapsTo sawCorePrimitivesModule "addNat")
  , ("intAdd",        mapsTo sawCorePrimitivesModule "intAdd")
  , ("intSub",        mapsTo sawCorePrimitivesModule "intSub")
  , ("intMul",        mapsTo sawCorePrimitivesModule "intMul")
  , ("intDiv",        mapsTo sawCorePrimitivesModule "intDiv")
  , ("intMod",        mapsTo sawCorePrimitivesModule "intMod")
  , ("intNeg",        mapsTo sawCorePrimitivesModule "intNeg")
  , ("intEq",         mapsTo sawCorePrimitivesModule "intEq")
  , ("intLe",         mapsTo sawCorePrimitivesModule "intLe")
  , ("natToInt",      mapsTo sawCorePrimitivesModule "natToInt")
  , ("intToNat",      mapsTo sawCorePrimitivesModule "intToNat")
  , ("gen",           mapsTo sawCorePrimitivesModule "gen")
  , ("atWithDefault", mapsTo sawCorePrimitivesModule "atWithDefault")
  , ("foldr",         mapsTo sawCorePrimitivesModule "foldr")
  , ("foldl",         mapsTo sawCorePrimitivesModule "foldl")
  , ("coerce",        mapsTo sawCorePrimitivesModule "coerce")
  , ("unsafeAssert",  mapsTo sawCorePrimitivesModule "unsafeAssert")
  , ("error",         mapsTo sawCorePrimitivesModule "error")
  ]

-- | Escape a Lean identifier so it's lexically valid. Any non-alnum,
-- non-@_@, non-@'@ character causes the whole identifier to be
-- Z-encoded with an @Op_@ prefix (same scheme the Rocq backend uses,
-- since Z-encoding is purely textual).
escapeIdent :: Lean.Ident -> Lean.Ident
escapeIdent (Lean.Ident str)
  | all okChar str = Lean.Ident str
  | otherwise      = Lean.Ident ("Op_" ++ zEncodeString str)
 where
   okChar x = isAlphaNum x || x `elem` ("_'" :: String)
