{-# LANGUAGE FlexibleContexts #-}
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
sawScaffoldingModule, sawVectorsModule, sawBitvectorsModule :: ModuleName
sawScaffoldingModule = mkModuleName ["CryptolToLean", "SAWCoreScaffolding"]
sawVectorsModule     = mkModuleName ["CryptolToLean", "SAWCoreVectors"]
sawBitvectorsModule  = mkModuleName ["CryptolToLean", "SAWCoreBitvectors"]

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

-- | Cryptol-side treatment entries.
cryptolPreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
cryptolPreludeSpecialTreatmentMap = Map.fromList
  -- 'TCNum' and 'TCInf' are Cryptol's two 'Num' constructors. Don't
  -- unwrap them: 'seq : Num -> sort 0' expects a 'Num', not the
  -- underlying 'Nat'. The Phase-2 generated prelude defines both;
  -- until then they're dangling qualified references (same contract
  -- as every other Cryptol primitive).
  [ ("seq",   mapsTo sawVectorsModule "Vec")
  ]

-- | Seed entries for 'Prelude.*' primitives whose Lean realisation is
-- already in scope (via Lean's core or the handwritten support lib).
-- Every entry here replaces an otherwise-unresolvable qualified
-- reference like @CryptolToLean.SAWCorePrelude.Bool@.
sawCorePreludeSpecialTreatmentMap :: Map String IdentSpecialTreatment
sawCorePreludeSpecialTreatmentMap = Map.fromList
  -- Lean core
  [ ("Bool",    mapsToCore "Bool")
  , ("Nat",     mapsToCore "Nat")
  , ("Integer", mapsToCore "Int")
  , ("String",  mapsToCore "String")
  , ("True",    mapsToCore "true")
  , ("False",   mapsToCore "false")
  , ("Eq",      mapsToCoreExpl "Eq")
    -- SAWCore's Eq takes the type explicitly; Lean's Eq takes it
    -- implicitly, so we need @Eq to force the application through.

  -- Support lib
  , ("Bit",       mapsTo sawScaffoldingModule "Bit")
  , ("Vec",       mapsTo sawVectorsModule     "Vec")
  , ("bitvector", mapsTo sawBitvectorsModule  "bitvector")

  -- Nat constructors — collapse at translation time when the argument
  -- is a known literal. Any non-literal input falls back to the
  -- qualified SAWCorePrelude reference.
  , ("Zero",   IdentSpecialTreatment DefSkip (UseMacro 0 (constMacro 0)))
  , ("Succ",   IdentSpecialTreatment DefSkip (UseMacro 1 succMacro))

  -- Cryptol's binary positives: One = 1, Bit0 n = 2n, Bit1 n = 2n + 1.
  , ("One",    IdentSpecialTreatment DefSkip (UseMacro 0 (constMacro 1)))
  , ("Bit0",   IdentSpecialTreatment DefSkip (UseMacro 1 (arithMacro "Bit0" (\n -> 2 * n))))
  , ("Bit1",   IdentSpecialTreatment DefSkip (UseMacro 1 (arithMacro "Bit1" (\n -> 2 * n + 1))))

    -- 'NatPos : Pos -> Nat' is a structural wrapper with no Lean
    -- counterpart. Leave as a qualified reference; the Phase-2
    -- generated prelude provides 'NatPos : Nat -> Nat := id' (the
    -- Pos/Nat distinction is absent on the Lean side).
  ]

-- | Produce a fixed 'NatLit' regardless of (empty) arguments.
constMacro :: Integer -> [Lean.Term] -> Lean.Term
constMacro n _ = Lean.NatLit n

-- | Collapse @ctor (NatLit n)@ to @NatLit (f n)@; fall back to
-- rebuilding @ctor arg@ as a normal application when the argument
-- isn't already a literal (unexpected for type-level numerics but
-- cheap to handle).
arithMacro :: String -> (Integer -> Integer) -> [Lean.Term] -> Lean.Term
arithMacro _   f [Lean.NatLit n] = Lean.NatLit (f n)
arithMacro ctor _ args =
  Lean.App (Lean.Var (Lean.Ident ("CryptolToLean.SAWCorePrelude." ++ ctor))) args

succMacro :: [Lean.Term] -> Lean.Term
succMacro = arithMacro "Succ" (+ 1)

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
