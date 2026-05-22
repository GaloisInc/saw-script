{- |
Module      : CryptolSAWCore.GlobalCryptolEnv
Description : Cryptol to SAWCore import logic
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module CryptolSAWCore.GlobalCryptolEnv 
  ( ImportVisibility(..)
  , isToplevel
  , sameHeight
  , pushScope
  , popScope
  , initEnv
  , CryptolEnv(..)
  , withModEnvSupply
  , mapNaming
  , mapImports
  , setModuleEnv
  , eExtraNaming
  , eImports
  , eModuleEnv
  , eExtraVars
  , addExtraVars
  , eExtraTySyns
  , addExtraTySyns
  , eAllVars
  , addAllVars
  , eTyVars
  , addTyVars
  , eTyProps
  , addTyProps
  , eAllTerms
  , addAllTerms
  , eRefPrims
  , addRefPrims
  , ePrims
  , addPrims
  , ePrimTypes
  , addPrimTypes
  , eFFITypes
  , addFFITypes
  , withFreshScope
  , getAllIfaceDecls
  ) where

import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NE
import Data.Map (Map)
import qualified Data.Map as Map


import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Name as C
import qualified Cryptol.ModuleSystem.Renamer as MR

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Utils.Ident as C

import SAWCore.SharedTerm
import SAWCore.Term.Functor (FieldName)

import CryptolSAWCore.Panic
import qualified Cryptol.ModuleSystem as MI
import Control.Monad (unless)

--------------------------------------------------------------------------------

-- | ImportVisibility is an enumeration that indicates how we handle
-- the visibility of the symbols in an imported module.
--
-- `OnlyPublic` makes only the public/exported symbols of a module
-- visible from SAW. `PublicAndPrivate` instead makes all symbols
-- visible, as if one is working inside it. The latter is often useful
-- (or necessary) for verification and code generation.
--
-- `PublicAndPrivate` is akin to setting the module focus in the
-- Cryptol REPL; however, it uses a simpler internal mechanism and is
-- only settable at import time.
--
-- (See 'CryptolEnv.importCryptolModule'.)
--
-- NOTE: this notion of public vs. private symbols is specific to
-- SAWScript and distinct from Cryptol's notion of private
-- definitions.
--
-- FUTURE: this should probably be replaced with a way to manipulate
-- the module focus like the Cryptol REPL uses. What you really want
-- is not to expose module innards that weren't meant to be exposed,
-- but to go inside to prove things in the module's internal context.
--
data ImportVisibility
  = OnlyPublic       -- ^ behaves like a normal Cryptol @import@
  | PublicAndPrivate -- ^ allows viewing of both @private@ sections
                     --   and (arbitrarily nested) submodules.
  deriving (Eq, Show)


-- | The global environment for capturing the Cryptol state, both
--   Cryptol's own state and the state associated with
--   importing/translating into SAWCore.
--   This is intended to be a write-once record of any work done
--   during translation, analagous to the 'SharedContext' from
---  SAWCore. Rather than directly accessing this environment,
--   operations take/return a 'CryptolEnv', which additionally
--   includes a scoped naming environment via 'CryptolScope'.


--
-- Note that prior to 202603 there were two environment types,
-- `CryptolEnv` carrying around the persistent bits and generally
-- being (in most places) the external interface; and another type
-- called (far too generically) @Env@ used by the import logic in this
-- file. There was a bunch of code for copying bits from `CryptolEnv`
-- into an empty @Env@ on the fly, calling into here, then pouring the
-- results back. This code was arbitrary and in some cases possibly
-- wrong. Furthermore, having the import code tied to an incompatible
-- type made a bunch of external code calling directly into it pass an
-- empty environment instead, which caused further problems.
--
-- While this was being fixed the prior @Env@ type got renamed to
-- @ImportEnv@. There should be no references to it or its field names
-- (@imp*@ rather than @env*@) left, but in case some are hiding in
-- comments the transitional field names are also documented below.
--
-- There is now one environment type. The history above remains
-- relevant until all the leftover warts and weaknesses arising from
-- the old structure get cleaned out, which may take a while.
--
-- (FUTURE: once that's done, remove the historical notes; they are
-- only of value while they remain relevant to the current code.)
data GlobalCryptolEnv = GlobalCryptolEnv
  { geModuleEnv   :: ME.ModuleEnv
  -- | Invariant: This is a subset of 'geAllVars', which is
  --   enforced by 'addExtraVars'
  , geExtraVars   :: Map C.Name C.Schema
  , geExtraTySyns :: Map C.Name C.TySyn
  , geAllVars     :: Map C.Name C.Schema
  , geTyVars      :: Map Int Term
  , geTyProps     :: Map C.Prop (Term, [FieldName])
  , geAllTerms    :: Map C.Name Term
  , geRefPrims    :: Map C.PrimIdent C.Expr
  , gePrims       :: Map C.PrimIdent Term
  , gePrimTypes   :: Map C.PrimIdent Term
  , geFFITypes    :: Map NameInfo C.FFI
  }

-- | Initialize the global environment with the given 'ME.ModuleEnv',
--   and populate the 'geAllVars' accordingly.
initGlobalEnv :: ME.ModuleEnv -> GlobalCryptolEnv
initGlobalEnv modEnv = refreshCryptolEnv $
    GlobalCryptolEnv modEnv
      mempty mempty mempty mempty mempty mempty mempty mempty mempty 
      mempty

instance IsMetadata GlobalCryptolEnv where
  initMetadata = initGlobalEnv <$> ME.initialModuleEnv

-- | Restore a `GlobalCryptolEnv` from a checkpoint. The first argument
--   @chkEnv@ is the `GlobalCryptolEnv` saved by / copied into the
--   checkpoint; the second argument @newEnv@ is the current one
--   we wish to overwrite by rolling back to the checkpoint.
--   The 'ME.meNameSeeds' and 'ME.meSupply' from the
--   module environment are not rolled back, to avoid re-using old
--   names.
--   NOTE: This effectively
--   invalidates any translated 'Term's or Cryptol expressions created
--   after the checkpoint. Attempting to use them in the restored
--   environment will have unpredictable results, and likely will
--   result in a panic. Similarly, 'CryptolEnv's captured after the
--   checkpoint are no longer safe to use in the resulting environment.

--   We also ought to invalidate terms constructed since the checkpoint
--   was taken, like SAWCore does. See #2859.

--   We could, for example, have 'CryptolScope' track which
--   identifiers it references, and check that they are in a valid
--   range with respect to the corresponding global environment
--   before combining them into a 'CryptolEnv'.
  restoreMetadata chk now = return $
    let newMEnv = geModuleEnv chk
        chkMEnv = geModuleEnv now
    in chk { geModuleEnv = chkMEnv 
               { ME.meNameSeeds = ME.meNameSeeds newMEnv
               , ME.meSupply = ME.meSupply newMEnv 
               }
           }

-- | A scope frame that captures which Cryptol names are accessible.
--  `fNamingEnv` is the local naming environment, which can be extended
--  ad-hoc with additional declarations. `fImports` is a list of all
--  the modules that have been imported, and a visibility setting for
--  each. This does not include, for example, builtin modules that
--  exist but that have not been imported.

data CryptolFrame =
  CryptolFrame { fNamingEnv :: MR.NamingEnv
               , fImports :: [(ImportVisibility, C.Import)] 
               }

initFrame :: CryptolFrame
initFrame = CryptolFrame mempty mempty

-- | A nonempty list of 'CryptolFrame's, where the first element is the
--   "bottom" frame that takes highest precedence when looking up
--   names. Each individual frame only contains values declared at
--   exactly that level. The full scope is computed by collecting
--   everything in this stack, via 'eExtraNaming' and 'eImports'.
newtype CryptolEnv = CryptolEnv (NonEmpty CryptolFrame)

initEnv :: CryptolEnv
initEnv = CryptolEnv (initFrame :| [])

isToplevel :: CryptolEnv -> Bool
isToplevel (CryptolEnv (_ :| frames)) = null frames

-- | Test if the scopes have the same number of frames pushed.
sameHeight :: CryptolEnv -> CryptolEnv -> Bool
sameHeight (CryptolEnv scope1) (CryptolEnv scope2) = 
  NE.length scope1 == NE.length scope2

mapCurFrame :: 
  (CryptolFrame -> CryptolFrame) -> 
  CryptolEnv -> 
  CryptolEnv
mapCurFrame f (CryptolEnv (frame :| frames)) =
  CryptolEnv (f frame :| frames)

-- | Push a fresh frame onto the stack.
pushScope :: CryptolEnv -> CryptolEnv
pushScope (CryptolEnv frames) = CryptolEnv (initFrame <| frames)

-- | Pop the current frame from the stack, discarding its
--   contents. Panics if this is the only frame.
popScope :: CryptolEnv -> CryptolEnv
popScope (CryptolEnv frames) = case snd (NE.uncons frames) of
  Nothing -> panic "popScope" [ "Popping topmost scope"]
  Just frames' -> CryptolEnv frames'

-- | Map the naming environment of the frame currently in scope.
mapNaming :: 
  (MR.NamingEnv -> MR.NamingEnv) -> 
  CryptolEnv -> 
  CryptolEnv
mapNaming f = mapCurFrame $ 
      \fr -> fr {fNamingEnv = f (fNamingEnv fr) }

-- | Map the module imports of the frame currently in scope.
mapImports :: 
  ([(ImportVisibility, C.Import)] -> [(ImportVisibility, C.Import)] ) -> 
  CryptolEnv -> 
  CryptolEnv
mapImports f = mapCurFrame $ 
      \fr -> fr {fImports = f (fImports fr) }

-- | Run the inner action bracketed new frame pushed/popped on
--   the 'CryptolScope' stack.
--   Fails if the inner action changes the scope height
--   (i.e. it does not properly bracket its pushes and pops).
withFreshScope :: 
  MonadFail m =>
  CryptolEnv -> 
  (CryptolEnv -> 
  m (a, CryptolEnv)) -> 
  m (a, CryptolEnv)
withFreshScope env0 f = do
  let env1 = pushScope env0
  (a, env2) <- f env1
  unless (sameHeight env1 env2) $
    fail "withFreshScope: mismatched push/pops"
  let env3 = popScope env2
  return (a, env3)

-- | Access the 'C.Supply' in the global 'ME.ModuleEnv' for generating
--   fresh names. More efficient than directly modifying the
--   environment and using 'setModuleEnv', as it avoids any other
--   bookkeeping.
withModEnvSupply :: SharedContext -> (C.Supply -> (a, C.Supply)) -> IO a
withModEnvSupply sc f = do
  modEnv <- eModuleEnv sc
  let (a, supply) = f $ ME.meSupply modEnv
  mapModEnv sc (\modEnv_ -> modEnv_ { ME.meSupply = supply } )
  return a

-------------------------------------
-- Environment Access --

getGlobal :: (GlobalCryptolEnv -> a) -> SharedContext -> IO a
getGlobal f sc = f <$> scGetData sc

mapGlobal :: SharedContext -> (GlobalCryptolEnv -> GlobalCryptolEnv) -> IO ()
mapGlobal = scUpdateData

mapModEnv :: SharedContext -> (ME.ModuleEnv -> ME.ModuleEnv) -> IO ()
mapModEnv sc f = mapGlobal sc (\genv -> genv { geModuleEnv = f (geModuleEnv genv) })

-- The "getters" below were historically fields in 'CryptolEnv', which
-- are now defined functions that access either the 'GlobalCryptolEnv'
-- or the 'CryptolScope' as appropriate. In contrast, updates were
-- historically made by directly accessing 'CryptolEnv' fields, and are
-- now restricted to only adding new entries to the maps in
-- 'GlobalCryptolEnv' (e.g. 'addExtraVars'). This enforces the policy
-- that the global environment is intended to be a complete record of
-- all work done during translation/import, regardless of scope. Since
-- the maps in the global environment are all keyed on globally-unique
-- values, these operations are expected to only add entries and never
-- overwrite existing ones.
--
-- NOTE: We could enforce a write-once policy here, but it's
-- not immediately obvious if we need to support key clashes
-- for equal entries (not possible for
-- some times like 'C.Expr'), or if it is even useful to do so.

-- == Maps from 'GlobalCryptolEnv':

-- == Pieces relating to Cryptol primitives:

-- | Maps Cryptol primitives to their reference
-- implementations that Cryptol keeps around. Currently this field is
-- only populated during initialization; it isn't clear if that's a
-- bug. (If there are really no further uses after initialization,
-- regardless of what the user does, dropping the contents allows the
-- memory to be reclaimed. But if it's possible to construct such
-- uses, they're likely to panic.)
--
-- Before the environment types were merged, this field was found only
-- in @Env@ and called @envRefPrims@ (transitionally @impRefPrims@).
eRefPrims :: SharedContext -> IO (Map C.PrimIdent C.Expr)
eRefPrims = getGlobal geRefPrims

-- | Add entries to 'eRefPrims'
addRefPrims :: SharedContext -> Map C.PrimIdent C.Expr -> IO ()
addRefPrims sc m = mapGlobal sc $ \genv -> 
  genv { geRefPrims = Map.union m (geRefPrims genv) }

-- | Maps names of Cryptol primitives to their implementations
-- as SAWCore terms. Before the environment types were merged, it was
-- also present in @Env@ under the name @envPrims@ (transitionally
-- @impPrims@).
ePrims :: SharedContext -> IO (Map C.PrimIdent Term)
ePrims = getGlobal gePrims

-- | Add entries to 'ePrims'
addPrims :: SharedContext -> Map C.PrimIdent Term -> IO ()
addPrims sc m = mapGlobal sc $ \genv -> 
  genv { gePrims = Map.union m (gePrims genv) }

-- | Maps names of Cryptol primitive types to their
-- implementations as SAWCore terms (that are types). Before the
-- environment types were merged, it was also present in @Env@ under
-- the name @envPrimTypes@ (transitionally @impPrimTypes@).
ePrimTypes :: SharedContext -> IO (Map C.PrimIdent Term)
ePrimTypes = getGlobal gePrimTypes

-- | Add entries to 'ePrimTypes'
addPrimTypes :: SharedContext -> Map C.PrimIdent Term -> IO ()
addPrimTypes sc m = mapGlobal sc $ \genv -> 
  genv { gePrimTypes = Map.union m (gePrimTypes genv) }

-- == Second, the pieces that track Cryptol-level objects and types:

-- | The Cryptol-level module environment; it holds all
-- the modules that have been loaded. Its type is also the state for
-- Cryptol's `ME.ModuleM` monad.
eModuleEnv :: SharedContext -> IO ME.ModuleEnv
eModuleEnv = getGlobal geModuleEnv

-- | Update 'eModuleEnv', adding new entries to 'eAllVars' as needed.

-- TODO: sanity checks? This only makes sense if set of loaded modules
-- in the given environment is a superset of those in the current
-- environment. Additionally, the supply and seeds should necessarily
-- be more recent. Finally, the environment refresh is only necessary
-- if more modules were actually added (and technically only required
-- for the new modules).
setModuleEnv :: SharedContext -> ME.ModuleEnv -> IO ()
setModuleEnv sc modEnv = mapGlobal sc $ \genv ->
  refreshCryptolEnv $ genv { geModuleEnv = modEnv }


-- | Formerly @eExtraTSyns@, holds the expansions for
-- the "extra names" that are type aliases (synonyms). Maps names to
-- `T.TySyn`, which wraps Cryptol types and among other things allows
-- synonyms to take parameters.
eExtraTySyns :: SharedContext -> IO (Map C.Name C.TySyn)
eExtraTySyns = getGlobal geExtraTySyns

-- | Add entries to 'eExtraTySyns'
addExtraTySyns :: SharedContext -> Map C.Name C.TySyn -> IO ()
addExtraTySyns sc m = mapGlobal sc $ \genv -> 
  genv { geExtraTySyns = Map.union m (geExtraTySyns genv) }

-- | Formerly @eExtraTypes@, holds the Cryptol-level
-- types for "extra names" that are value/term variables. Maps names
-- to type schemes.
eExtraVars :: SharedContext -> IO (Map C.Name C.Schema)
eExtraVars = getGlobal geExtraVars

-- | Add entries to both 'eExtraVars' and 'eAllVars'
addExtraVars :: SharedContext -> Map C.Name C.Schema -> IO ()
addExtraVars sc m = mapGlobal sc $ \genv -> 
  genv { geExtraVars = Map.union m (geExtraVars genv)
       , geAllVars = Map.union m (geAllVars genv) 
       }

-- Before the environment types were merged, the above five fields
-- were not accessible via @Env@, which turned out to cause
-- complications.

-- | Map from Cryptol names to Cryptol types. This is
-- used to call `fastTypeOf` and `fastSchemaOf` on Cryptol expressions
-- to fetch their types. This table is derived from information
-- properly kept elsewhere and is a headache to have.
--
-- Before the environment types were merged, this was found only in
-- @Env@ under the name @envC@. It was built on the fly when calling
-- into the import code using @Env@ and thrown away afterwards.
-- Now it is updated every time the module environment is modified
-- via 'setModuleEnv'.
-- (Transitionally it was called @impCry@ and then @impAllVars@.)

-- FUTURE: in principle we should be able to use the SAWCore types of
-- the SAWCore terms after importing them, instead of `fastTypeOf` and
-- `fastSchemaOf`, and drop the `eAllVars` table. In practice, doing
-- that relies (in some cases) on being able to call `scCryptolType`
-- to reconstruct the Cryptol-level type; that in turn requires, when
-- inside a forall-binding, logic to intercept and lift SAWCore type
-- variables back to their Cryptol parents. That requires a table we
-- don't currently have, as well as additional lookup logic that
-- doesn't currently exist. Furthermore, while we've fixed many of the
-- ways the Cryptol -> SAWCore type mapping is noninjective, it still
-- won't work for enumerations. And beyond that, when handling
-- polymorphic type schemes we erase certain typeclasses in the
-- translation, and that loses info, so we might need to translate
-- those classes to placeholders instead of erasing them. It may then
-- also be that the one use of `fastSchemaOf` can't actually be
-- avoided; that isn't super clear.
eAllVars :: SharedContext -> IO (Map C.Name C.Schema)
eAllVars = getGlobal geAllVars

-- | Add entries to 'eAllVars'
addAllVars :: SharedContext  -> Map C.Name C.Schema -> IO ()
addAllVars sc m = mapGlobal sc $ \genv -> 
  genv { geAllVars = Map.union m (geAllVars genv) }

-- == Third, the pieces that track imported SAWCore bits:

-- | Maps Cryptol type variable IDs to SAWCore types. This is
-- only nonempty during import, when working inside a forall-binding.
-- Before the environment types were merged, this was only needed in
-- (and only found in) @Env@ as @envT@. Transitionally, it was called
-- @impTy@ and then @impTyVars@.
eTyVars :: SharedContext -> IO (Map Int Term)
eTyVars = getGlobal geTyVars

-- | Add entries to 'eTyVars'
addTyVars :: SharedContext -> Map Int Term -> IO ()
addTyVars sc m = mapGlobal sc $ \genv -> 
  genv { geTyVars = Map.union m (geTyVars genv) }

-- | Maps Cryptol `C.Prop`, which are type constraints, to
-- corresponding SAWCore information. There is both a term and a list
-- of `FieldName`. The actual class dictionary we need is obtained by
-- applying the given field selectors (in reverse order!) to the term.
-- (This arises when a dictionary comes from a superclass; the field
-- projections traverse the subclass dictionaries.)
-- The constraints are referenced implicitly by their types.
--
-- Like `eTyVars`, this table is only nonempty during import, when
-- working inside a forall-binding, and carries the info from that
-- binding.
--
-- Before the environment types were merged, this was only needed in
-- (and only found in) @Env@ as @envP@. Transitionally, it was called
-- @impProp@ and then @envTyProps@.
eTyProps :: SharedContext -> IO (Map C.Prop (Term, [FieldName]))
eTyProps = getGlobal geTyProps

-- | Add entries to 'eTyProps'.

--   The one current use of this function in 'CryptolSAWCore.Cryptol'
--   collects all of the superclasses of the given 'C.Prop' as well.
--   It may make sense to move that logic here, as the current
--   approach involves redundantly re-computing the entries for
--   all superclasses for each individual entry.
--   This is not expensive, but would become problematic
--   if we wanted to enforce a write-once policy.
addTyProps :: SharedContext -> Map C.Prop (Term, [FieldName]) -> IO ()
addTyProps sc m = mapGlobal sc $ \genv -> 
  genv { geTyProps = Map.union m (geTyProps genv)  }

-- | Formerly @eTermEnv@, holds the translations for all
-- Cryptol names in scope. It maps names to SAWCore terms. Apparently
-- it includes types as well as values. Does not include the contents
-- of `ePrims` or `ePrimTypes` (which are not identified with a
-- 'C.Name').
-- Note that the keys in this map are not necessarily a superset of
-- those in 'eAllVars', which may contain variables that have not been
-- translated into SAWCore yet. For entries with matching keys, the
-- 'Term' in 'eAllTerms' should be a 'Variable' with a type that is the
-- imported 'C.Schema' from 'eAllVars'.
--
-- Before the environment types were merged, it was also found in @Env@
-- under the name @envE@.
eAllTerms :: SharedContext -> IO (Map C.Name Term)
eAllTerms = getGlobal geAllTerms

-- | Add entries to 'eAllTerms'
addAllTerms :: SharedContext -> Map C.Name Term -> IO ()
addAllTerms sc m = mapGlobal sc $ \genv -> 
  genv { geAllTerms = Map.union m (geAllTerms genv) }

-- | Maps SAWCore names to Cryptol FFI info where relevant.
-- Before the environment types were merged, this was unavailable in
-- @Env@.
eFFITypes :: SharedContext -> IO (Map NameInfo C.FFI)
eFFITypes = getGlobal geFFITypes

-- | Add entries to 'eFFITypes'
addFFITypes :: SharedContext -> Map NameInfo C.FFI -> IO ()
addFFITypes sc m = mapGlobal sc $ \genv -> 
  genv { geFFITypes = Map.union m (geFFITypes genv) }

-- == Scoped entries from 'CryptolEnv':

-- | The "extra" naming environment that captures Cryptol names
--   which don't correspond to any imported module. Generally these
--   result from names created in SAW which have been reflected into
--   the Cryptol environment.
--   This is scoped content, where the accessible names are expected
--   to be managed by SAW and correspond to the same SAW values that
--   are in scope.

-- FUTURE: Cryptol has its own functionality for additional bindings
-- (it uses it for things created from the Cryptol REPL) and we ought
-- to be able to use it instead of bolting on our own additional layer
-- of material. Doing so would avoid various inconsistencies and
-- irregularities that can creep in when we reimplement Cryptol name
-- resolution.
eExtraNaming :: CryptolEnv -> MR.NamingEnv
eExtraNaming (CryptolEnv (frame :| frames)) = 
  foldr (\fr ne -> ne `MR.shadowing` (fNamingEnv fr)) (fNamingEnv frame) frames

-- | The list of Cryptol modules which have been brought into the
--   current scope. This essentially acts as a filter on the full set
--   of loaded modules in the global module environment ('eModuleEnv'),
--   where the contents of the selected modules are brought into scope
--   according to the associated 'ImportVisibility'. The modules here
--   should only correspond to modules that are present in the module
--   environment *and* have been translated into SAWCore.
eImports :: CryptolEnv -> [(ImportVisibility, C.Import)]
eImports (CryptolEnv frames) = 
  concat $ map fImports $ NE.toList frames


-- | Refresh 'geAllVars' after updating the module environment.
--   Previously (before 'GlobalCryptolEnv'), this would overwrite the
--   'eAllVars' field. Now this will add new vars (i.e. from
--   newly-added modules) but keep existing ones, as the
--   'GlobalCryptolEnv' should never drop entries. If the module
--   environment has been managed properly, we expect any clashing keys
--   to have equal elements, but this is not checked/enforced. Not
--   exported.
refreshCryptolEnv :: GlobalCryptolEnv -> GlobalCryptolEnv
refreshCryptolEnv genv =
     let modEnv = geModuleEnv genv
         ifaceDecls = getAllIfaceDecls modEnv
         newtypeCons = Map.fromList
                         [ con
                         | nt <- Map.elems (MI.ifNominalTypes ifaceDecls)
                         , con <- C.nominalTypeConTypes nt
                         ]
         vars = Map.map MI.ifDeclSig $ MI.ifDecls ifaceDecls
         -- note that we don't need to re-add geExtraVars, because
         -- it is already included in the existing geAllVars
         allvars = newtypeCons `Map.union` vars
         allvars' = Map.union allvars (geAllVars genv)
     in genv { geAllVars = allvars' }

---- Misc Exports --------------------------------------------------------------

getAllIfaceDecls :: ME.ModuleEnv -> MI.IfaceDecls
getAllIfaceDecls me =
  mconcat
    (map (MI.ifDefines . ME.lmInterface)
         (ME.getLoadedModules (ME.meLoadedModules me)))