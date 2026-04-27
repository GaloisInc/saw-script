{- |
Module      : CryptolSAWCore.CryptolEnv
Description : Context for interpreting Cryptol within SAW-Script.
License     : BSD3
Maintainer  : huffman
Stability   : provisional

This module contains (most of) the code for managing the Cryptol
environment and also some of logic for importing into SAWCore.

FUTURE: This module and "Cryptol" should be merged together, shaken
up, and then maybe or maybe not split apart again following some kind
of organizational principle. Right now the division of functionality
between these two modules is mostly a function of historical accident.

-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CryptolSAWCore.CryptolEnv
    -- XXX: re-export ImportVisibility and CryptolEnv from Cryptol.hs
    -- to avoid needing to touch every downstream use. For now. The
    -- whole external interface of Cryptol.hs and CryptolEnv.hs really
    -- needs to be reorganized, after which these exports can go away.
    -- (The definitions used to live here.)
  ( ImportVisibility(..)
  , CryptolEnv(..)

  , ExtCryptolModule(..)
  , prettyExtCryptolModule
  , initCryptolEnv
  , loadCryptolModule
  , loadExtCryptolModule
  , bindExtCryptolModule

  , extractDefFromExtCryptolModule
  , restoreCryptolEnv
  , importCryptolModule
  , bindExtraVar
  , withExtraVar
  , bindTySyn
  , bindIntegerType
  , parseTypedTerm
  , pExprToTypedTerm
  , parseDecls
  , parseSchema
  , declareName
  , getNamingEnv
  , InputText(..)
  , lookupIn
  , resolveIdentifier
  , meSolverConfig
  , C.ImportPrimitiveOptions(..)
  , C.defaultPrimitiveOptions
  )
  where

import Data.ByteString (ByteString)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, splitOn)
import Control.Monad(when)
import GHC.Stack

import System.Environment (lookupEnv)
import System.Environment.Executable (splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import SAWSupport.Console
import qualified SAWSupport.Pretty as PPS

import CryptolSAWCore.Panic
import SAWCore.Name (nameInfo)
import SAWCore.Recognizer (asConstant)
import SAWCore.SharedTerm (NameInfo, SharedContext, Term, ppTerm)

import qualified CryptolSAWCore.Cryptol as C
-- These used to live in this file, so import them unqualified for now.
-- XXX: tidy up
import CryptolSAWCore.Cryptol (ImportVisibility(..), CryptolEnv(..))

import qualified Cryptol.Eval as E
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.ExpandPropGuards as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Error as TE
import qualified Cryptol.TypeCheck.Infer as TI
import qualified Cryptol.TypeCheck.Kind as TK
import qualified Cryptol.TypeCheck.Monad as TM
import qualified Cryptol.TypeCheck.Interface as TIface
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
--import qualified Cryptol.TypeCheck.PP as TP

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Exports as MEx
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Name as MN
import qualified Cryptol.ModuleSystem.Renamer as MR

import qualified Cryptol.Utils.Ident as C

import Cryptol.Utils.Ident (Ident, preludeName, arrayName, preludeReferenceName
                           , mkIdent, interactiveName, identText
                           , textToModName
                           , prelPrim)
import Cryptol.Utils.Logger (quietLogger)

import qualified CryptolSAWCore.Pretty as CryPP
--import SAWScript.REPL.Monad (REPLException(..))
import CryptolSAWCore.TypedTerm
import Cryptol.ModuleSystem.Env (ModContextParams(NoParams))
-- import SAWCentral.AST (Located(getVal, locatedPos), Import(..))

---- Key Types -----------------------------------------------------------------

-- | Input to send to Cryptol's parser, including the starting source position.
data InputText = InputText
  { inpText :: Text   -- ^ Parse this
  , inpFile :: String -- ^ It came from this file (or thing)
  , inpLine :: Int    -- ^ On this line number
  , inpCol  :: Int    -- ^ On this column number
  }


-- Finding things --------------------------------------------------------------


-- | Look up a name in a map containing Cryptol names.
--
-- The string corresponds to the Cryptol name we are looking for.
--
-- If it is unqualifed, then we return any entry associated with the given
-- name.  If the string is qualified (i.e., has @::@), then we only consider
-- entries from the module named by the qualification.
--
-- The result is either the corresponding value, or a list of the candidate
-- fully-qualified names.
--
lookupIn :: Text -> Map T.Name b -> Either [T.Name] b
lookupIn nm mp =
  case [ x | x <- Map.toList mp, matches (fst x) ] of
    [ (_,v) ] -> Right v
    opts      -> Left (map fst opts)
  where
  matches = nameMatcher nm


-- | Parse a string into a function that will match Cryptol names.
--
-- If the string is unqualified (i.e., no `::`), then we match all
-- names with the given identifier.  Otherwise, we only match the
-- ones in the module specified by the qualification.
--
-- The first argument is the name we're looking for; the second
-- argument (or the first argument of the returned function, in the
-- intended usage) is a candidate name to match.
nameMatcher :: Text -> T.Name -> Bool
nameMatcher nm0 =
    case C.modNameChunksText (textToModName nm0) of
      []  -> const False
      [x] -> (x ==) . C.identText . MN.nameIdent
      cs  -> \n ->
                case MN.nameInfo n of
                  MN.LocalName {} -> False
                  MN.GlobalName _ og ->
                    let (top,ns) = C.modPathSplit (C.ogModule og)
                    in last cs == identText (C.ogName og) &&
                       init cs == C.modNameChunksText top ++ map identText ns


-- Initialize ------------------------------------------------------------------

-- | initCryptolEnv - Create initial CryptolEnv. This involves loading
--   the built-in modules (preludeName, arrayName,
--   preludeReferenceName) and translating them into SAWCore, and
--   putting them into scope.
--
--   NOTE: submodules in these built-in modules are supported in this code.
--
initCryptolEnv ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> IO CryptolEnv
initCryptolEnv sc = do
  modEnv0 <- M.initialModuleEnv

  -- Set the Cryptol include path (TODO: we may want to do this differently)
  (binDir, _) <- splitExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  mCryptolPath <- lookupEnv "CRYPTOLPATH"
  let cryptolPaths =
        case mCryptolPath of
          Nothing -> []
          Just path ->
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
            -- Windows paths search from end to beginning
            reverse (splitSearchPath path)
#else
            splitSearchPath path
#endif
  let modEnv1 = modEnv0 { ME.meSearchPath = cryptolPaths ++
                           (instDir </> "lib") : ME.meSearchPath modEnv0 }

  -- Load Cryptol prelude and magic Array module
  (_, modEnv2) <-
    liftModuleM modEnv1 $
      do _ <- MB.loadModuleFrom False (MM.FromModule preludeName)
         _ <- MB.loadModuleFrom False (MM.FromModule arrayName)
         return ()

  -- Load Cryptol reference implementation
  ((_,refTop), modEnv3) <-
    liftModuleM modEnv2 $
      MB.loadModuleFrom False (MM.FromModule preludeReferenceName)
  let refMod = T.tcTopEntityToModule refTop

  -- Set up reference implementation redirections
  let refDecls = T.mDecls refMod
  let nms = Set.toList (MI.ifsPublic (TIface.genIfaceNames refMod))

  let refPrims = Map.fromList
                  [ (prelPrim (identText (MN.nameIdent nm)), T.EWhere (T.EVar nm) refDecls)
                  | nm <- nms ]

  -- The module names in P.Import are now Located, so give them an empty position.
  let preludeName'          = locatedUnknown preludeName
      preludeReferenceName' = locatedUnknown preludeReferenceName
      arrayName'            = locatedUnknown arrayName

  let env0 = CryptolEnv
        { eImports    =
            [ mkImport OnlyPublic preludeName'          Nothing Nothing
            , mkImport OnlyPublic preludeReferenceName' (Just preludeReferenceName) Nothing
            , mkImport OnlyPublic arrayName'            Nothing Nothing
            ]
        , eModuleEnv  = modEnv3
        , eExtraNaming = mempty
        , eExtraVars  = Map.empty
        , eExtraTySyns = Map.empty
        , eAllVars    = Map.empty
        , eTyVars     = Map.empty
        , eTyProps    = Map.empty
        , eAllTerms   = Map.empty
        , eRefPrims   = refPrims
        , ePrims      = Map.empty
        , ePrimTypes  = Map.empty
        , eFFITypes   = Map.empty
        }

  -- Generate SAWCore translations for all values in scope
  env1 <- genTermEnv sc modEnv3 env0

  -- Clear `eRefPrims`. This preserves the behavior from before
  -- `CryptolEnv` and the old additional `Env` type were merged. It
  -- isn't clear if this is correct or not, but I don't want the code
  -- cleanup to change the behavior.
  return env1 {
      eRefPrims = Map.empty
  }


-- | Translate all declarations in all loaded modules to SAWCore terms.
--   NOTE: used only for initialization code.
--
genTermEnv :: SharedContext -> ME.ModuleEnv -> C.CryptolEnv -> IO C.CryptolEnv
genTermEnv sc modEnv env0 = do
  let declGroups = concatMap T.mDecls
                 $ filter (not . T.isParametrizedModule)
                 $ ME.loadedModules modEnv
      nominals   = loadedNonParamNominalTypes modEnv
  -- These update eAllTerms and eAllVars and leave the rest alone
  env1 <- C.genCodeForNominalTypes sc nominals env0
  env2 <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions env1 declGroups
  return env2


-- Parse -----------------------------------------------------------------------

-- | Parse a Cryptol expression.
ioParseExpr :: InputText -> IO (P.Expr P.PName)
ioParseExpr = ioParseGeneric P.parseExprWith

-- | Parse Cryptol declarations.
ioParseDecls :: InputText -> IO [P.Decl P.PName]
ioParseDecls = ioParseGeneric P.parseDeclsWith

-- | Parse a Cryptol type scheme.
ioParseSchema :: InputText -> IO (P.Schema P.PName)
ioParseSchema = ioParseGeneric P.parseSchemaWith

-- | Support function that handles the input to the Cryptol parser
--   entry points.
ioParseGeneric ::
  (P.Config -> Text -> Either P.ParseError a) -> InputText -> IO a
ioParseGeneric parse inp = ioParseResult (parse cfg str)
  where
  cfg = P.defaultConfig { P.cfgSource = inpFile inp }
  -- XXX this is kind of gross; maybe sometime we get a second parser
  -- entry point that takes a start position... (this is saw-script #2175)
  str = Text.concat [ Text.replicate (inpLine inp - 1) "\n"
                    , Text.replicate (inpCol inp - 1) " "
                    , inpText inp ]

-- | Support function that prints Cryptol parse errors.
ioParseResult :: Either P.ParseError a -> IO a
ioParseResult res = case res of
  Right a -> return a
  Left e  -> fail $ "Cryptol parse error:\n" ++ show (P.ppError e) -- X.throwIO (ParseError e)


-- NamingEnv and Related -------------------------------------------------------

-- | Get the full 'MR.NamingEnv' based on all the imports (from
--   `eImports`), plus all the local "extra" decls too. Note that the
--   imports are combined with `mconcat`, which uses the `Semigroup`
--   instance for `MR.NamingEnv` to ambiguate any names that appear
--   more than once, but the "extra" decls are (specifically) bolted
--   on with `MR.shadowing` so they hide any previous occurrences.
--
--   Note that while `eImports` is (mostly) maintained with more
--   recent imports at the front of the list, this should be
--   irrelevant to name resolution.
--
getNamingEnv :: CryptolEnv -> MR.NamingEnv
getNamingEnv env =
  eExtraNaming env
  `MR.shadowing`
  (mconcat $ map (getNamingEnvForImport (eModuleEnv env))
                 (eImports env)
  )

-- | Get the `MR.NamingEnv` for one `T.Import`.
getNamingEnvForImport :: ME.ModuleEnv
                      -> (ImportVisibility, T.Import)
                      -> MR.NamingEnv
getNamingEnvForImport modEnv (vis, imprt) =
    MN.interpImportEnv imprt -- adjust for qualified imports
  $ computeNamingEnv lm vis

  where
  modName :: C.ModName
  modName = P.thing $ T.iModule imprt

  lm = case ME.lookupModule modName modEnv of
         Just lm' -> lm'
         Nothing  -> panic "getNamingEnvForImport"
                       ["cannot lookupModule: " <> CryPP.pp modName]

-- | Compute a `MR.NamingEnv` for a module based on the
--   `ImportVisibility`.
computeNamingEnv :: ME.LoadedModule -> ImportVisibility -> MR.NamingEnv
computeNamingEnv lm vis =
  case vis of
    PublicAndPrivate -> envPublicAndPrivate  -- all names defined, pub & pri
    OnlyPublic       -> envPublic            -- i.e., what's exported.

  where
  -- NamingEnvs: --

    -- | envTopLevels
    --    - Does not include privates in submodules (which makes for
    --      much of the complications of this function).
    --    - Includes everything in scope at the toplevel of 'lm' module
    envTopLevels :: MR.NamingEnv
    envTopLevels = ME.lmNamingEnv lm

    -- | envPublicAndPrivate - awkward as envTopLevels excludes privates
    envPublicAndPrivate :: MR.NamingEnv
    envPublicAndPrivate =
       -- nab all the names defined in module (from toplevel scope):
       MN.filterUNames (`Set.member` nmsDefined) envTopLevels
       <>
       -- we must create a new NamingEnv (since the privates are not
       -- in `envTopLevels`):
       MN.namingEnvFromNames' MN.nameToPNameWithQualifiers nmsPrivate

    envPublic :: MR.NamingEnv
    envPublic = MN.filterUNames
                  (`Set.member` nmsPublic)
                  envTopLevels

  -- Name Sets: --

    -- | names in scope at Top level of module
    nmsTopLevels :: Set MN.Name
    nmsTopLevels = MN.namingEnvNames envTopLevels

    -- | names defined in module and in submodules
    --   - this includes `PublicAndPrivate` names!
    --   - includes submodule names, type synonyms, and nominal types
    nmsDefined :: Set MN.Name
    nmsDefined =
        -- definitions from all submodules:
        ( Set.unions
        $ map (MI.ifsDefines . T.smIface)
        $ Map.elems
        $ T.mSubmodules
        $ ME.lmModule lm
        )
      `Set.union`
        -- definitions at the top module:
        (MI.ifsDefines $ MI.ifNames $ ME.lmInterface lm)


    nmsPublic :: Set MN.Name
    nmsPublic = MI.ifsPublic $ MI.ifNames $ ME.lmInterface lm

    nmsPrivate :: Set MN.Name
    nmsPrivate = nmsDefined Set.\\ nmsTopLevels

-- | Like Cryptol's 'ME.loadedNominalTypes', except that it only returns
-- nominal types from non-parameterized modules, which are currently the only
-- types of modules that SAW can import.
loadedNonParamNominalTypes :: ME.ModuleEnv -> Map MN.Name T.NominalType
loadedNonParamNominalTypes menv =
  Map.unions $
    map (MI.ifNominalTypes . MI.ifDefines . ME.lmInterface)
        (ME.lmLoadedModules (ME.meLoadedModules menv))

-- Typecheck -------------------------------------------------------------------

-- | Process a `TM.InferOutput` (typechecker result) and return a
--   `MM.ModuleM` action.
runInferOutput :: TM.InferOutput a -> MM.ModuleM a
runInferOutput out =
  case out of

    TM.InferOK nm warns seeds supply o ->
      do MM.setNameSeeds seeds
         MM.setSupply supply
         MM.typeCheckWarnings nm warns
         return o

    TM.InferFailed nm warns errs ->
      do MM.typeCheckWarnings nm warns
         MM.typeCheckingFailed nm errs


---- Misc Exports --------------------------------------------------------------

-- | Restore a `CryptolEnv` from a checkpoint. The first argument
--   @chkEnv@ is the `CryptolEnv` saved by / copied into the
--   checkpoint; the second argument @newEnv@ is the current one
--   we wish to overwrite by rolling back to the checkpoint.
--
--   We need to keep the newer name supply so as to not reuse names
--   already issued, in case some of those are still floating around
--   after the restore. (They should not... but bugs happen.)
--
--   We also ought to invalidate terms constructed since the checkpoint
--   was taken, like SAWCore does. See #2859.
--
restoreCryptolEnv :: CryptolEnv -> CryptolEnv -> CryptolEnv
restoreCryptolEnv chkEnv newEnv =
    let newMEnv = eModuleEnv newEnv
        chkMEnv = eModuleEnv chkEnv
        menv' = chkMEnv { ME.meNameSeeds = ME.meNameSeeds newMEnv }
    in
    chkEnv { eModuleEnv = menv' }


---- Types and functions for CryptolModule & ExtCryptolModule ------------------


-- | ExtCryptolModule - Extended CryptolModule; we keep track of
--   whether this module came directly from a constructed
--   `CryptolModule` or whether it came from parsing a Cryptol module
--   from filesystem (in which case it is loaded).
--
data ExtCryptolModule =
    -- | source is parsed/loaded
    ECM_LoadedModule
        (P.Located C.ModName)
        PPS.Doc      -- ^ how we show this on SAWScript CLI.

    -- | source is internal/constructed (e.g., via cryptol_prims)
  | ECM_CryptolModule  CryptolModule

-- | Create the print string for an `ExtCryptolModule`, as used e.g.
--   by the REPL or by the SAWScript @print@ function.
--
--  - FIXME: This function, with the ECM_LoadedModule constructor, are
--      a bit ad hoc!  Currently `ExtCryptolModule` is exposed to the
--      CLI *and* requires a way to show this type to the user (as
--      implemented here) to support the user interface.  As the state
--      isn't available when we want to display this value, we compute
--      the "display" String when we construct `ExtCryptolModule` values.
--
--      The best solution is to implement Issue #2680 (Add `:cbrowse`) in
--      order to both improve the user interface and remove this awkward code.
--      Implementing #2680 will also address Issue #2700.
--
--  - Update: this is still problematic but now it's at least a ppdoc
--    and not a string. Note that it uses PPS.Doc (wired to the
--    SAWCore annotations) rather than a generic `PP.Doc ann` because
--    we're storing the doc in the `ExtCryptolModule` and making it
--    polymorphic there creates pointless complications.
--
-- There's no longer any barrier to passing this function the `CryptolEnv`
-- to extract information from.
--
-- Also note: `prettyCryptolModule` lives in @TypedTerm@, but is only used
-- from this file and should probably be moved here.
--
prettyExtCryptolModule :: ExtCryptolModule -> PPS.Doc
prettyExtCryptolModule =
  \case
    ECM_LoadedModule name doc ->
      -- Cryptol's prettyprinter is not compatible with ours
      let name' = CryPP.pretty (P.thing name) in
      "Loaded module" <+> PP.squotes name' <> ":" <> PP.hardline <> doc
    ECM_CryptolModule cm  ->
      PP.vsep [
          "Internal module:",
          prettyCryptolModule cm
      ]

-- | loadExtCryptolModule - load a cryptol module and return the
-- `ExtCryptolModule`.  The contents of the module are not directly
-- imported into the environment.
--
-- This is used to implement the @cryptol_load@ primitive in which a
-- handle to the module is returned and can be bound to a SAWScript
-- variable.
--
-- NOTE: Bringing the module into {{-}} scope is not handled
--       here; it is done rather in `bindExtCryptolModule`, ONLY if the
--       user binds the `CryptolModule` returned here at the SAW
--       command line.
loadExtCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext ->
  CryptolEnv ->
  FilePath ->
  IO (ExtCryptolModule, CryptolEnv)
loadExtCryptolModule sc env path =
  do
  (m, env') <- loadAndTranslateModule sc env (Left path)
  let doc = PP.vsep [
              "Public interface",
              prettyCryptolModule (mkCryptolModule m env')
          ]
          -- How to show, need to compute this here, because the show function
          -- (of course) has no access to the state.
          --
          -- FIXME: Since the complete public and private interface is
          -- extractable, we should show the whole thing with public,
          -- private, typesyns, constructors, submodules.
          -- See Issue #2700
          --
          -- FUTURE: there's no remaining barrier to giving
          -- prettyCryptolModule access to whatever state it wants.
  return (ECM_LoadedModule (locatedUnknown (T.mName m)) doc, env')


-- | loadCryptolModule - load a Cryptol module and return a handle to it
--
-- NOTE RE CALLS TO THIS:
--  - There is only one path to this function from the command line,
--    and it is only via the experimental command,
--      "write_rocq_cryptol_module".
--  - It is also used from crux-mir-comp.
--
-- XXX: probably those callers should be updated to instead use
-- loadExtCryptolModule, at which point this code can be dropped.
--
-- This function (note `mkCryptolModule`) returns the public types and values
-- of the module in a `CryptolModule` structure.
--
loadCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext ->
  CryptolEnv ->
  FilePath ->
  IO (CryptolModule, CryptolEnv)
loadCryptolModule sc env path =
  do
  (mod', env') <- loadAndTranslateModule sc env (Left path)
  return (mkCryptolModule mod' env', env')


-- | mkCryptolModule m env - translate a @m :: T.Module@ to a `CryptolModule`
--
-- This function returns the public types and values of the module @m@
-- as a `CryptolModule` structure.
--
-- This is used in two places: in `loadCryptolModule`, which is a
-- legacy code path that would ideally be removed, and in
-- `loadExtCryptolModule` as part of generating the print output.
-- Ideally all of this could be consolidated.
--
mkCryptolModule :: T.Module -> CryptolEnv -> CryptolModule
mkCryptolModule m env =
  let
      ifaceDecls = C.getAllIfaceDecls (eModuleEnv env)
      types = Map.map MI.ifDeclSig (MI.ifDecls ifaceDecls)
      -- we're keeping only the exports of `m`:
      vNameSet = MEx.exported C.NSValue (T.mExports m)
      tNameSet = MEx.exported C.NSType  (T.mExports m)
  in
      CryptolModule
        -- create Map of type synonyms:
        (Map.filterWithKey
           (\k _ -> Set.member k tNameSet)
           (T.mTySyns m)
        )

        -- create Map of the `TypedTerm` s:
        ( Map.filterWithKey (\k _ -> Set.member k vNameSet)
        $ Map.intersectionWith
             (\t x -> TypedTerm (TypedTermSchema t) x)
             types
             (eAllTerms env)
        )

-- | bindExtCryptolModule - add extra bindings to the Cryptol
--     environment {{-}}; this happens when an `ExtCryptolModule` is
--     bound in the SAWScript code.  (This may be referred to as a
--     "magic bind").
--
--     The code that does this in the SAWScript interpreter is in
--     @extendEnv@, which currently lives in Value.hs.
--
--   NOTE RE CALLS TO THIS: Three SAWScript variants get us here:
--
--      > D <- cryptol_load "PATH"
--
--    which results in a call to `bindLoadedModule`.
--    And each of these
--
--      > x <- return (cryptol_prims ())
--      > let x = cryptol_prims ()
--
--    will result in calling `bindCryptolModule`.
--
-- NOTE:
--  - The `ExtCryptolModule` datatype and these functions are a bit
--    ad hoc.
--  - Ideally thse would go away with further improvements to the
--    external interface and corresponding implementation changes.
--    - See #2569.
--    - Re `bindCryptolModule` below
--      - It is more general than what is needed.
--      - It is somewhat duplicating functionality that we already have with
--        `importCryptolModule`, this could go away in the future.
--
--  - See also the discusion of the SAWScript-level @cryptol_load@ in
--    @CHANGES.md@.
--
bindExtCryptolModule ::
  (P.ModName, ExtCryptolModule) -> CryptolEnv -> CryptolEnv
bindExtCryptolModule (modName, ecm) =
  case ecm of
    ECM_CryptolModule cm   -> bindCryptolModule (modName, cm)
    ECM_LoadedModule  nm _ -> bindLoadedModule  (modName, nm)

-- | bindLoadedModule - when we have a @cryptol_load@ created object,
-- add the module into the import list.
bindLoadedModule ::
  (P.ModName, P.Located C.ModName) -> CryptolEnv -> CryptolEnv
bindLoadedModule (asName, origName) env =
  env {eImports = mkImport PublicAndPrivate origName (Just asName) Nothing
                : eImports env
      }

-- | Undo `bindLoadedModule`. Not a general removal function. Not
--  exported, and used exactly once below where we want to add a
--  module to the import list temporarily.
unbindLoadedModule :: CryptolEnv -> CryptolEnv
unbindLoadedModule env =
  env { eImports = pop (eImports env) }
  where
     pop (_ : imports) = imports
     pop [] = panic "unbindLoadedModule" ["Nothing here"]

-- | bindCryptolModule - when we have the @cryptol_prims ()@ created
--   object, add the `CryptolModule` to the relevant maps in the
--   `CryptolEnv` See `bindExtCryptolModule` above.
--
--   Note that this stuffs the module contents in as "extra"
--   declarations, which can be subtly different from importing it,
--   e.g. in the presence of overlapping names. This is only used for
--   @cryptol_prims@, and when we eventually manage to figure out how
--   to handle that stuff better / more like a real module (#2645), it
--   can and should be removed.
--
bindCryptolModule :: (P.ModName, CryptolModule) -> CryptolEnv -> CryptolEnv
bindCryptolModule (modName, CryptolModule sm tm) env =
  env { eExtraNaming = flip (foldr addName) (Map.keys tm') $
                      flip (foldr addTSyn) (Map.keys sm) $
                      eExtraNaming env
      , eExtraTySyns = Map.union sm (eExtraTySyns env)
      , eExtraVars  = Map.union (fmap fst tm') (eExtraVars env)
      , eAllTerms   = Map.union (fmap snd tm') (eAllTerms env)
      }
  where
    -- | `tm'` is the typed terms from `tm` that have Cryptol schemas
    tm' = Map.mapMaybe f tm
          where
          f (TypedTerm (TypedTermSchema s) x) = Just (s,x)
          f _                                 = Nothing

    addName name =
      MN.shadowing
       (MN.singletonNS C.NSValue (P.mkQual modName (MN.nameIdent name)) name)

    addTSyn name =
      MN.shadowing
        (MN.singletonNS C.NSType (P.mkQual modName (MN.nameIdent name)) name)


-- | @extractDefFromExtCryptolModule sc en ecm name@:
--   interpret @name@ as a definition in the module @ecm@, and return
--   the TypedTerm.
--
--  NOTE RE CALLS TO THIS: this is (only) used for the
--  @cryptol_extract@ primitive.
--
--  Also note that @cryptol_extract mod "name"@ is not supposed to be
--  different from just writing @{{ mod::name }}@. We should be able
--  to look the name up that way and not have to invent a temporary
--  fake @import qualified@ module name to insert and use for lookup.
--  XXX: look into this. (As a bonus, this would also allow dropping
--  `unbindLoadedModule`.)
--
extractDefFromExtCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> ExtCryptolModule -> Text -> IO (TypedTerm, CryptolEnv)
extractDefFromExtCryptolModule sc env_0 ecm name =
  case ecm of
    ECM_LoadedModule loadedModName _ ->
        do let localMN = C.packModName
                           [ "INTERNAL_EXTRACT_MODNAME"
                           , C.modNameToText (P.thing loadedModName)
                           ]
               -- Temporarily insert the module into the imports list
               env_1    = bindLoadedModule (localMN, loadedModName) env_0
               expr    = noLoc (C.modNameToText localMN <> "::" <> name)
           (tt, env_2) <- parseTypedTerm sc env_1 expr
           let env_3 = unbindLoadedModule env_2
           pure (tt, env_3)

           -- FIXME: error message for bad `name` exposes the
           --   `localMN` to user.  Fixing locally is challenging, as
           --   the error is not an exception we can handle here.
    ECM_CryptolModule (CryptolModule _ tm) ->
        case Map.lookup (mkIdent name) (Map.mapKeys MN.nameIdent tm) of
          Just t  -> return (t, env_0)
          Nothing -> fail $ Text.unpack $ "Binding not found: " <> name

        -- NOTE RE CALLS TO THIS:
        --   - currently we can only get to this branch when CryptolModule
        --     is the one created with `cryptol_prims` (Haskell function and
        --     SAWScript function).  E.g.,
        --
        --     > cryptol_extract (cryptol_prims ()) "trunc"
        --
        -- FIXME: this code is somewhat ad hoc; might we rather invoke
        -- parse for name or the like?  However, this code should become
        -- unnecessary after addressing Issue #2645 (turning
        -- cryptol_prims into a built-in Cryptol module).

---- Core functions for loading and Translating Modules ------------------------

-- | Load a Cryptol module and translate its contents to SAWCore.
--
-- There are three paths here:
--    - `importCryptolModule`, which is the back end for SAWScript @import@
--    - `loadExtCryptolModule`, which is the back end for SAWScript @cryptol_load@
--    - `loadCryptolModule`, which is used for Rocq export and from crux-mir-comp
--
-- These can probably be unified.
--
loadAndTranslateModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext             {- ^ Shared context for creating terms -} ->
  CryptolEnv                {- ^ Extend this environment -} ->
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  IO (T.Module, CryptolEnv)
loadAndTranslateModule sc env0 src =
  do let modEnv = eModuleEnv env0
     (mtop, modEnv') <- liftModuleM modEnv $
       case src of
         Left path -> MB.loadModuleByPath True path
         Right mn  -> snd <$> MB.loadModuleFrom True (MM.FromModule mn)
     m <- case mtop of
            T.TCTopModule mod'  -> pure mod'
            T.TCTopSignature {} ->
              fail $
                "Expected a module, but "
                ++ (case src of
                      Left  path -> show path
                      Right mn   -> Text.unpack (CryPP.pp mn)
                   )
                ++ " is an interface."

     checkNotParameterized m
     let env1 = env0 { eModuleEnv = modEnv' }

     -- Regenerate SharedTerm environment:
     let oldModNames   = map ME.lmName
                       $ ME.lmLoadedModules
                       $ ME.meLoadedModules modEnv
         isNew m'      = T.mName m' `notElem` oldModNames
         newModules    = filter isNew
                       $ map ME.lmModule
                       $ ME.lmLoadedModules
                       $ ME.meLoadedModules modEnv'
         newDeclGroups = concatMap T.mDecls newModules
         newNominal    = Map.difference (loadedNonParamNominalTypes modEnv')
                                        (loadedNonParamNominalTypes modEnv)

     env2 <- C.refreshCryptolEnv env1

     -- These update eAllTerms and eAllVars and leave the rest alone
     env3 <- C.genCodeForNominalTypes sc newNominal env2
     env4 <- C.importTopLevelDeclGroups
                        sc C.defaultPrimitiveOptions env3 newDeclGroups

     ffiTypes' <- updateFFITypes sc m (eAllTerms env4) (eFFITypes env4)
     let env5 = env4 { eFFITypes  = ffiTypes' }

     return (m, env5)

-- | Reject unapplied functors.
checkNotParameterized :: T.Module -> IO ()
checkNotParameterized m =
  when (T.isParametrizedModule m) $
    fail $ unlines [ "Cannot load parameterized modules directly."
                   , "Either use a ` import, or make a module instantiation."
                   ]

-- | Helper for updating `eFFITypes` in `CryptolEnv`.
updateFFITypes ::
  SharedContext ->
  T.Module ->
  Map MN.Name Term ->
  Map NameInfo T.FFI ->
  IO (Map NameInfo T.FFI)
updateFFITypes sc m allTerms' eFFITypes' = do
  let getNameInfo (nm, ty) = do
        let tm = case Map.lookup nm allTerms' of
              Just tm' -> tm'
              Nothing ->
                  panic "updateFFITypes" [
                      "Cannot find foreign function in term environment: " <>
                          CryPP.pp nm
                  ]
        info <- case asConstant tm of
              Just n ->
                pure $ nameInfo n
              Nothing -> do
                tm' <- ppTerm sc tm
                panic "updateFFITypes" [
                    "SAWCore term of Cryptol name is not a Constant",
                    "Name: " <> CryPP.pp nm,
                    "Term: " <> Text.pack tm'
                 ]
        pure $ (info, ty)
  decls <- mapM getNameInfo (T.findForeignDecls m)
  pure $ foldr (\(info, ty) decl -> Map.insert info ty decl) eFFITypes' decls


---- import --------------------------------------------------------------------

-- | @'importCryptolModule' sc env src as vis imps@ - extend the Cryptol
--   environment with a module.  Backend for SAWScript @import@.
--
-- NOTE:
--  - the module can be qualified or not (per @as@ argument).
--  - per @vis@ we can import public definitions or *all* (i.e., internal
--    and public) definitions.

importCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext             {- ^ Shared context for creating terms -} ->
  CryptolEnv                {- ^ Extend this environment -} ->
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  Maybe P.ModName           {- ^ Name qualifier -} ->
  ImportVisibility          {- ^ What visibility to give symbols from this module -} ->
  Maybe P.ImportSpec        {- ^ What to import -} ->
  IO CryptolEnv
importCryptolModule sc env src as vis imps =
  do
  (mod', env') <- loadAndTranslateModule sc env src
  let import' = mkImport vis (locatedUnknown (T.mName mod')) as imps
  return $ env' {eImports = import' : eImports env }

-- | Create an entry for the `eImports` list in `CryptolEnv`.
mkImport :: ImportVisibility
         -> P.Located C.ModName
         -> Maybe C.ModName
         -> Maybe T.ImportSpec
         -> (ImportVisibility, T.Import)
mkImport vis nm as imps =
    let im = P.Import { T.iModule = nm
                      , T.iAs     = as
                      , T.iSpec   = imps
                      , T.iInst   = Nothing
                      , T.iDoc    = Nothing
                      }
    in
    (vis, im)


---- Binding -------------------------------------------------------------------

-- | Prepare an identifier for adding to the Cryptol environment.
--   May update the name supply.
--
--   XXX: @bind@ is the wrong name for this; it doesn't bind anything
--   itself.
--
--   XXX: should probably be unified with `declareName`.
--
bindIdent :: Ident -> CryptolEnv -> (T.Name, CryptolEnv)
bindIdent ident env = (name, env')
  where
    modEnv = eModuleEnv env
    supply = ME.meSupply modEnv
    fixity = Nothing
    (name, supply') = MN.mkDeclared
                        C.NSValue
                        (C.TopModule interactiveName)
                        MN.UserName
                        ident fixity P.emptyRange supply
    modEnv' = modEnv { ME.meSupply = supply' }
    env' = env { eModuleEnv = modEnv' }

-- | Add a new variable as an "extra" declaration.
bindExtraVar :: (Ident, TypedTerm) -> CryptolEnv -> CryptolEnv
bindExtraVar (ident, TypedTerm (TypedTermSchema schema) trm) env =
  env' { eExtraNaming = MR.shadowing (MN.singletonNS C.NSValue pname name)
                                    (eExtraNaming env)
       , eExtraVars = Map.insert name schema (eExtraVars env)
       , eAllTerms  = Map.insert name trm (eAllTerms env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env

-- Only bind terms that have Cryptol schemas.
--
-- XXX: this should probably fail instead. Silently ignoring
-- inappropriate attempts is a policy more appropriate for the
-- caller. (Although there are enough callers that this warrants
-- some thought before jumping.)
bindExtraVar _ env = env

-- | Like `bindExtraVar` but temporary within a passed-in operation.
--
--   That is, it adds a new variable as an "extra" declaration while
--   running the passed in @op@ on the `CryptolEnv`, then drops it
--   again, preserving unrelated changes to the `CryptolEnv`.
--
--   XXX: This will come unstuck if the wrapped operation touches
--   XXX: `eExtraNaming`, `eExtraVars`, or `eAllTerms`. We need a
--   XXX: better way to do this; however, there's no way to undo
--   XXX: `MR.shadowing` so there aren't many choices.
--
--   The right way to do this is probably to extend `CryptolEnv` to
--   support scopes, and then to have the caller create a temporary
--   scope and use `bindExtraVar`. (Scope support should happen
--   anyway. Right now the SAWScript interpreter creates stacks of
--   environments to handle scopes, which was an ad hoc solution to an
--   immediate need, isn't the right way, and creates its own
--   problems.)
--
withExtraVar ::
    (Ident, TypedTerm) ->
    CryptolEnv ->
    (CryptolEnv -> IO (a, CryptolEnv)) ->
    IO (a, CryptolEnv)
withExtraVar (ident, TypedTerm (TypedTermSchema schema) trm) env_0 op = do
  -- Note: bindIdent only updates the name supply, arguably it is misnamed
  let (name, env_1) = bindIdent ident env_0

  -- Extract the original state
  let naming_1 = eExtraNaming env_1
      extravars_1 = eExtraVars env_1
      allterms_1 = eAllTerms env_1

  -- Generate an updated state and a working environment
  let pname = P.mkUnqual ident
      naming_2 = MR.shadowing (MN.singletonNS C.NSValue pname name) naming_1
      extravars_2 = Map.insert name schema extravars_1
      allterms_2 = Map.insert name trm allterms_1
  let env_2 = env_1 {
        eExtraNaming = naming_2,
        eExtraVars = extravars_2,
        eAllTerms = allterms_2
      }

  -- Call the op
  (ret, env_3) <- op env_2

  -- Restore the original state
  let env_4 = env_3 {
        eExtraNaming = naming_1,
        eExtraVars = extravars_1,
        eAllTerms = allterms_1
      }

  -- done
  pure (ret, env_4)

-- Maybe this should panic. The caller presumably meant it to do
-- something, so it'd be a mistake if they passed in a binding that
-- can't be made visible.
withExtraVar _ env_0 op =
  op env_0

-- | Add a new type synonym as an "extra" declaration.
--
-- XXX: this should probably fail on inappropriate types; silently
-- ignoring them is a policy decision more appropriate for the caller.
--
bindTySyn :: (Ident, T.Schema) -> CryptolEnv -> CryptolEnv
bindTySyn (ident, T.Forall [] [] ty) env =
  env' { eExtraNaming = MR.shadowing (MN.singletonNS C.NSType pname name) (eExtraNaming env)
       , eExtraTySyns = Map.insert name tysyn (eExtraTySyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] ty Nothing
bindTySyn _ env = env -- only monomorphic types may be bound

-- | Add a new Cryptol integer type as an "extra" declration.
bindIntegerType :: (Ident, Integer) -> CryptolEnv -> CryptolEnv
bindIntegerType (ident, n) env =
  env' { eExtraNaming = MR.shadowing (MN.singletonNS C.NSType pname name) (eExtraNaming env)
       , eExtraTySyns = Map.insert name tysyn (eExtraTySyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] (T.tNum n) Nothing


--------------------------------------------------------------------------------

-- | Produce a `TM.SolverConfig`.
--
-- XXX: Why is this exported? Calling into the Cryptol typechecker
-- seems like it should be restricted to this file, or at least belong
-- to cryptol-saw-core, and not be splattered all over everywhere.
--
meSolverConfig :: ME.ModuleEnv -> TM.SolverConfig
meSolverConfig env = TM.defaultSolverConfig (ME.meSearchPath env)


-- | Look up an identifier in the Cryptol environment and return its
--   full name.
resolveIdentifier ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> Text -> IO (Maybe T.Name)
resolveIdentifier env nm =
  case splitOn (pack "::") nm of
    []  -> pure Nothing
           -- FIXME: shouldn't this be error?
    [i] -> doResolve (P.mkUnqual (C.mkIdent i))
    xs  -> let (qs,i) = (init xs, last xs)
           in  doResolve (P.Qual (C.packModName qs) (C.mkIdent i))
    -- FIXME: Is there no function that parses Text into PName?

  where
  modEnv = eModuleEnv env
  nameEnv = getNamingEnv env

  doResolve pnm =
    -- Note: this throws away the potentially-updated state returned
    -- by MM.runModuleM. However, it should really not have changed
    -- anything, and as of this writing does not, so we'll leave it
    -- like this. It would be more robust to not throw the state away;
    -- maybe at some point in the future it will be less awkward to
    -- keep it.
    SMT.withSolver (return ()) (meSolverConfig modEnv) $ \solver ->
    do let minp = MM.ModuleInput {
               MM.minpCallStacks = True,
               MM.minpSaveRenamed = False,
               MM.minpEvalOpts = pure defaultEvalOpts,
               MM.minpByteReader = ?fileReader,
               MM.minpModuleEnv = modEnv,
               MM.minpTCSolver = solver
           }
       (res, _ws) <- MM.runModuleM minp $
          MM.interactive (MB.rename interactiveName nameEnv (MR.renameVar MR.NameUse pnm))
       case res of
         Left _ -> pure Nothing
         Right (x,_) -> pure (Just x)

-- | Read a Cryptol expression from `InputText` and return it as a
--   `TypedTerm`.
parseTypedTerm ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO (TypedTerm, CryptolEnv)
parseTypedTerm sc env input = do
  -- Parse:
  pexpr <- ioParseExpr input
  -- Translate:
  pExprToTypedTerm sc env pexpr

-- | Convert a parsed Cryptol expression to a `TypedTerm`. Runs the
--   typechecker.
--
-- This is exported because there's a place that constructs Cryptol
-- parser AST for subsequent use, which is more robust (and more
-- efficient) than printing to text and parsing the text.
--
pExprToTypedTerm ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> P.Expr P.PName -> IO (TypedTerm, CryptolEnv)
pExprToTypedTerm sc env pexpr = do
  let modEnv = eModuleEnv env

  ((expr, schema), modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns:
    npe <- MM.interactive (MB.noPat pexpr)

    let nameEnv = getNamingEnv env
    let npe' = MR.rename npe
    re <- MM.interactive (MB.rename interactiveName nameEnv npe')
      -- NOTE: if a name is not in scope, it is reported here.

    -- Infer types
    let ifDecls = C.getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc re)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraVars env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTySyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }

  -- Translate
  trm <- C.translateExpr sc env' expr
  return (TypedTerm (TypedTermSchema schema) trm, env')

-- | Read Cryptol declarations from `InputText` and ingest them into
--   the `CryptolEnv`.
parseDecls ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO CryptolEnv
parseDecls sc env input = do
  let modEnv = eModuleEnv env
  let ifaceDecls = C.getAllIfaceDecls modEnv

  -- Parse
  (decls :: [P.Decl P.PName]) <- ioParseDecls input

  (tmodule, modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    (npdecls :: [P.Decl P.PName]) <- MM.interactive (MB.noPat decls)

    -- Expand PropGuards
    epgDecls <- case P.runExpandPropGuardsM (concat <$> mapM P.expandDecl npdecls) of
      Left err -> MM.expandPropGuardsError err
      Right e' -> pure e'

    -- Convert from 'Decl' to 'TopDecl' so that types will be generalized
    let topdecls = [ P.Decl (P.TopLevel P.Public Nothing d) | d <- epgDecls ]

    -- Resolve names
    (_nenv, rdecls) <- MM.interactive (MB.rename interactiveName (getNamingEnv env) (MR.renameTopDecls interactiveName topdecls))

    -- Create a Module to contain the declarations
    let rmodule = P.Module { P.mName = locatedUnknown interactiveName
                           , P.mDef  = P.NormalModule rdecls
                           , P.mInScope = mempty
                           , P.mDocTop = Nothing
                           }

    -- Infer types
    let range = fromMaybe P.emptyRange (P.getLoc rdecls)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifaceDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraVars env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTySyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (TM.runInferM tcEnv' (TI.inferTopModule rmodule))
    tmodule <- MM.interactive (runInferOutput out)
    m <- case tmodule of
           T.TCTopModule m -> pure m
           T.TCTopSignature {} ->
              fail "Expected a module, but found an interface."
    return m

  -- Add new type synonyms and their name bindings to the environment
  let syns' = Map.union (eExtraTySyns env) (T.mTySyns tmodule)
  let addName name = MR.shadowing (MN.singletonNS C.NSType (P.mkUnqual (MN.nameIdent name)) name)
  let naming' = foldr addName (eExtraNaming env) (Map.keys (T.mTySyns tmodule))
  let env' = env { eModuleEnv = modEnv', eExtraNaming = naming', eExtraTySyns = syns' }

  -- Translate
  let dgs = T.mDecls tmodule
  C.translateDeclGroups sc env' dgs

-- | Read a Cryptol type scheme from `InputText`.
parseSchema ::
  (?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> InputText -> IO (T.Schema, CryptolEnv)
parseSchema env input = do
  let modEnv = eModuleEnv env

  -- Parse
  pschema <- ioParseSchema input

  (schema, modEnv') <- liftModuleM modEnv $ do

    -- Resolve names
    let nameEnv = getNamingEnv env
    rschema <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename pschema))

    let ifDecls = C.getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc rschema)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpTSyns = Map.union (eExtraTySyns env) (TM.inpTSyns tcEnv) }
    let infer =
          case rschema of
            P.Forall [] [] t _ -> do
              let k = Nothing -- allow either kind KNum or KType
              (t', goals) <- TM.collectGoals $ TK.checkType t k
              return (T.Forall [] [] t', goals)
            _ -> TK.checkSchema TM.AllowWildCards rschema
    out <- MM.io (TM.runInferM tcEnv' infer)
    (schema, _goals) <- MM.interactive (runInferOutput out)
    --mapM_ (MM.io . print . TP.ppWithNames TP.emptyNameMap) goals
    return (schemaNoUser schema)

  let env' = env { eModuleEnv = modEnv' }
  return (schema, env')

-- | Prepare an identifier for adding to the Cryptol environment.
--   May update the name supply.
--
--   XXX: much the same as, and should probably be unified with, `bindIdent`.
--
declareName ::
  (?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> P.ModName -> Text -> IO (T.Name, CryptolEnv)
declareName env mname input = do
  let pname = P.mkUnqual (mkIdent input)
  let modEnv = eModuleEnv env
  (cname, modEnv') <-
    liftModuleM modEnv $ MM.interactive $
    MN.liftSupply (MN.mkDeclared C.NSValue (C.TopModule mname) MN.UserName (P.getIdent pname) Nothing P.emptyRange)
  let env' = env { eModuleEnv = modEnv' }
  return (cname, env')

-- | Remove type synonym annotations from a Cryptol type.
--
--   (After typechecking, type aliases are expanded, but the original
--   name is left in place as a wrapper for printing purposes.)
--
typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts     -> T.TCon tc (map typeNoUser ts)
    T.TVar {}        -> t
    T.TUser _ _ ty   -> typeNoUser ty
    T.TRec fields    -> T.TRec (fmap typeNoUser fields)
    T.TNominal nt ts -> T.TNominal nt (fmap typeNoUser ts)

-- | Remove type synonym annotations from a Cryptol type scheme.
schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)


---- Local Utility Functions ---------------------------------------------------

-- | An `InputText` representing no particular place
noLoc :: Text -> InputText
noLoc x = InputText
            { inpText = x
            , inpFile = "(internalUse)"
            , inpLine = 1
            , inpCol  = 1
            }


-- | Make a value `P.Located` with a placeholder position.
--
-- XXX: it would be better to have the real position, but it
-- seems to have been thrown away on the Cryptol side in the uses
-- of this function.
locatedUnknown :: a -> P.Located a
locatedUnknown x = P.Located P.emptyRange x

-- | Run a `MM.ModuleM` (Cryptol module environment monad)
--   computation.
--
-- XXX: misnamed, it's not a lift, it's a run.
liftModuleM ::
 (?fileReader :: FilePath -> IO ByteString) =>
  ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m =
  do let minp solver = MM.ModuleInput {
             MM.minpCallStacks = True,
             MM.minpSaveRenamed = False,
             MM.minpEvalOpts = pure defaultEvalOpts,
             MM.minpByteReader = ?fileReader,
             MM.minpModuleEnv = env,
             MM.minpTCSolver = solver
         }
     SMT.withSolver (return ()) (meSolverConfig env) $ \solver ->
       MM.runModuleM (minp solver) m >>= moduleCmdResult


-- | Default `E.EvalOpts` for evaluating Cryptol.
defaultEvalOpts :: E.EvalOpts
defaultEvalOpts = E.EvalOpts quietLogger E.defaultPPOpts

-- | Process an `M.ModuleRes` (result of a `MM.ModuleM` computation)
--   Print errors and warnings.
--
--   Suppress warnings about defaulting types.
--
moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (warnN' . CryPP.pretty) (concatMap suppressDefaulting ws)
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> errX' $ "Cryptol:" <+> CryPP.pretty err
  where
    -- If all warnings are about type defaults, pretend there are no warnings at
    -- all to avoid displaying an empty warning container.
    suppressDefaulting :: MM.ModuleWarning -> [MM.ModuleWarning]
    suppressDefaulting w =
      case w of
        MM.RenamerWarnings xs -> [MM.RenamerWarnings xs]
        MM.TypeCheckWarnings nm xs ->
          case filter (notDefaulting . snd) xs of
            [] -> []
            xs' -> [MM.TypeCheckWarnings nm xs']

    notDefaulting :: TE.Warning -> Bool
    notDefaulting (TE.DefaultingTo {}) = False
    notDefaulting _ = True
