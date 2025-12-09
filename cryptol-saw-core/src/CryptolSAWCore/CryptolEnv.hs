{- |
Module      : CryptolSAWCore.CryptolEnv
Description : Context for interpreting Cryptol within SAW-Script.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CryptolSAWCore.CryptolEnv
  ( ImportVisibility(..)
  , CryptolEnv(..)

  , ExtCryptolModule(..)
  , showExtCryptolModule
  , initCryptolEnv
  , loadCryptolModule
  , loadExtCryptolModule
  , bindExtCryptolModule

  , extractDefFromExtCryptolModule
  , combineCryptolEnv
  , importCryptolModule
  , bindTypedTerm
  , bindType
  , bindInteger
  , parseTypedTerm
  , pExprToTypedTerm
  , parseDecls
  , parseSchema
  , declareName
  , typeNoUser
  , schemaNoUser
  , translateExpr
  , getNamingEnv
  , getAllIfaceDecls
  , InputText(..)
  , lookupIn
  , resolveIdentifier
  , meSolverConfig
  , mkCryEnv
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

import qualified SAWSupport.Pretty as PPS

import CryptolSAWCore.Panic
import SAWCore.Name (nameInfo)
import SAWCore.Recognizer (asConstant)
import SAWCore.SharedTerm (NameInfo, SharedContext, Term)
import SAWCore.Term.Pretty (ppTermPureDefaults)

import qualified CryptolSAWCore.Cryptol as C

import qualified Cryptol.Eval as E
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
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

import Cryptol.Utils.PP hiding ((</>))
import Cryptol.Utils.Ident (Ident, preludeName, arrayName, preludeReferenceName
                           , mkIdent, interactiveName, identText
                           , textToModName
                           , prelPrim)
import Cryptol.Utils.Logger (quietLogger)

--import SAWScript.REPL.Monad (REPLException(..))
import CryptolSAWCore.TypedTerm
import Cryptol.ModuleSystem.Env (ModContextParams(NoParams))
-- import SAWCentral.AST (Located(getVal, locatedPos), Import(..))

---- Key Types -----------------------------------------------------------------

-- | Parse input, together with information about where it came from.
data InputText = InputText
  { inpText :: Text   -- ^ Parse this
  , inpFile :: String -- ^ It came from this file (or thing)
  , inpLine :: Int    -- ^ On this line number
  , inpCol  :: Int    -- ^ On this column number
  }

-- | 'ImportVisibility' - Should a given import (see 'importCryptolModule')
-- result in all symbols being visible (as they are for focused
-- modules in the Cryptol REPL) or only public symbols?  Making all
-- symbols visible is useful for verification and code generation.
--
-- NOTE: this notion of public vs. private symbols is specific to
-- SAWScript and distinct from Cryptol's notion of private
-- definitions.
--
data ImportVisibility
  = OnlyPublic       -- ^ behaves like a normal Cryptol "import"
  | PublicAndPrivate -- ^ allows viewing of both "private" sections
                     --   and (arbitrarily nested) submodules.
  deriving (Eq, Show)


-- | The environment for capturing the Cryptol interpreter state as well as the
--   SAWCore translations and associated state.
--
data CryptolEnv = CryptolEnv
  { eImports    :: [(ImportVisibility, P.Import)]
                                        -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv         -- ^ Loaded & imported modules, and
                                        --   state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv         -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.Name T.Schema  -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn   -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name Term      -- ^ SAWCore terms for *all* names in scope
  , ePrims      :: Map C.PrimIdent Term -- ^ SAWCore terms for primitives
  , ePrimTypes  :: Map C.PrimIdent Term -- ^ SAWCore terms for primitive type names
  , eFFITypes   :: Map NameInfo T.FFI
                  -- ^ FFI info for SAWCore names of Cryptol foreign functions
  }


-- Finding things --------------------------------------------------------------


-- | Lookup a name in a map containg Cryptol names.
-- The string corresponds to the Cryptol name we are looking for.
-- If it is unqualifed, then we return any entry associated with the given
-- name.  If the string is qualified (i.e., has @::@), then we only consider
-- entries from the module in the qualified.
-- The result is either the corresponding value, or a list of the
lookupIn :: Text -> Map T.Name b -> Either [T.Name] b
lookupIn nm mp =
  case [ x | x <- Map.toList mp, matches (fst x) ] of
    [ (_,v) ] -> Right v
    opts      -> Left (map fst opts)
  where
  matches = nameMatcher nm


-- | Parse a string into a function that will match names.
-- If the string is unqualified (i.e., no `::`), then we match all
-- names with the given identifier.  Otherwise, we only match the
-- ones in the module specified by the qualifier.
nameMatcher :: Text -> T.Name -> Bool
nameMatcher xs =
    case C.modNameChunksText (textToModName xs) of
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

-- | initCryptolEnv - Create initial CryptolEnv, this involves loading
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
  let cryEnv0 = C.emptyEnv { C.envRefPrims = refPrims }

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv3 cryEnv0

  -- The module names in P.Import are now Located, so give them an empty position.
  let preludeName'          = locatedUnknown preludeName
      preludeReferenceName' = locatedUnknown preludeReferenceName
      arrayName'            = locatedUnknown arrayName

  return CryptolEnv
    { eImports    =
        [ mkImport OnlyPublic preludeName'          Nothing Nothing
        , mkImport OnlyPublic preludeReferenceName' (Just preludeReferenceName) Nothing
        , mkImport OnlyPublic arrayName'            Nothing Nothing
        ]
    , eModuleEnv  = modEnv3
    , eExtraNames = mempty
    , eExtraTypes = Map.empty
    , eExtraTSyns = Map.empty
    , eTermEnv    = termEnv
    , ePrims      = Map.empty
    , ePrimTypes  = Map.empty
    , eFFITypes   = Map.empty
    }


-- | Translate all declarations in all loaded modules to SAWCore terms
--   NOTE: used only for initialization code.
--
genTermEnv :: SharedContext -> ME.ModuleEnv -> C.Env -> IO (Map T.Name Term)
genTermEnv sc modEnv cryEnv0 = do
  let declGroups = concatMap T.mDecls
                 $ filter (not . T.isParametrizedModule)
                 $ ME.loadedModules modEnv
      nominals   = loadedNonParamNominalTypes modEnv
  cryEnv1 <- C.genCodeForNominalTypes sc nominals cryEnv0
  cryEnv2 <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions cryEnv1 declGroups
  return (C.envE cryEnv2)


-- Parse -----------------------------------------------------------------------

ioParseExpr :: InputText -> IO (P.Expr P.PName)
ioParseExpr = ioParseGeneric P.parseExprWith

ioParseDecls :: InputText -> IO [P.Decl P.PName]
ioParseDecls = ioParseGeneric P.parseDeclsWith

ioParseSchema :: InputText -> IO (P.Schema P.PName)
ioParseSchema = ioParseGeneric P.parseSchemaWith

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

ioParseResult :: Either P.ParseError a -> IO a
ioParseResult res = case res of
  Right a -> return a
  Left e  -> fail $ "Cryptol parse error:\n" ++ show (P.ppError e) -- X.throwIO (ParseError e)


-- NamingEnv and Related -------------------------------------------------------

-- | @'getNamingEnv' env@ - get the full 'MR.NamingEnv' based on all
-- the imports (@eImports env@).
getNamingEnv :: CryptolEnv -> MR.NamingEnv
getNamingEnv env =
  eExtraNames env
  `MR.shadowing`
  (mconcat $ map (getNamingEnvForImport (eModuleEnv env))
                 (eImports env)
  )

-- | get Naming Env for one Import.
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
                       ["cannot lookupModule: " <> Text.pack(show modName)]

-- | compute the NamingEnv based on the ImportVisibility.
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


getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me =
  mconcat
    (map (MI.ifDefines . ME.lmInterface)
         (ME.getLoadedModules (ME.meLoadedModules me)))

-- | Like Cryptol's 'ME.loadedNominalTypes', except that it only returns
-- nominal types from non-parameterized modules, which are currently the only
-- types of modules that SAW can import.
loadedNonParamNominalTypes :: ME.ModuleEnv -> Map MN.Name T.NominalType
loadedNonParamNominalTypes menv =
  Map.unions $
    map (MI.ifNominalTypes . MI.ifDefines . ME.lmInterface)
        (ME.lmLoadedModules (ME.meLoadedModules menv))

-- Typecheck -------------------------------------------------------------------

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


-- Translate -------------------------------------------------------------------

mkCryEnv ::
  (?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> IO C.Env
mkCryEnv env =
  do let modEnv = eModuleEnv env
     let ifaceDecls = getAllIfaceDecls modEnv
     (types, _) <-
       liftModuleM modEnv $
       do prims <- MB.getPrimMap
          -- noIfaceParams because we don't support translating functors yet
          infInp <- MB.genInferInput P.emptyRange prims NoParams ifaceDecls
          let newtypeCons = Map.fromList
                              [ con
                              | nt <- Map.elems (TM.inpNominalTypes infInp)
                              , con <- T.nominalTypeConTypes nt
                              ]
          pure (newtypeCons `Map.union` TM.inpVars infInp)
     let types' = Map.union (eExtraTypes env) types
     let terms = eTermEnv env
     let cryEnv = C.emptyEnv
           { C.envE = terms
           , C.envC = types'
           , C.envPrims = ePrims env
           , C.envPrimTypes = ePrimTypes env
           }
     return cryEnv

translateExpr ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> T.Expr -> IO Term
translateExpr sc env expr =
  do cryEnv <- mkCryEnv env
     C.importExpr sc cryEnv expr

translateDeclGroups ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> [T.DeclGroup] -> IO CryptolEnv
translateDeclGroups sc env dgs =
  do cryEnv  <- mkCryEnv env
     cryEnv' <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions cryEnv dgs
     let decls = concatMap T.groupDecls dgs
     let names = map T.dName decls
     let newTypes = Map.fromList [ (T.dName d, T.dSignature d) | d <- decls ]
     let addName name = MR.shadowing (MN.singletonNS C.NSValue (P.mkUnqual (MN.nameIdent name)) name)
     return env { eExtraNames = foldr addName (eExtraNames env) names
                , eExtraTypes = Map.union (eExtraTypes env) newTypes
                , eTermEnv    = C.envE cryEnv'
                }

---- Misc Exports --------------------------------------------------------------

combineCryptolEnv :: CryptolEnv -> CryptolEnv -> IO CryptolEnv
combineCryptolEnv chkEnv newEnv =
  do let newMEnv = eModuleEnv newEnv
     let chkMEnv = eModuleEnv chkEnv
     let menv' = chkMEnv { ME.meNameSeeds = ME.meNameSeeds newMEnv }
     return chkEnv { eModuleEnv = menv' }


---- Types and functions for CryptolModule & ExtCryptolModule ------------------


-- | ExtCryptolModule - Extended CryptolModule; we keep track of
--   whether this module came directly from a constructed
--   `CryptolModule` or whether it came from parsing a Cryptol module
--   from filesystem (in which case it is loaded).
--
--
data ExtCryptolModule =
    -- | source is parsed/loaded
    ECM_LoadedModule
        (P.Located C.ModName)
        String      -- ^ how we show this on SAWScript CLI.

    -- | source is internal/constructed (e.g., via cryptol_prims)
  | ECM_CryptolModule  CryptolModule

-- | create the string needed for display in the CLI.
--
--  - FIXME: This function, with the ECM_LoadedModule constructor, are
--    a bit ad hoc!  Currently `ExtCrytpolModule` is exposed to the
--    CLI *and* requires a way to show this type to the user (as
--    implemented here) to support the user interface.  As the state
--    isn't available when we want to display this value, we compute
--    the "display" String when we construct `ExtCryptolModule` values.
--
--    The best solution is to implement Issue #2680 (Add `:cbrowse`) in
--    order to both improve the user interface and remove this awkward code.
--    Implementing #2680 will also address Issue #2700.
--
showExtCryptolModule :: ExtCryptolModule -> String
showExtCryptolModule =
  \case
    ECM_LoadedModule name s ->
      unlines ["Loaded module '" ++ show(pp (P.thing name)) ++ "':"
              , s
              ]
    ECM_CryptolModule cm  ->
      PPS.render PPS.defaultOpts $ PP.vsep [
          "Internal module:",
          prettyCryptolModule cm
      ]

-- | loadCryptolModule - load a cryptol module and return the
-- `ExtCryptolModule`.  The contents of the module are not directly
-- imported into the environment.
--
-- This is used to implement the "cryptol_load" primitive in which a
-- handle to the module is returned and can be bound to a SAWScript
-- variable.
--
-- NOTE: Bringing the module into {{-}} scope is not handled
--       here; it is done rather in `bindExtCryptolModule`, ONLY if the
--       user binds the `cryptolModule` returned here at the SAW
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
  let s = PPS.render PPS.defaultOpts $ PP.vsep [
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
  return (ECM_LoadedModule (locatedUnknown (T.mName m)) s, env')


-- | loadCryptolModule
--
-- NOTE RE CALLS TO THIS:
--  - There is only the path to this function from the command line,
--    and it is only via the experimental command,
--      "write_coq_cryptol_module".
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
-- This function returns the public types and values of the module `m`
-- as a `CryptolModule` structure.
mkCryptolModule :: T.Module -> CryptolEnv -> CryptolModule
mkCryptolModule m env =
  let
      ifaceDecls = getAllIfaceDecls (eModuleEnv env)
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
             (eTermEnv env)
        )

-- | bindExtCryptolModule - add extra bindings to the Cryptol
--     environment {{-}}, this happens when an `ExtCryptolModule` is
--     bound in the SAWScript code.  (This may be referred to as a
--     "magic bind").
--
--   NOTE RE CALLS TO THIS: Three SAWScript variants get us here:
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
--    adhoc.
--  - Ideally thse would go away with further improvements to the
--    external interface and corresponding implementation changes.
--    - See #2569.
--    - Re `bindCryptolModule` below
--      - It is more general than what is needed.
--      - It is somewhat duplicating functionality that we already have with
--        `importCryptolModule`, this could go away in the future.
--
--  - See also the discusion of `cryptol_load` in CHANGES.md.

bindExtCryptolModule ::
  (P.ModName, ExtCryptolModule) -> CryptolEnv -> CryptolEnv
bindExtCryptolModule (modName, ecm) =
  case ecm of
    ECM_CryptolModule cm   -> bindCryptolModule (modName, cm)
    ECM_LoadedModule  nm _ -> bindLoadedModule  (modName, nm)

-- | bindLoadedModule - when we have a `cryptol_load` created object,
-- add the module into the import list.
bindLoadedModule ::
  (P.ModName, P.Located C.ModName) -> CryptolEnv -> CryptolEnv
bindLoadedModule (asName, origName) env =
  env {eImports = mkImport PublicAndPrivate origName (Just asName) Nothing
                : eImports env
      }

-- | bindCryptolModule - when we have a `cryptol_prims ()` created
--   object, add the `CryptolModule` to the relevant maps in the
--   `CryptolEnv` See `bindExtCryptolModule` above.
bindCryptolModule :: (P.ModName, CryptolModule) -> CryptolEnv -> CryptolEnv
bindCryptolModule (modName, CryptolModule sm tm) env =
  env { eExtraNames = flip (foldr addName) (Map.keys tm') $
                      flip (foldr addTSyn) (Map.keys sm) $
                      eExtraNames env
      , eExtraTSyns = Map.union sm (eExtraTSyns env)
      , eExtraTypes = Map.union (fmap fst tm') (eExtraTypes env)
      , eTermEnv    = Map.union (fmap snd tm') (eTermEnv env)
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


-- | extractDefFromExtCryptolModule sc en ecm name - interpret `name` as a definition in
--   the module `ecm`, return the TypedTerm.
--
--  NOTE RE CALLS TO THIS: this is (only) used for the
--  "cryptol_extract" primitive.
--
extractDefFromExtCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> ExtCryptolModule -> Text -> IO TypedTerm
extractDefFromExtCryptolModule sc env ecm name =
  case ecm of
    ECM_LoadedModule loadedModName _ ->
        do let localMN = C.packModName
                           [ "INTERNAL_EXTRACT_MODNAME"
                           , C.modNameToText (P.thing loadedModName)
                           ]
               env'    = bindLoadedModule (localMN, loadedModName) env
               expr    = noLoc (C.modNameToText localMN <> "::" <> name)
           parseTypedTerm sc env' expr

           -- FIXME: error message for bad `name` exposes the
           --   `localMN` to user.  Fixing locally is challenging, as
           --   the error is not an exception we can handle here.
    ECM_CryptolModule (CryptolModule _ tm) ->
        case Map.lookup (mkIdent name) (Map.mapKeys MN.nameIdent tm) of
          Just t  -> return t
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

loadAndTranslateModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext             {- ^ Shared context for creating terms -} ->
  CryptolEnv                {- ^ Extend this environment -} ->
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  IO (T.Module, CryptolEnv)
loadAndTranslateModule sc env src =
  do let modEnv = eModuleEnv env
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
                      Right mn   -> show mn
                   )
                ++ " is an interface."

     checkNotParameterized m

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

     newTermEnv <-
       do oldCryEnv <- mkCryEnv env
          cEnv      <- C.genCodeForNominalTypes sc newNominal oldCryEnv
          newCryEnv <- C.importTopLevelDeclGroups
                        sc C.defaultPrimitiveOptions cEnv newDeclGroups
          return (C.envE newCryEnv)

     return ( m
            , env { eModuleEnv = modEnv'
                  , eTermEnv   = newTermEnv
                  , eFFITypes  = updateFFITypes m newTermEnv (eFFITypes env)
                  }
            )

checkNotParameterized :: T.Module -> IO ()
checkNotParameterized m =
  when (T.isParametrizedModule m) $
    fail $ unlines [ "Cannot load parameterized modules directly."
                   , "Either use a ` import, or make a module instantiation."
                   ]

updateFFITypes :: T.Module -> Map MN.Name Term -> Map NameInfo T.FFI -> Map NameInfo T.FFI
updateFFITypes m eTermEnv' eFFITypes' =
  foldr (\(nm, ty) -> Map.insert (getNameInfo nm) ty)
                       eFFITypes'
                       (T.findForeignDecls m)
  where
  getNameInfo nm =
    case Map.lookup nm eTermEnv' of
      Just tm ->
        case asConstant tm of
          Just n -> nameInfo n
          Nothing ->
            panic "updateFFITypes" [
                "SAWCore term of Cryptol name is not Constant",
                "Name: " <> Text.pack (show nm),
                "Term: " <> Text.pack (ppTermPureDefaults tm)
            ]
      Nothing ->
        panic "updateFFITypes" [
            "Cannot find foreign function in term environment: " <> Text.pack (show nm)
        ]


---- import --------------------------------------------------------------------

-- | @'importCryptolModule' sc env src as vis imps@ - extend the Cryptol
--   environment with a module.  Closely mirrors the sawscript command "import".
--
-- NOTE:
--  - the module can be qualified or not (per 'as' argument).
--  - per 'vis' we can import public definitions or *all* (i.e., internal
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

bindTypedTerm :: (Ident, TypedTerm) -> CryptolEnv -> CryptolEnv
bindTypedTerm (ident, TypedTerm (TypedTermSchema schema) trm) env =
  env' { eExtraNames = MR.shadowing (MN.singletonNS C.NSValue pname name)
                                    (eExtraNames env)
       , eExtraTypes = Map.insert name schema (eExtraTypes env)
       , eTermEnv    = Map.insert name trm (eTermEnv env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env

-- Only bind terms that have Cryptol schemas
bindTypedTerm _ env = env


bindType :: (Ident, T.Schema) -> CryptolEnv -> CryptolEnv
bindType (ident, T.Forall [] [] ty) env =
  env' { eExtraNames = MR.shadowing (MN.singletonNS C.NSType pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] ty Nothing
bindType _ env = env -- only monomorphic types may be bound

bindInteger :: (Ident, Integer) -> CryptolEnv -> CryptolEnv
bindInteger (ident, n) env =
  env' { eExtraNames = MR.shadowing (MN.singletonNS C.NSType pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] (T.tNum n) Nothing


--------------------------------------------------------------------------------

meSolverConfig :: ME.ModuleEnv -> TM.SolverConfig
meSolverConfig env = TM.defaultSolverConfig (ME.meSearchPath env)

resolveIdentifier ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> Text -> IO (Maybe T.Name)
resolveIdentifier env nm =
  case splitOn (pack "::") nm of
    []  -> pure Nothing
           -- FIXME: shouldn't this be error?
    [i] -> doResolve (P.UnQual (C.mkIdent i))
    xs  -> let (qs,i) = (init xs, last xs)
           in  doResolve (P.Qual (C.packModName qs) (C.mkIdent i))
    -- FIXME: Is there no function that parses Text into PName?

  where
  modEnv = eModuleEnv env
  nameEnv = getNamingEnv env

  doResolve pnm =
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

parseTypedTerm ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO TypedTerm
parseTypedTerm sc env input = do
  -- Parse:
  pexpr <- ioParseExpr input
  -- Translate:
  pExprToTypedTerm sc env pexpr

pExprToTypedTerm ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> P.Expr P.PName -> IO TypedTerm
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
    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc re)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }

  -- Translate
  trm <- translateExpr sc env' expr
  return (TypedTerm (TypedTermSchema schema) trm)

parseDecls ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO CryptolEnv
parseDecls sc env input = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv

  -- Parse
  (decls :: [P.Decl P.PName]) <- ioParseDecls input

  (tmodule, modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    (npdecls :: [P.Decl P.PName]) <- MM.interactive (MB.noPat decls)

    -- Convert from 'Decl' to 'TopDecl' so that types will be generalized
    let topdecls = [ P.Decl (P.TopLevel P.Public Nothing d) | d <- npdecls ]

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
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (TM.runInferM tcEnv' (TI.inferTopModule rmodule))
    tmodule <- MM.interactive (runInferOutput out)
    m <- case tmodule of
           T.TCTopModule m -> pure m
           T.TCTopSignature {} ->
              fail "Expected a module, but found an interface."
    return m

  -- Add new type synonyms and their name bindings to the environment
  let syns' = Map.union (eExtraTSyns env) (T.mTySyns tmodule)
  let addName name = MR.shadowing (MN.singletonNS C.NSType (P.mkUnqual (MN.nameIdent name)) name)
  let names' = foldr addName (eExtraNames env) (Map.keys (T.mTySyns tmodule))
  let env' = env { eModuleEnv = modEnv', eExtraNames = names', eExtraTSyns = syns' }

  -- Translate
  let dgs = T.mDecls tmodule
  translateDeclGroups sc env' dgs

parseSchema ::
  (?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> InputText -> IO T.Schema
parseSchema env input = do
  let modEnv = eModuleEnv env

  -- Parse
  pschema <- ioParseSchema input

  fmap fst $ liftModuleM modEnv $ do

    -- Resolve names
    let nameEnv = getNamingEnv env
    rschema <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename pschema))

    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc rschema)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv) }
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

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts     -> T.TCon tc (map typeNoUser ts)
    T.TVar {}        -> t
    T.TUser _ _ ty   -> typeNoUser ty
    T.TRec fields    -> T.TRec (fmap typeNoUser fields)
    T.TNominal nt ts -> T.TNominal nt (fmap typeNoUser ts)

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)


---- Local Utility Functions ---------------------------------------------------

noLoc :: Text -> InputText
noLoc x = InputText
            { inpText = x
            , inpFile = "(internalUse)"
            , inpLine = 1
            , inpCol  = 1
            }


locatedUnknown :: a -> P.Located a
locatedUnknown x = P.Located P.emptyRange x
  -- XXX: it would be better to have the real position, but it
  -- seems to have been thrown away on the Cryptol side in the uses
  -- of this function.

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

defaultEvalOpts :: E.EvalOpts
defaultEvalOpts = E.EvalOpts quietLogger E.defaultPPOpts

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (print . pp) (concatMap suppressDefaulting ws)
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> fail $ "Cryptol error:\n" ++ show (pp err) -- X.throwIO (ModuleSystemError err)
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
