{- |
Module      : CryptolSAWCore.CryptolEnv
Description : Context for interpreting Cryptol within SAW-Script.
License     : BSD3
Maintainer  : huffman
Stability   : provisional

This module contains (most of) the code for managing the Cryptol
environment and also some of the logic for importing into SAWCore.

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

-- base & standard modules:
import           Control.Monad(when)
import           Data.ByteString (ByteString)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text, pack, splitOn)
import           GHC.Stack
import           System.Environment (lookupEnv)
import           System.Environment.Executable (splitExecutablePath)
import           System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

-- pretty-printer pkg:
import qualified Prettyprinter as PP
import           Prettyprinter ((<+>))

-- cryptol pkg:
import qualified Cryptol.Eval as E
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Env as ME
import           Cryptol.ModuleSystem.Env (ModContextParams(NoParams))
import qualified Cryptol.ModuleSystem.Exports as MEx
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.ModuleSystem.Name      as MN
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Renamer as MR
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.ExpandPropGuards as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Error as TE
import qualified Cryptol.TypeCheck.Infer as TI
import qualified Cryptol.TypeCheck.Interface as TIface
import qualified Cryptol.TypeCheck.Kind as TK
import qualified Cryptol.TypeCheck.Monad as TM
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import qualified Cryptol.Utils.Ident as C
import           Cryptol.Utils.Ident
                           ( Ident, preludeName, arrayName, preludeReferenceName
                           , mkIdent, interactiveName, identText
                           , textToModName
                           , prelPrim)
import           Cryptol.Utils.Logger (quietLogger)

-- local:
import qualified CryptolSAWCore.Cryptol as C
import           CryptolSAWCore.GlobalCryptolEnv
import           CryptolSAWCore.Panic
import qualified CryptolSAWCore.Pretty as CryPP
import           CryptolSAWCore.TypedTerm
import           SAWCore.Name (nameInfo)
import           SAWCore.Recognizer (asConstant)
import           SAWCore.SharedTerm (NameInfo, SharedContext, Term, ppTerm)
import           SAWSupport.Console
import qualified SAWSupport.Pretty as PPS


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
  modEnv0 <- ME.initialModuleEnv

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
  setModuleEnv sc modEnv3

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

  let env0 = C.mapImports (\_ ->
            [ mkImport OnlyPublic preludeName'          Nothing Nothing
            , mkImport OnlyPublic preludeReferenceName' (Just preludeReferenceName) Nothing
            , mkImport OnlyPublic arrayName'            Nothing Nothing
            ]) $ C.initEnv
  C.addRefPrims sc refPrims
  -- Generate SAWCore translations for all values in scope
  genTermEnv sc
  return env0


-- | Translate all declarations in all loaded modules to SAWCore terms.
--   NOTE: used only for initialization code.
--
genTermEnv :: SharedContext -> IO ()
genTermEnv sc = do
  modEnv <- eModuleEnv sc
  let declGroups = concatMap T.mDecls
                 $ filter (not . T.isParametrizedModule)
                 $ ME.loadedModules modEnv
      nominals   = loadedNonParamNominalTypes modEnv
  -- These update eAllTerms and eAllVars and leave the rest alone
  C.genCodeForNominalTypes sc nominals
  C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions declGroups


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
--   all `sImports` in the scope stack),
--   plus all the local "extra" decls too.
--   At each scoping level, the imports are combined with `mconcat`,
--   which uses the `Semigroup`
--   instance for `MR.NamingEnv` to ambiguate any names that appear
--   more than once. The "extra" declarations are then (specifically) bolted
--   on with `MR.shadowing` so they hide any imported occurrences.
--   The environment for each scoping level then shadows everything
--   above it.

--
--   Note that while each `sImports` is (mostly) maintained with more
--   recent imports at the front of the list, this should be
--   irrelevant to name resolution.
--

getNamingEnv :: SharedContext -> CryptolEnv -> IO MR.NamingEnv
getNamingEnv sc env = do
  modEnv <- eModuleEnv sc
  return $ eExtraNaming env
    `MR.shadowing`
    (mconcat $ map (getNamingEnvForImport modEnv)
                  (eImports env)
    )

-- | Get the `MR.NamingEnv` for one `T.Import`.
getNamingEnvForImport :: ME.ModuleEnv
                      -> (ImportVisibility, T.Import)
                      -> MR.NamingEnv
getNamingEnvForImport modEnv (vis, imprt) =
    MN.interpImportEnv'
      MN.nameToPNameWithQualifiers (T.iAs imprt) (T.iSpec imprt)
         -- adjusting for qualified imports
  $ MN.namingEnvNames
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
--  - FIXME: This function, with the ECM_LoadedModule constructor, is
--      quite ad hoc!  Currently `ExtCryptolModule` is exposed to the
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
  FilePath ->
  IO ExtCryptolModule
loadExtCryptolModule sc path =
  do
  m <- loadAndTranslateModule sc (Left path)
  cm <- mkCryptolModule sc m
  let doc = PP.vsep [
              "Public interface",
              prettyCryptolModule cm
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
  return (ECM_LoadedModule (locatedUnknown (T.mName m)) doc)


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
  FilePath ->
  IO (CryptolModule)
loadCryptolModule sc path =
  do
  mod' <- loadAndTranslateModule sc (Left path)
  mkCryptolModule sc mod'


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
mkCryptolModule :: SharedContext -> T.Module -> IO CryptolModule
mkCryptolModule sc m = do
  modEnv <- eModuleEnv sc
  allterms <- eAllTerms sc
  let
      ifaceDecls = C.getAllIfaceDecls modEnv
      types = Map.map MI.ifDeclSig (MI.ifDecls ifaceDecls)
      -- we're keeping only the exports of `m`:
      vNameSet = MEx.exported C.NSValue (T.mExports m)
      tNameSet = MEx.exported C.NSType  (T.mExports m)
  return $
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
             allterms
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
  SharedContext -> (P.ModName, ExtCryptolModule) -> CryptolEnv -> IO CryptolEnv
bindExtCryptolModule sc (modName, ecm) =
  case ecm of
    ECM_CryptolModule cm   -> bindCryptolModule sc (modName, cm)
    ECM_LoadedModule  nm _ -> bindLoadedModule sc (modName, nm)

-- | bindLoadedModule - when we have a @cryptol_load@ created object,
-- add the module into the import list.
bindLoadedModule ::
  SharedContext -> (P.ModName, P.Located C.ModName) -> CryptolEnv -> IO CryptolEnv
bindLoadedModule _ (asName, origName) env = 
  return $ C.mapImports 
    ((:) (mkImport PublicAndPrivate origName (Just asName) Nothing)) env

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
bindCryptolModule :: SharedContext -> (P.ModName, CryptolModule) -> CryptolEnv -> IO CryptolEnv
bindCryptolModule sc (modName, CryptolModule sm tm) env0 = do
  addExtraTySyns sc sm
  addExtraVars sc (fmap fst tm')
  addAllTerms sc (fmap snd tm')
  return $ C.mapNaming (flip (foldr addName) (Map.keys tm') .
               flip (foldr addTSyn) (Map.keys sm)) env0
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
  SharedContext -> CryptolEnv -> ExtCryptolModule -> Text -> IO TypedTerm
extractDefFromExtCryptolModule sc env_0 ecm name =
  case ecm of
    ECM_LoadedModule loadedModName _ ->
        do let localMN = C.packModName
                           [ "INTERNAL_EXTRACT_MODNAME"
                           , C.modNameToText (P.thing loadedModName)
                           ]
               -- Temporarily insert the module into the imports list
           env_1 <- bindLoadedModule sc (localMN, loadedModName) env_0
           let expr    = noLoc (C.modNameToText localMN <> "::" <> name)
           tt <- parseTypedTerm sc env_1 expr
           pure tt

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
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  IO T.Module
loadAndTranslateModule sc src =
  do modEnv <- eModuleEnv sc
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
     setModuleEnv sc modEnv'

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

     -- These update eAllTerms and eAllVars and leave the rest alone
     C.genCodeForNominalTypes sc newNominal
     C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions newDeclGroups
     allterms <- eAllTerms sc
     ffiTypes <- eFFITypes sc

     ffiTypes' <- updateFFITypes sc m allterms ffiTypes
     addFFITypes sc ffiTypes'

     return m

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
--
importCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext             {- ^ Shared context for creating terms -} ->
  CryptolEnv                {- ^ Extend this environment -} ->
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  Maybe P.ModName           {- ^ Name qualifier -} ->
  Bool                      {- ^ isSubmodule: True if 'import submodule ...' -} ->
  ImportVisibility          {- ^ What visibility to give symbols from this module -} ->
  Maybe P.ImportSpec        {- ^ What to import -} ->
  IO CryptolEnv
importCryptolModule sc env src as False vis imps =
  -- importing full module:
  do
  mod' <- loadAndTranslateModule sc src
  let import' = mkImport vis (locatedUnknown (T.mName mod')) as imps
  return $ C.mapImports ((:) import') env
importCryptolModule _sc _env (Right __nm) _as True _vis _imps =
  -- importing submodule by name:
  -- FIXME: this will be implemented in #2618 (soon).
  fail $ "`import submodule` is unsupported."
importCryptolModule _sc _env (Left _)  _as True _vis _imps =
  -- importing submodule by FilePath: disallowed:
  fail $ "`import submodule PATHNAME` is not allowed."
     -- NOTE: this is allowed by parser (thus we can get here).
     -- FIXME: Would we want to implement this check in the typechecker?

-- | Create an entry for the `eImports` list in `CryptolEnv`.
mkImport :: ImportVisibility
         -> P.Located C.ModName
         -> Maybe C.ModName
         -> Maybe T.ImportSpec
         -> (ImportVisibility, T.Import)
mkImport vis nm as imps =
    let im = T.Import { T.iModule = nm
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
bindIdent :: SharedContext -> Ident -> IO T.Name
bindIdent sc ident = withModEnvSupply sc $ \supply ->
  let
    fixity = Nothing
    (name, supply') = MN.mkDeclared
                        C.NSValue
                        (C.TopModule interactiveName)
                        MN.UserName
                        ident fixity P.emptyRange supply
  in (name, supply')

-- | Add a new variable as an "extra" declaration.
bindExtraVar :: SharedContext -> (Ident, TypedTerm) -> CryptolEnv -> IO CryptolEnv
bindExtraVar sc (ident, TypedTerm (TypedTermSchema schema) trm) env0 = do
  name <- bindIdent sc ident
  let pname = P.mkUnqual ident
  addExtraVars sc (Map.singleton name schema) 
  addAllTerms sc (Map.singleton name trm)
  return $ C.mapNaming (MR.shadowing $ MN.singletonNS C.NSValue pname name) env0

-- Only bind terms that have Cryptol schemas.
--
-- XXX: this should probably fail instead. Silently ignoring
-- inappropriate attempts is a policy more appropriate for the
-- caller. (Although there are enough callers that this warrants
-- some thought before jumping.)
bindExtraVar _ _ env = pure env

-- | Like `bindExtraVar` but temporary within a passed-in operation.
--
--   That is, it adds a new variable as an "extra" declaration while
--   running the passed in @op@ on the `CryptolEnv`, then drops it
--   out of scope, preserving unrelated changes to the `CryptolEnv`.
--

withExtraVar ::
    SharedContext ->
    (Ident, TypedTerm) ->
    CryptolEnv ->
    (CryptolEnv -> IO (a, CryptolEnv)) ->
    IO (a, CryptolEnv)
withExtraVar sc b env0 op = withFreshScope env0 $ \env1 -> do
  env2 <- bindExtraVar sc b env1
  op env2

-- | Add a new type synonym as an "extra" declaration.
--
-- XXX: this should probably fail on inappropriate types; silently
-- ignoring them is a policy decision more appropriate for the caller.
--
bindTySyn :: SharedContext -> (Ident, T.Schema) -> CryptolEnv -> IO CryptolEnv
bindTySyn sc (ident, T.Forall [] [] ty) env = do
  name <- bindIdent sc ident
  let tysyn = T.TySyn name [] [] ty Nothing
  addExtraTySyns sc (Map.singleton name tysyn)
  let pname = P.mkUnqual ident
  return $ C.mapNaming (MR.shadowing (MN.singletonNS C.NSType pname name)) env
  
bindTySyn _ _ env = pure env -- only monomorphic types may be bound

-- | Add a new Cryptol integer type as an "extra" declration.
bindIntegerType :: SharedContext -> (Ident, Integer) -> CryptolEnv -> IO CryptolEnv
bindIntegerType sc (ident, n) env = do
  name <- bindIdent sc ident
  let tysyn = T.TySyn name [] [] (T.tNum n) Nothing
  addExtraTySyns sc (Map.singleton name tysyn)
  let pname = P.mkUnqual ident
  return $ C.mapNaming (MR.shadowing (MN.singletonNS C.NSType pname name)) env

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
  SharedContext -> CryptolEnv -> Text -> IO (Maybe T.Name)
resolveIdentifier sc env nm = do
  case splitOn (pack "::") nm of
    []  -> pure Nothing
           -- FIXME: shouldn't this be error?
    [i] -> doResolve (P.mkUnqual (C.mkIdent i))
    xs  -> let (qs,i) = (init xs, last xs)
           in  doResolve (P.Qual (C.packModName qs) (C.mkIdent i))
    -- FIXME: Is there no function that parses Text into PName?

  where

  doResolve pnm = do
    modEnv <- eModuleEnv sc
    nameEnv <- getNamingEnv sc env
    -- Note: this throws away the potentially-updated state returned
    -- by MM.runModuleM. However, it should really not have changed
    -- anything, and as of this writing does not, so we'll leave it
    -- like this. It would be more robust to not throw the state away;
    -- maybe at some point in the future it will be less awkward to
    -- keep it.
    SMT.withSolver (return ()) (meSolverConfig modEnv) $ \solver -> do
       let minp = MM.ModuleInput {
               MM.minpCallStacks = True,
               MM.minpSaveRenamed = False,
               MM.minpEvalOpts = pure defaultEvalOpts,
               MM.minpByteReader = ?fileReader,
               MM.minpModuleEnv = modEnv,
               MM.minpTCSolver = solver
           }
       (res, _ws) <- MM.runModuleM minp $
          MM.interactive (MB.rename interactiveName nameEnv
                                    (MR.resolveNameUse C.NSValue pnm)
                         )
       case res of
         Left _ -> pure Nothing
         Right (x,_) -> pure (Just x)

-- | Read a Cryptol expression from `InputText` and return it as a
--   `TypedTerm`.
parseTypedTerm ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO TypedTerm
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
  SharedContext -> CryptolEnv -> P.Expr P.PName -> IO TypedTerm
pExprToTypedTerm sc env pexpr = do
  modEnv <- eModuleEnv sc
  nameEnv <- getNamingEnv sc env
  extraVars <- eExtraVars sc
  extraTySyns <- eExtraTySyns sc

  ((expr, schema), modEnv') <- liftModuleM modEnv $ do
    -- Eliminate patterns:
    npe <- MM.interactive (MB.noPat pexpr)

    
    let npe' = MR.rename npe
    re <- MM.interactive (MB.rename interactiveName nameEnv npe')
      -- NOTE: if a name is not in scope, it is reported here.

    -- Infer types
    let ifDecls = C.getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc re)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union extraVars (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union extraTySyns (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  setModuleEnv sc modEnv'

  -- Translate
  trm <- C.translateExpr sc expr
  return (TypedTerm (TypedTermSchema schema) trm)

-- | Read Cryptol declarations from `InputText` and ingest them into
--   the `CryptolEnv`.
parseDecls ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO CryptolEnv
parseDecls sc env input = do
  modEnv <- eModuleEnv sc
  namingEnv <- getNamingEnv sc env
  extraVars <- eExtraVars sc
  extraTySyns <- eExtraTySyns sc
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
    (_nenv, rdecls) <- MM.interactive
        (MB.rename interactiveName
                   namingEnv
                   (MR.renameTopDecls topdecls)
        )

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
    let tcEnv' = tcEnv { TM.inpVars = Map.union extraVars (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union extraTySyns (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (TM.runInferM tcEnv' (TI.inferTopModule rmodule))
    tmodule <- MM.interactive (runInferOutput out)
    m <- case tmodule of
           T.TCTopModule m -> pure m
           T.TCTopSignature {} ->
              fail "Expected a module, but found an interface."
    return m

  -- Add new type synonyms and their name bindings to the environment
  let addName name = MR.shadowing (MN.singletonNS C.NSType (P.mkUnqual (MN.nameIdent name)) name)
  setModuleEnv sc modEnv'
  addExtraTySyns sc (T.mTySyns tmodule)
  let env' = C.mapNaming (\ne -> foldr addName ne (Map.keys (T.mTySyns tmodule))) env

  -- Translate
  let dgs = T.mDecls tmodule
  C.translateDeclGroups sc env' dgs

-- | Read a Cryptol type scheme from `InputText`.
parseSchema ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO T.Schema
parseSchema sc env input = do
  modEnv <- eModuleEnv sc
  nameEnv <- getNamingEnv sc env
  extraTySyns <- eExtraTySyns sc

  -- Parse
  pschema <- ioParseSchema input

  (schema, modEnv') <- liftModuleM modEnv $ do

    -- Resolve names
    rschema <- MM.interactive
             $ MB.rename interactiveName nameEnv
                (MR.renameSchema pschema pure)

    let ifDecls = C.getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc rschema)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims NoParams ifDecls
    let tcEnv' = tcEnv { TM.inpTSyns = Map.union extraTySyns (TM.inpTSyns tcEnv) }
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

  setModuleEnv sc modEnv'
  return schema

-- | Prepare an identifier for adding to the Cryptol environment.
--   May update the name supply.
--
--   XXX: much the same as, and should probably be unified with, `bindIdent`.
--
declareName ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> P.ModName -> Text -> IO T.Name
declareName sc mname input = do
  let pname = P.mkUnqual (mkIdent input)
  modEnv <- eModuleEnv sc
  (cname, modEnv') <-
    liftModuleM modEnv $ MM.interactive $
    MN.liftSupply (MN.mkDeclared C.NSValue (C.TopModule mname) MN.UserName (P.getIdent pname) Nothing P.emptyRange)
  setModuleEnv sc modEnv'
  return cname

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
