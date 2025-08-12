{- |
Module      : CryptolSAWCore.CryptolEnv
Description : Context for interpreting Cryptol within SAW-Script.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CryptolSAWCore.CryptolEnv
  ( ImportVisibility(..)
  , CryptolEnv(..)
  , initCryptolEnv
  , loadCryptolModule
  , bindCryptolModule
  , extractDefFromCryptolModule
  , combineCryptolEnv
  , importModule
  , bindTypedTerm
  , bindType
  , bindInteger
  , parseTypedTerm
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
  , setFocusModule    -- FIXME:MT: remove or make a "full feature"
  )
  where

--import qualified Control.Exception as X
import Data.ByteString (ByteString,readFile)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, splitOn)
import Control.Monad(when)
import GHC.Stack

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable
#endif

import System.Environment (lookupEnv)
import System.Environment.Executable (splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

import CryptolSAWCore.Panic
import SAWCore.Name (ecName)
import SAWCore.Recognizer (asConstant)
import SAWCore.SharedTerm (NameInfo, SharedContext, Term, incVars)
  -- FIXME: `incVars` leaks the De Bruijn representation of Term's!
  --   - Think this is the only function that does. (?)
  --   - It would be desirable to not expose this representation.
import SAWCore.Term.Pretty (showTerm)

import qualified CryptolSAWCore.Cryptol as C

import qualified Cryptol.Eval as E
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.FFI.FFIType as T
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
                           , packIdent, interactiveName, identText
                           , textToModName
                           , prelPrim)
import Cryptol.Utils.Logger (quietLogger)

--import SAWScript.REPL.Monad (REPLException(..))
import CryptolSAWCore.TypedTerm
import Cryptol.ModuleSystem.Env (ModContextParams(NoParams))
-- import SAWCentral.AST (Located(getVal, locatedPos), Import(..))

-- pkg: pretty-show
import Text.Show.Pretty (ppShow) -- FIXME: debugging

debug :: Bool
debug = True

-- | Parse input, together with information about where it came from.
data InputText = InputText
  { inpText :: Text   -- ^ Parse this
  , inpFile :: String -- ^ It came from this file (or thing)
  , inpLine :: Int    -- ^ On this line number
  , inpCol  :: Int    -- ^ On this column number
  }



--------------------------------------------------------------------------------

-- | Should a given import result in all symbols being visible (as they
-- are for focused modules in the Cryptol REPL) or only public symbols?
-- Making all symbols visible is useful for verification and code
-- generation.
data ImportVisibility
  = OnlyPublic
  | PublicAndPrivate
  deriving (Eq, Show)

  -- NOTE: Saw: thus can see multiple modules, and their internals. [cryptol cannot]
  --   -

-- | The environment for capturing the Cryptol interpreter state as well as the
--   SAWCore translations and associated state.
--
--  FIXME[D]: The differences in function between this and the similar
--   C.Env?

data CryptolEnv = CryptolEnv
  { eImports    :: [(ImportVisibility, P.Import)]
     -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv
      -- ^ Imported modules, and state for the ModuleM monad
      --
      -- Invariant: each module in `eModuleEnv` is in the `eImports`
      --  list.  (But the converse is not true, because when we load,
      --  not import, a module it is part of `eModuleEnv` but is not
      --  "imported".)
  , eExtraNames :: MR.NamingEnv
      -- ^ Context for the Cryptol renamer
      --
      -- FIXME:doc: this a "computed field" (a function of other fields)?
      -- FIXME:doc: Or, are these 'eExtra' fields holding what's defined at the CL??
  , eExtraTypes :: Map T.Name T.Schema
      -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn
      -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name Term
      -- ^ SAWCore terms for *all* names in scope

      -- TODO:MT: check if name I want is also in here!!
  , ePrims      :: Map C.PrimIdent Term
      -- ^ SAWCore terms for primitives
  , ePrimTypes  :: Map C.PrimIdent Term
     -- ^ SAWCore terms for primitive type names
  , eFFITypes   :: Map NameInfo T.FFIFunType
     -- ^ FFI info for SAWCore names of Cryptol foreign functions
  }


-- Finding things --------------------------------------------------------------


-- | Lookup a name in a map containg Cryptol names.
-- The string corresponds to the Cryptol name we are looking for.
-- If it is unqualifed, then we return any entry associated with the given
-- name.  If the string is qualified (i.e., has @::@), then we only consider
-- entries from the module in the qualified.
-- The result is either the corresponding value, or a list of the
lookupIn :: String -> Map T.Name b -> Either [T.Name] b
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
nameMatcher :: String -> T.Name -> Bool
nameMatcher xs =
    case C.modNameChunksText (textToModName (pack xs)) of
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

  -- Load Cryptol reference implementations
  ((_,refTop), modEnv3) <-
    liftModuleM modEnv2 $
      MB.loadModuleFrom False (MM.FromModule preludeReferenceName)
  let refMod = T.tcTopEntityToModule refTop

  -- Set up reference implementation redirections
  --  FIXME:MT: what's going on here?
  let refDecls = T.mDecls refMod
  let nms = Set.toList (MI.ifsPublic (TIface.genIfaceNames refMod))

   -- FIXME: assuming we have same "bug" were we to have submodules in prelude. ?
  let refPrims = Map.fromList
                  [ (prelPrim (identText (MN.nameIdent nm)), T.EWhere (T.EVar nm) refDecls)
                  | nm <- nms ]
  let cryEnv0 = C.emptyEnv{ C.envRefPrims = refPrims }

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv3 cryEnv0

  return CryptolEnv
    { eImports    = [ (OnlyPublic, P.Import preludeName Nothing Nothing Nothing Nothing)
                    , (OnlyPublic, P.Import preludeReferenceName (Just preludeReferenceName) Nothing Nothing Nothing)
                    , (OnlyPublic, P.Import arrayName Nothing Nothing Nothing Nothing)
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


-- setFocusModule --------------------------------------------------------------

-- FIXME: just drop this, what you would really want is add/substract from import set.
-- FIXME: really the name you want?
--   MT: source of this code?
setFocusModule :: String -> ME.ModuleEnv -> IO ME.ModuleEnv
setFocusModule modNm me0 =
  case P.parseImpName modNm of
    Nothing      -> error $ "focus, cannot parse module name: " ++ modNm
    Just impName -> do
          let ?fileReader = Data.ByteString.readFile
          (impName',me1)
             <- liftModuleM me0 (MB.renameImpNameInCurrentEnv impName)
          case ME.focusModule impName' me1 of
            Just me2 -> return me2
            Nothing  -> panic "setFocusModule:"
                          ["cannot find" <> Text.pack (show modNm)]

-- FIXME
--  - can this replace next?
--  - add error when you access conflicting name.
--  - more testing.

getNamingEnv2 :: CryptolEnv -> MR.NamingEnv
getNamingEnv2 env =

  eExtraNames env `MR.shadowing` nameEnv

  where
  mods = map importToModImp (eImports env)
  modEnv = eModuleEnv env
  nameEnv = ME.mctxNames $ ME.focusedEnvL mods modEnv

  importToModImp (_,imprt) = P.ImpTop (T.iModule imprt)

-- Rename ----------------------------------------------------------------------
--  FIXME: why ^ "Rename"?  I see we pass the result of this to 'MB.rename'

getNamingEnv :: CryptolEnv -> MR.NamingEnv
getNamingEnv env = eExtraNames env `MR.shadowing` nameEnv
  where
    nameEnv = mconcat $ map addImportToEnv (eImports env)
      {-
      eImports : TODO!
      but note: type T.Import = T.ImportG C.ModName
      -}

    -- FIXME:MT: this feels suspicious
    --   1. outside of the case on `vis`, it's all among Cryptol.ModuleSystem.**
    --      functions:
    --        - which is, wow, very complex.
    --        - and is there code there that does this?

    addImportToEnv :: (ImportVisibility, T.ImportG C.ModName) -> MR.NamingEnv
    addImportToEnv (vis, i) = MN.interpImportEnv i syms

      where
      -- get the LoadedModule:
      nm = T.iModule i
      lm = case ME.lookupModule nm (eModuleEnv env) of
              Just x  -> x
              Nothing -> panic "getNamingEnv"
                           [ "unknown module: " <> Text.pack (show nm)
                           , "(module in `eImports`, not in `eModuleEnv`)"
                           ]

      ifc = MI.ifNames (ME.lmInterface lm)
      syms = MN.namingEnvFromNames $
             case vis of
               OnlyPublic       -> MI.ifsPublic ifc
               PublicAndPrivate -> MI.ifsDefines ifc

      -- BH: not sure anything like this exists in Cryptol REPL
      --  saw - a union of scopes/modules, not just one module.
      --  special name for top-level [interactive] module: then use

getNamingEnvLog :: CryptolEnv -> IO MR.NamingEnv
getNamingEnvLog env =
  do
  nameEnv <- mconcat <$> mapM namingEnvFromImport (eImports env)
  return $ eExtraNames env `MR.shadowing` nameEnv

  where
    namingEnvFromImport :: (ImportVisibility, T.ImportG C.ModName) -> IO MR.NamingEnv
    namingEnvFromImport (vis, imprt) =
      do
      when debug $ do
        putStrLn $ unwords ["\nLOG: namingEnvFromImport",show vis, show imprt]
        putStr "ifc= "; ppIfaceNames ifc
          -- no D::D2::d2 but do I really expect this?
        putStrLn "- LOG: nameEnv0:"; print (pp nameEnv0)
          -- FIXME: ?
        putStrLn "- LOG: nameEnv1:"; print (pp nameEnv1)
          -- FIXME: Aha, has D::D2 but not D::D2::d2
        print $ ppListX "- LOG: subModNames: "
               (Set.toList submodNames)
          -- appears to be whats in scope in the module, thus, not useful.
        putStrLn "LOG: [end namingEnvFromImport]\n"
      return nameEnv1

      -- FIXME: UGH/HUH: no module (ModuleG ) accessible (?) scope, rather
      where
        -- get the LoadedModule:
        nm = T.iModule imprt
        lm = case ME.lookupModule nm (eModuleEnv env) of
                Just x  -> x
                Nothing -> panic "getNamingEnvLog"
                             [ "unknown module: " <> Text.pack (show nm)
                             , "(module in `eImports`, not in `eModuleEnv`)"
                             ]

        ifc :: MI.IfaceNames C.ModName
        ifc = MI.ifNames (ME.lmInterface lm)

        -- | names - include all nested Submodule names
        -- HIA/FIXME
        names :: Set.Set MN.Name
        names = case vis of
                  OnlyPublic       -> MI.ifsPublic ifc
                  PublicAndPrivate -> MI.ifsDefines ifc

        submodNames :: Set.Set MN.Name
        submodNames = genSubmoduleExports (ME.lmModule lm)
          -- FIXME: TODO: add =case vis of ...=

        nameEnv0 :: MR.NamingEnv
        nameEnv0 = MN.namingEnvFromNames (names `Set.union` submodNames)

        -- adjust for qualified, hiding (and in-scope?) (FIXME: poor name)
        nameEnv1 = MN.interpImportEnv imprt nameEnv0
           -- TODO: check into?

        -- FIXME: mtg notes to Refile:
        --   BH: not sure anything like this exists in Cryptol REPL
        --   saw - a union of scopes/modules, not just one module.
        --   idea: special name for top-level [interactive] module: then use that.


-- | Generate all the names in a module that are inside submodules.
--    TODO: ... that are public.
-- compare to Cryptol.TypeCheck.Interface.genModDefines
--   FIXME: this belongs rather in src/Cryptol/TypeCheck/Interface.hs?

genSubmoduleExports :: T.ModuleG name -> Set.Set MN.Name
genSubmoduleExports m = nestedInSet (T.mNested m)
  where
  nestedInSet = Set.unions . map inNested . Set.toList
  inNested x  = case Map.lookup x (T.mSubmodules m) of
                  Just y  -> MI.ifsDefines iface
                               `Set.union` nestedInSet (MI.ifsNested iface)
                             where
                               iface = T.smIface y
                  Nothing -> Set.empty -- must be signature or a functor

--
getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me =
  mconcat
    (map (MI.ifDefines . ME.lmInterface)
         (ME.getLoadedModules (ME.meLoadedModules me)))


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

-- FIXME: Very poor name due to the multiple "cryptol environments" around.
--   We must somehow distinguish (in type names, but in var names, and in func names):
--     - CryptolEnv and C.Env

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
           { C.envE = fmap (\t -> (t, 0)) terms -- FIXME: huh?! DeBruijn??
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
  do cryEnv <- mkCryEnv env
     cryEnv' <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions cryEnv dgs
     termEnv' <- traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv')
                  -- FIXME: debruijn??
     let decls = concatMap T.groupDecls dgs
     let names = map T.dName decls
     let newTypes = Map.fromList [ (T.dName d, T.dSignature d) | d <- decls ]
     let addName name = MR.shadowing (MN.singletonNS C.NSValue (P.mkUnqual (MN.nameIdent name)) name)
     return env
           { eExtraNames = foldr addName (eExtraNames env) names
           , eExtraTypes = Map.union (eExtraTypes env) newTypes
           , eTermEnv = termEnv'
           }

-- | Translate all declarations in all loaded modules to SAWCore terms
genTermEnv :: SharedContext -> ME.ModuleEnv -> C.Env -> IO (Map T.Name Term)
genTermEnv sc modEnv cryEnv0 = do
  let declGroups = concatMap T.mDecls
                 $ filter (not . T.isParametrizedModule)
                 $ ME.loadedModules modEnv
      nominals   = ME.loadedNominalTypes modEnv
  cryEnv1 <- C.genCodeForNominalTypes sc nominals cryEnv0
  cryEnv2 <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions cryEnv1 declGroups
  traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv2)

--------------------------------------------------------------------------------


combineCryptolEnv :: CryptolEnv -> CryptolEnv -> IO CryptolEnv
combineCryptolEnv chkEnv newEnv =
  do let newMEnv = eModuleEnv newEnv
     let chkMEnv = eModuleEnv chkEnv
     let menv' = chkMEnv{ ME.meNameSeeds = ME.meNameSeeds newMEnv }
     return chkEnv{ eModuleEnv = menv' }


checkNotParameterized :: T.Module -> IO ()
checkNotParameterized m =
  when (T.isParametrizedModule m) $
    fail $ unlines [ "Cannot load parameterized modules directly."
                   , "Either use a ` import, or make a module instantiation."
                   ]

-- FIXME: Code duplication, these two functions are highly similar
--  - loadCryptolModule
--  - importModule
-- TODO:
--   - determine if these are correctly (vs. accidentally) dissimilar
--      - handling prims differently
--      - returned CryptolEnv's are subtly different for the two.
--      - import _ as X
--   - obvious differences
--      - return of CryptolModule
--   - common up the common code

-- | loadCryptolModule - load a cryptol module and return a handle to
-- the `CryptolModule`.  The contents of the module are not imported.
--
-- This is used to implement the "cryptol_load" primitive in which a
-- handle to the module is returned and can be bound to a sawscript
-- variable.

loadCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext ->
  C.ImportPrimitiveOptions ->
  CryptolEnv ->
  FilePath ->
  IO (CryptolModule, CryptolEnv)
loadCryptolModule sc primOpts env path = do
  let modEnv = eModuleEnv env
  (mtop, modEnv') <- liftModuleM modEnv (MB.loadModuleByPath True path)
  m <- case mtop of
         T.TCTopModule mod' -> pure mod'
         T.TCTopSignature {} ->
            fail $ "Expected a module, but " ++ show path ++ " is an interface."
  checkNotParameterized m

  let ifaceDecls = getAllIfaceDecls modEnv' -- MT: d2!

  -- NOTE: unclear what's happening here!
  --   - FIXME: understand and doc.
  --   - `m` not used (directly) but translating the modEnv'
  --   - this behavior is not in `importModule`
  (types, modEnv'') <- liftModuleM modEnv' $ do
    prims <- MB.getPrimMap
      -- a monad reader; doc: "generate the primitive map"
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims NoParams ifaceDecls
      -- NOTE: inpVars are the variables that are in scope.
      -- See source for the above two functions
      --   - doing a bit of unnecessary work here?!

      -- NOTE: looking at the source code of the functions in this action, it
      -- appears (not 100% clear) that modEnv'' will be equal to modEnv'

  -- FIXME[MT]:debugging:
  when debug $ do
    putStrLn $ unwords [ "LOG: loadCryptolModule ("
                       , show path
                       , ")"
                       ]
    writeFile (path ++ ".iface") $
       (ppShow $
         vsep [ ppListX "ifDecls:"   (Map.keys (MI.ifDecls   ifaceDecls))
              , ppListX "ifModules:" (Map.keys (MI.ifModules ifaceDecls))
              , text ""
              , ppListX "types(nmd):" (Map.keys types)
              ]
       )

    writeFile (path ++ ".ast-ld1") (ppShow m)
    ME.logModuleEnv (path ++ ".ld.modenv") modEnv''

    -- writeFile (path ++ ".ast-ld2") (ppShow (last $ ME.loadedModules modEnv'))
    -- writeFile (path ++ ".ast-ld3") (ppShow (last $ ME.loadedModules modEnv''))
     -- NOTE: -ld2/these three are all identical and look good ^.
     -- NOTE: "d2" is different as it is Qual, all else is UnQual.

  -- NOTE: at this point (all above) completely in cryptol-land!

  -- Regenerate SharedTerm environment.
  let oldModNames = map ME.lmName
                  $ ME.lmLoadedModules
                  $ ME.meLoadedModules modEnv

  let isNew m'    = T.mName m' `notElem` oldModNames
  let newModules  = filter isNew
                  $ map ME.lmModule
                  $ ME.lmLoadedModules
                  $ ME.meLoadedModules modEnv''

  let newDeclGroups = concatMap T.mDecls newModules
  let newNominal    = Map.difference (ME.loadedNominalTypes modEnv')
                                     (ME.loadedNominalTypes modEnv)

  -- TODO:MT: [#C] anything wrt submodules above?

  newTermEnv <-
    do oldCryEnv <- mkCryEnv env
       cEnv <- C.genCodeForNominalTypes sc newNominal oldCryEnv
       newCryEnv <- C.importTopLevelDeclGroups sc primOpts cEnv newDeclGroups
       traverse (\(t, j) -> incVars sc 0 j t) (C.envE newCryEnv)

  let names1 = MEx.exported C.NSValue (T.mExports m) -- :: Set T.Name
        -- FIXME:
        --   This excludes both submodules and what they contain.
        -- mExports :: MEx.ExportSpec MN.Name
      namesP = MI.ifsPublic (TIface.genIfaceNames m)
        -- This includes submodules, but does not contain
        -- names of defns inside them.

  {-
      namesN = MI.ifsNested (TIface.genIfaceNames m)
        -- lists the submodules, but not the defs inside them
  -}
      names = namesP
        -- names includes submodules (vs. names1)

  -- TODO:MT:HIA:
  --   - you need to get the submodules 'expanded' into names!
  --   - could do by-hand/adhoc, but
  --   - TODO: searching in deps/cryptol for 'the right way'
  --      1. not seeing anything.
  --      2. from exploring cryptol: submodules in scope and treated differently.
  --         -- special D2
  --
  when debug $ do
    putStrLn "<begin TIface.genIfaceNames m>:"
    ppIfaceNames (TIface.genIfaceNames m)

  let cryptolModule =
        CryptolModule
          -- create type synonym Map, keep only the exports:
          (Map.filterWithKey
             (\k _ -> Set.member k (MEx.exported C.NSType (T.mExports m)))
             (T.mTySyns m)
          )
          (Map.filterWithKey (\k _ -> Set.member k names) $
              --  - FIXME:
              --    - fixing/removing above
              --      - partially fixes (better fix is ...) loading submodules.
              --      - but doesn't fix submodules when importing!
              --  - NOTE removing this filter when loading D, causes
              --      the def "D::D2:d2" to now be available as "d2"!?  Seems odd!

              --  - FIXME:MT:undo
              --    - A TEMP FIX, RESTORE THIS, (doesn't fix!)
              --      - BUT, isn't this still not correct?
           Map.intersectionWith
             (\t x -> TypedTerm (TypedTermSchema t) x)
             types          -- NOTE: only use of this variable.
            newTermEnv
          )

    putStrLn "\n<end>\n"
    print $ ppListX "newTermEnv="        (Map.keys newTermEnv)
    print $ ppListX "types="             (Map.keys types)
    print $ ppListX "[old/info: exported] names1=" (Set.toList names1)
  -- MT: So, it appears that the bringing of the module-handle into
  --     "cryptol scope", via {{-}}, is not handled here; it is done
  --     elsewhere with the use of `cryptolModule` being bound as a
  --     sawscript variable.

  return ( cryptolModule
         , updateFFITypes m
             env { eModuleEnv = modEnv''
                 , eTermEnv = newTermEnv
                 }
             -- NOTE here the difference between this function and
             -- `importModule`:
             --  1. the `eImports` field is not updated, as
             --     this module (as a whole) is not being
             --     brought into scope inside {{ }} constructs.
             --  2. modEnv'' vs modEnv' (which may not be different, see
             --     notes above).
         )

ppIfaceNames :: Show n => MI.IfaceNames n -> IO ()
ppIfaceNames x =
  do
  putStrLn $ "IFaceNames " ++ show (MI.ifsName x)
  putStrLn $ ppShow $ ppListX " ifsNested =" (Set.toList (MI.ifsNested x))
  putStrLn $ ppShow $ ppListX " ifsDefines=" (Set.toList (MI.ifsDefines x))
  putStrLn $ ppShow $ ppListX " ifsPublic =" (Set.toList (MI.ifsPublic  x))
  putStrLn $ " "

ppListX :: PP a => String -> [a] -> Doc
ppListX s xs = text s <+> ppList (map pp xs)

updateFFITypes :: T.Module -> CryptolEnv -> CryptolEnv
updateFFITypes m env = env { eFFITypes = eFFITypes' }
  where
  eFFITypes' = foldr (\(nm, ty) -> Map.insert (getNameInfo nm) ty)
                     (eFFITypes env)
                     (T.findForeignDecls m)
  getNameInfo nm =
    case Map.lookup nm (eTermEnv env) of
      Just tm ->
        case asConstant tm of
          Just (ec, _) -> ecName ec
          Nothing ->
            panic "updateFFITypes" [
                "SAWCore term of Cryptol name is not Constant",
                "Name: " <> Text.pack (show nm),
                "Term: " <> Text.pack (showTerm tm)
            ]
      Nothing ->
        panic "updateFFITypes" [
            "Cannot find foreign function in term environment: " <> Text.pack (show nm)
        ]

bindCryptolModule :: (P.ModName, CryptolModule) -> CryptolEnv -> CryptolEnv
bindCryptolModule (modName, CryptolModule sm tm) env =
  env { eExtraNames = flip (foldr addName) (Map.keys tm') $
                      flip (foldr addTSyn) (Map.keys sm) $ eExtraNames env
      , eExtraTSyns = Map.union sm (eExtraTSyns env)
      , eExtraTypes = Map.union (fmap fst tm') (eExtraTypes env)
      , eTermEnv    = Map.union (fmap snd tm') (eTermEnv env)
      }
  where
    -- select out those typed terms from `tm' that have Cryptol schemas
    tm' = Map.mapMaybe f tm
          where
          f (TypedTerm (TypedTermSchema s) x) = Just (s,x)
          f _                                 = Nothing

    addName name = MN.shadowing (MN.singletonNS C.NSValue (P.mkQual modName (MN.nameIdent name)) name)
    -- FIXME: MT:suspicious. (we need to do any C.NSModule?)

    addSubModule name = MN.shadowing (MN.singletonNS C.NSModule (P.mkQual modName (MN.nameIdent name)) name)

    addTSyn name = MN.shadowing (MN.singletonNS C.NSType (P.mkQual modName (MN.nameIdent name)) name)

    -- FIXME: something wrong here, we lose ability to access sub-module names!!

-- | NOTE: Only used in the "cryptol_extract" primitive.
extractDefFromCryptolModule :: CryptolModule -> String -> IO TypedTerm
extractDefFromCryptolModule (CryptolModule _ tm) name =
  case Map.lookup (packIdent name) (Map.mapKeys MN.nameIdent tm) of
    Nothing -> do
               when debug $
                  putStrLn $
                    unlines ["LOG: extractDefFromCryptolModule:"
                            , " " ++ show (packIdent name)
                            , " " ++ show (ppListX "tm names:"
                                            (map MN.nameIdent $ Map.keys tm))
                            ]

               fail $ "Binding not found: " ++ name
               -- See bindCryptolModule, I'm not seeing dups disappearing! [huh?]
               -- FIXME: unfortunate we have lost the name of the cryptol module.
    Just t  -> return t

    -- FIXME: bug: see ... (we can't access things in submodules)
    -- FIXME: this is quite ad hoc, somehow invoke parse for name or something??


--------------------------------------------------------------------------------

importModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext             {- ^ Shared context for creating terms -} ->
  CryptolEnv                {- ^ Extend this environment -} ->
  Either FilePath P.ModName {- ^ Where to find the module -} ->
  Maybe P.ModName           {- ^ Name qualifier -} ->
  ImportVisibility          {- ^ What visibility to give symbols from this module -} ->
  Maybe P.ImportSpec        {- ^ What to import -} ->
  IO CryptolEnv
importModule sc env src as vis imps = do
  let modEnv = eModuleEnv env
  (m, modEnv') <-
    liftModuleM modEnv $
      do
      mtop <-
        case src of
          Left path -> MB.loadModuleByPath True path
          Right mn  -> snd <$> MB.loadModuleFrom True (MM.FromModule mn)
      m <- case mtop of
             T.TCTopModule m -> pure m
             T.TCTopSignature {} ->
                fail "Expected a module but found an interface."
      MM.io $ checkNotParameterized m
      return m

  when debug $ do
    putStrLn $ unwords [ "LOG: importModule ("
                       , show src
                       , ",", show vis
                       , ")"
                       ]
    case src of
      Left fp -> do
                 writeFile (fp ++ ".ast-im") (ppShow m)
                 ME.logModuleEnv (fp ++ ".im.modenv") modEnv'
      Right _ -> return ()


  -- Regenerate SharedTerm environment.
  let oldModNames   = map ME.lmName
                    $ ME.lmLoadedModules
                    $ ME.meLoadedModules modEnv
  let isNew m'      = T.mName m' `notElem` oldModNames
  let newModules    = filter isNew
                    $ map ME.lmModule
                    $ ME.lmLoadedModules
                    $ ME.meLoadedModules modEnv'
  let newDeclGroups = concatMap T.mDecls newModules

  let newNominal    = Map.difference (ME.loadedNominalTypes modEnv')
                                     (ME.loadedNominalTypes modEnv)

  newTermEnv <- do
       oldCryEnv <- mkCryEnv env
       cEnv      <- C.genCodeForNominalTypes sc newNominal oldCryEnv
       newCryEnv <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions
                                               cEnv newDeclGroups
       traverse (\(t, j) -> incVars sc 0 j t) (C.envE newCryEnv)

  when debug $ do
    putStrLn $ ppShow $ ppListX "newTermEnv=" (Map.keys newTermEnv)
     -- OK: has D::D2::d2

  return $
    updateFFITypes m
      env { eImports   = (vis, P.Import { T.iModule= T.mName m
                                        , T.iAs    = as
                                        , T.iSpec  = imps
                                        , T.iInst  = Nothing
                                        , T.iDoc   = Nothing
                                        }
                         )
                       : eImports env
          , eModuleEnv = modEnv'
          , eTermEnv   = newTermEnv
          }

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
  do
  when debug $ do
    putStrLn $ unwords [ "LOG: resolveIdentifier:", show nm]
    putStrLn "- LOG: nameEnv:"
    print (pp nameEnv)
  case splitOn (pack "::") nm of
    []  -> pure Nothing
           -- FIXME: shouldn't this be error?
    [i] -> doResolve (P.UnQual (C.mkIdent i))
    xs  -> let (qs,i) = (init xs, last xs)
           in  doResolve (P.Qual (C.packModName qs) (C.mkIdent i))
           -- test this
    -- FIXME: Is there no function that parses Text into PName?

  where
  modEnv = eModuleEnv env
  nameEnv = getNamingEnv2 env

  doResolve pnm =
    SMT.withSolver (return ()) (meSolverConfig modEnv) $ \s ->
    do let minp = MM.ModuleInput True (pure defaultEvalOpts) ?fileReader modEnv
       (res, _ws) <- MM.runModuleM (minp s) $
          MM.interactive (MB.rename interactiveName nameEnv (MR.renameVar MR.NameUse pnm))
       case res of
         Left _ -> pure Nothing
         Right (x,_) -> pure (Just x)


parseTypedTerm ::
  (HasCallStack, ?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO TypedTerm
parseTypedTerm sc env input = do
  let modEnv = eModuleEnv env

  -- Parse
  pexpr <- ioParseExpr input
  when debug $ do
    putStrLn $ unwords ["\nLOG: parseTypedTerm:"]
    putStrLn $ " pexpr= " ++ show pexpr

  ((expr, schema), modEnv') <- liftModuleM modEnv $ do

    -- FIXME: refactor: improve var names here:

    -- Eliminate patterns:
    npe <- MM.interactive (MB.noPat pexpr)

    -- FIXME: WIP: copied from cryptol's `checkExpr`:
    let nameEnv = getNamingEnv2 env
               -- ME.mctxNames <$> MM.getFocusedEnv OLD
               -- FIXME
               {- MT:  ::  M.ModContext -}
                {- MT:  ::  M.NamingEnv -}

        -- FIXME:WIP:MT:
        --  - this is empty when nothing focused.
        --  - this WORKS after we've `sawscript> focus MODULENAME`
        --    - for both load and import
        -- FIXME:WIP:MT:
        --  - are there other means by which other top-levels are in env?

    -- Resolve names
    -- let nameEnv = getNamingEnv env       -- FIXME:MT:restore
    -- nameEnv <- MM.io $ getNamingEnvLog env  -- FIXME:MT:undo
    when debug $ MM.io $ do
      putStrLn "- LOG: nameEnv:"
      print $ pp nameEnv
        -- FIXME: NOTE: if import: has D::D2 but not D::D2::d2
        -- FIXME: NOTE: if load:   has D::D2::d2
        -- but in both cases, we get Value not in scope in next line:

    let npe' = MR.rename npe
    -- MM.io $ print npe'  (FIXME: HUH?)
    when debug $ MM.io $ putStrLn "- LOG parseTypedTerm: point 0"
    re <- MM.interactive (MB.rename interactiveName nameEnv npe')
      -- FIXME: NOTE: this ^ where we get Value not in scope.    :HIA:
    when debug $ MM.io $ putStrLn "- LOG parseTypedTerm: point 1"

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

  when debug $
    putStrLn $ unwords ["\nLOG: parseDecls...:"]
  -- Parse
  (decls :: [P.Decl P.PName]) <- ioParseDecls input

  (tmodule, modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    (npdecls :: [P.Decl P.PName]) <- MM.interactive (MB.noPat decls)

    -- Convert from 'Decl' to 'TopDecl' so that types will be generalized
    let topdecls = [ P.Decl (P.TopLevel P.Public Nothing d) | d <- npdecls ]

    -- Resolve names
    (_nenv, rdecls) <- MM.interactive (MB.rename interactiveName (getNamingEnv2 env) (MR.renameTopDecls interactiveName topdecls))

    -- Create a Module to contain the declarations
    let rmodule = P.Module { P.mName = P.Located P.emptyRange interactiveName
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

  when debug $
    putStrLn $ unwords ["\nLOG: parseSchema...:"]
  -- Parse
  pschema <- ioParseSchema input

  fmap fst $ liftModuleM modEnv $ do

    -- Resolve names
    let nameEnv = getNamingEnv2 env
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
  CryptolEnv -> P.ModName -> String -> IO (T.Name, CryptolEnv)
declareName env mname input = do
  let pname = P.mkUnqual (packIdent input)
  let modEnv = eModuleEnv env
  (cname, modEnv') <-
    liftModuleM modEnv $ MM.interactive $
    MN.liftSupply (MN.mkDeclared C.NSValue (C.TopModule mname) MN.UserName (P.getIdent pname) Nothing P.emptyRange)
  let env' = env { eModuleEnv = modEnv' }
  return (cname, env')

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec (fmap typeNoUser fields)
    T.TNominal nt ts -> T.TNominal nt (fmap typeNoUser ts)

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)

------------------------------------------------------------

liftModuleM ::
  (?fileReader :: FilePath -> IO ByteString) =>
  ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m =
  do let minp = MM.ModuleInput True (pure defaultEvalOpts) ?fileReader env
     SMT.withSolver (return ()) (meSolverConfig env) $ \s ->
       MM.runModuleM (minp s) m >>= moduleCmdResult

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
