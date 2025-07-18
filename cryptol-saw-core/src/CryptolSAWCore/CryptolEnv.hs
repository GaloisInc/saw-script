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
  , lookupCryptolModule
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
  )
  where

--import qualified Control.Exception as X
import Data.ByteString (ByteString)
import qualified Data.Text as Text
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, splitOn)
import Control.Monad(when)

import System.Environment (lookupEnv)
import System.Environment.Executable (splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

import CryptolSAWCore.Panic
import SAWCore.Name (nameInfo)
import SAWCore.Recognizer (asConstant)
import SAWCore.SharedTerm (NameInfo, SharedContext, Term)
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
                           , mkIdent, interactiveName, identText
                           , textToModName
                           , prelPrim)
import Cryptol.Utils.Logger (quietLogger)

--import SAWScript.REPL.Monad (REPLException(..))
import CryptolSAWCore.TypedTerm
import Cryptol.ModuleSystem.Env (ModContextParams(NoParams))
-- import SAWCentral.AST (Located(getVal, locatedPos), Import(..))


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

-- | The environment for capturing the Cryptol interpreter state as well as the
--   SAWCore translations and associated state.
--
--  FIXME[D]: The differences in function between this and the similar
--   C.Env?

data CryptolEnv = CryptolEnv
  { eImports    :: [(ImportVisibility, P.Import)]
                                        -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv         -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv         -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.Name T.Schema  -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn   -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name Term      -- ^ SAWCore terms for *all* names in scope
  , ePrims      :: Map C.PrimIdent Term -- ^ SAWCore terms for primitives
  , ePrimTypes  :: Map C.PrimIdent Term -- ^ SAWCore terms for primitive type names
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

-- FIXME: Code duplication, these three functions are relatively similar (and last 2 are 85% similar):
--  - initCryptolEnv
--  - loadCryptolModule
--  - importModule
--- TODO: common up the common code.

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
  ((_,refTop), modEnv) <-
    liftModuleM modEnv2 $
      MB.loadModuleFrom False (MM.FromModule preludeReferenceName)
  let refMod = T.tcTopEntityToModule refTop

  -- Set up reference implementation redirections
  let refDecls = T.mDecls refMod
  let nms = Set.toList (MI.ifsPublic (TIface.genIfaceNames refMod))
  let refPrims = Map.fromList
                  [ (prelPrim (identText (MN.nameIdent nm)), T.EWhere (T.EVar nm) refDecls)
                  | nm <- nms ]
  let cryEnv0 = C.emptyEnv{ C.envRefPrims = refPrims }

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv cryEnv0

  return CryptolEnv
    { eImports    = [ (OnlyPublic, P.Import preludeName Nothing Nothing Nothing Nothing)
                    , (OnlyPublic, P.Import preludeReferenceName (Just preludeReferenceName) Nothing Nothing Nothing)
                    , (OnlyPublic, P.Import arrayName Nothing Nothing Nothing Nothing)
                    ]
    , eModuleEnv  = modEnv
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

-- Rename ----------------------------------------------------------------------

getNamingEnv :: CryptolEnv -> MR.NamingEnv
getNamingEnv env = eExtraNames env `MR.shadowing` nameEnv
  where
    nameEnv = mconcat $ fromMaybe [] $ traverse loadImport (eImports env)
    loadImport (vis, i) = do
      lm <- ME.lookupModule (T.iModule i) (eModuleEnv env)
      let ifc = MI.ifNames (ME.lmInterface lm)
          syms = MN.namingEnvFromNames $
                 case vis of
                   OnlyPublic       -> MI.ifsPublic ifc
                   PublicAndPrivate -> MI.ifsDefines ifc
      return $ MN.interpImportEnv i syms

getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me = mconcat (map (both . ME.lmInterface) (ME.getLoadedModules (ME.meLoadedModules me)))
  where both = MI.ifDefines

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
     return env
           { eExtraNames = foldr addName (eExtraNames env) names
           , eExtraTypes = Map.union (eExtraTypes env) newTypes
           , eTermEnv    = C.envE cryEnv'
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
  return (C.envE cryEnv2)

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
         T.TCTopModule mo -> pure mo
         T.TCTopSignature {} ->
            fail $ "Expected a module, but " ++ show path ++ " is an interface."
  checkNotParameterized m

  let ifaceDecls = getAllIfaceDecls modEnv'
  (types, modEnv'') <- liftModuleM modEnv' $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims NoParams ifaceDecls

  -- Regenerate SharedTerm environment.
  oldCryEnv <- mkCryEnv env
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

  newTermEnv <-
    do cEnv <- C.genCodeForNominalTypes sc newNominal oldCryEnv
       newCryEnv <- C.importTopLevelDeclGroups sc primOpts cEnv newDeclGroups
       return (C.envE newCryEnv)

  let names = MEx.exported C.NSValue (T.mExports m) -- :: Set T.Name

  let tm'   = Map.filterWithKey (\k _ -> Set.member k names) $
              Map.intersectionWith
                (\t x -> TypedTerm (TypedTermSchema t) x)
                types
                newTermEnv

  let env' = updateFFITypes m
               env { eModuleEnv = modEnv''
                   , eTermEnv = newTermEnv
                   }

  let sm' = Map.filterWithKey
              (\k _ -> Set.member k (MEx.exported C.NSType (T.mExports m)))
              (T.mTySyns m)

  return (CryptolModule sm' tm', env')

updateFFITypes :: T.Module -> CryptolEnv -> CryptolEnv
updateFFITypes m env = env { eFFITypes = eFFITypes' }
  where
  eFFITypes' = foldr
    (\(nm, ty) -> Map.insert (getNameInfo nm) ty)
    (eFFITypes env)
    (T.findForeignDecls m)
  getNameInfo nm =
    case Map.lookup nm (eTermEnv env) of
      Just tm ->
        case asConstant tm of
          Just n -> nameInfo n
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
    -- select out those typed terms that have Cryptol schemas
    tm' = Map.mapMaybe f tm
    f (TypedTerm (TypedTermSchema s) x) = Just (s,x)
    f _ = Nothing

    addName name = MN.shadowing (MN.singletonNS C.NSValue (P.mkQual modName (MN.nameIdent name)) name)
    addTSyn name = MN.shadowing (MN.singletonNS C.NSType (P.mkQual modName (MN.nameIdent name)) name)

lookupCryptolModule :: CryptolModule -> Text -> IO TypedTerm
lookupCryptolModule (CryptolModule _ tm) name =
  case Map.lookup (mkIdent name) (Map.mapKeys MN.nameIdent tm) of
    Nothing -> fail $ Text.unpack $ "Binding not found: " <> name
    Just t -> return t

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
  (mtop, modEnv') <-
    liftModuleM modEnv $
    case src of
      Left path -> MB.loadModuleByPath True path
      Right mn -> snd <$> MB.loadModuleFrom True (MM.FromModule mn)
  m <- case mtop of
         T.TCTopModule m -> pure m
         T.TCTopSignature {} ->
            fail "Expected a module but found an interface."
  checkNotParameterized m

  -- Regenerate SharedTerm environment.
  oldCryEnv <- mkCryEnv env
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

  newTermEnv <-
    do cEnv      <- C.genCodeForNominalTypes sc newNominal oldCryEnv
       newCryEnv <- C.importTopLevelDeclGroups sc C.defaultPrimitiveOptions
                                                            cEnv newDeclGroups
       return (C.envE newCryEnv)

  return $
    updateFFITypes m
      env { eImports   = (vis, P.Import (T.mName m) as imps Nothing Nothing)
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
    (name, supply') = MN.mkDeclared C.NSValue (C.TopModule interactiveName) MN.UserName ident fixity P.emptyRange supply
    modEnv' = modEnv { ME.meSupply = supply' }
    env' = env { eModuleEnv = modEnv' }

bindTypedTerm :: (Ident, TypedTerm) -> CryptolEnv -> CryptolEnv
bindTypedTerm (ident, TypedTerm (TypedTermSchema schema) trm) env =
  env' { eExtraNames = MR.shadowing (MN.singletonNS C.NSValue pname name) (eExtraNames env)
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
  (?fileReader :: FilePath -> IO ByteString) =>
  CryptolEnv -> Text -> IO (Maybe T.Name)
resolveIdentifier env nm =
  case splitOn (pack "::") nm of
    []  -> pure Nothing
    [i] -> doResolve (P.UnQual (C.mkIdent i))
    xs  -> let (qs,i) = (init xs, last xs)
            in doResolve (P.Qual (C.packModName qs) (C.mkIdent i))
  where
  modEnv = eModuleEnv env
  nameEnv = getNamingEnv env

  doResolve pnm =
    SMT.withSolver (return ()) (meSolverConfig modEnv) $ \s ->
    do let minp = MM.ModuleInput True (pure defaultEvalOpts) ?fileReader modEnv
       (res, _ws) <- MM.runModuleM (minp s) $
          MM.interactive (MB.rename interactiveName nameEnv (MR.renameVar MR.NameUse pnm))
       case res of
         Left _ -> pure Nothing
         Right (x,_) -> pure (Just x)


parseTypedTerm ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> InputText -> IO TypedTerm
parseTypedTerm sc env input = do
  let modEnv = eModuleEnv env

  -- Parse
  pexpr <- ioParseExpr input

  ((expr, schema), modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    npe <- MM.interactive (MB.noPat pexpr)

    -- Resolve names
    let nameEnv = getNamingEnv env

    re <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename npe))

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
