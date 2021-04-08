{- |
Module      : SAWScript.CryptolEnv
Description : Context for interpreting Cryptol within SAW-Script.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Verifier.SAW.CryptolEnv
  ( ImportVisibility(..)
  , CryptolEnv(..)
  , initCryptolEnv
  , loadCryptolModule
  , bindCryptolModule
  , lookupCryptolModule
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
  )
  where

--import qualified Control.Exception as X
import Data.ByteString (ByteString)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Text (Text, pack, splitOn)
import Control.Monad(when)

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable
#endif

import System.Environment (lookupEnv)
import System.Environment.Executable (splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

import Verifier.SAW.SharedTerm (SharedContext, Term, incVars)

import qualified Verifier.SAW.Cryptol as C

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

import Cryptol.Utils.PP
import Cryptol.Utils.Ident (Ident, preludeName, preludeReferenceName
                           , packIdent, interactiveName, identText
                           , packModName, textToModName, modNameChunks
                           , prelPrim)
import Cryptol.Utils.Logger (quietLogger)

--import SAWScript.REPL.Monad (REPLException(..))
import Verifier.SAW.TypedTerm
-- import SAWScript.Utils (Pos(..))
-- import SAWScript.AST (Located(getVal, locatedPos), Import(..))


-- | Parse input, together with information about where it came from.
data InputText = InputText
  { inpText :: String -- ^ Parse this
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

data CryptolEnv = CryptolEnv
  { eImports    :: [(ImportVisibility, P.Import)]           -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv         -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv         -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.Name T.Schema  -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn   -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name Term      -- ^ SAWCore terms for *all* names in scope
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
    case modNameChunks (textToModName (pack xs)) of
      []  -> const False
      [x] -> (packIdent x ==) . MN.nameIdent
      cs -> let m = MN.Declared (packModName (map pack (init cs))) MN.UserName
                i = packIdent (last cs)
             in \n -> MN.nameIdent n == i && MN.nameInfo n == m



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

  -- Load Cryptol prelude
  (_, modEnv2) <-
    liftModuleM modEnv1 $
      MB.loadModuleFrom False (MM.FromModule preludeName)

  -- Load Cryptol reference implementations
  ((_,refMod), modEnv) <-
    liftModuleM modEnv2 $
      MB.loadModuleFrom False (MM.FromModule preludeReferenceName)

  -- Set up reference implementation redirections
  let refDecls = T.mDecls refMod
  let nms = fst <$> Map.toList (M.ifDecls (M.ifPublic (M.genIface refMod)))
  let refPrims = Map.fromList
                  [ (prelPrim (identText (MN.nameIdent nm)), T.EWhere (T.EVar nm) refDecls)
                  | nm <- nms ]
  let cryEnv0 = C.emptyEnv{ C.envRefPrims = refPrims }

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv cryEnv0

  return CryptolEnv
    { eImports    = [ (OnlyPublic, P.Import preludeName Nothing Nothing)
                    , (OnlyPublic, P.Import preludeReferenceName (Just preludeReferenceName) Nothing)
                    ]
    , eModuleEnv  = modEnv
    , eExtraNames = mempty
    , eExtraTypes = Map.empty
    , eExtraTSyns = Map.empty
    , eTermEnv    = termEnv
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
ioParseGeneric parse inp = ioParseResult (parse cfg (pack str))
  where
  cfg = P.defaultConfig { P.cfgSource = inpFile inp }
  str = concat [ replicate (inpLine inp - 1) '\n'
               , replicate (inpCol inp - 1) ' '
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
      let ifc = ME.lmInterface lm
          syms = case vis of
                   OnlyPublic       -> MI.ifPublic ifc
                   PublicAndPrivate -> MI.ifPublic ifc `mappend` M.ifPrivate ifc
      return $ MN.interpImport i syms

getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me = mconcat (map (both . ME.lmInterface) (ME.getLoadedModules (ME.meLoadedModules me)))
  where both ifc = M.ifPublic ifc `mappend` M.ifPrivate ifc

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
          TM.inpVars `fmap` MB.genInferInput P.emptyRange prims
            MI.noIfaceParams ifaceDecls
     let types' = Map.union (eExtraTypes env) types
     let terms = eTermEnv env
     let cryEnv = C.emptyEnv
           { C.envE = fmap (\t -> (t, 0)) terms
           , C.envC = types'
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
     cryEnv' <- C.importTopLevelDeclGroups sc cryEnv dgs
     termEnv' <- traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv')

     let decls = concatMap T.groupDecls dgs
     let names = map T.dName decls
     let newTypes = Map.fromList [ (T.dName d, T.dSignature d) | d <- decls ]
     let addName name = MR.shadowing (MN.singletonE (P.mkUnqual (MN.nameIdent name)) name)
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
  cryEnv <- C.importTopLevelDeclGroups sc cryEnv0 declGroups
  traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv)

--------------------------------------------------------------------------------

checkNotParameterized :: T.Module -> IO ()
checkNotParameterized m =
  when (T.isParametrizedModule m) $
    fail $ unlines [ "Cannot load parameterized modules directly."
                   , "Either use a ` import, or make a module instantiation."
                   ]


loadCryptolModule ::
  (?fileReader :: FilePath -> IO ByteString) =>
  SharedContext -> CryptolEnv -> FilePath ->
  IO (CryptolModule, CryptolEnv)
loadCryptolModule sc env path = do
  let modEnv = eModuleEnv env
  (m, modEnv') <- liftModuleM modEnv (MB.loadModuleByPath path)
  checkNotParameterized m

  let ifaceDecls = getAllIfaceDecls modEnv'
  (types, modEnv'') <- liftModuleM modEnv' $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims MI.noIfaceParams ifaceDecls

  -- Regenerate SharedTerm environment.
  oldCryEnv <- mkCryEnv env
  let oldModNames = map ME.lmName $ ME.lmLoadedModules $ ME.meLoadedModules modEnv
  let isNew m' = T.mName m' `notElem` oldModNames
  let newModules = filter isNew $ map ME.lmModule $ ME.lmLoadedModules $ ME.meLoadedModules modEnv''
  let newDeclGroups = concatMap T.mDecls newModules
  newCryEnv <- C.importTopLevelDeclGroups sc oldCryEnv newDeclGroups
  newTermEnv <- traverse (\(t, j) -> incVars sc 0 j t) (C.envE newCryEnv)

  let names = MEx.eBinds (T.mExports m) -- :: Set T.Name
  let tm' = Map.filterWithKey (\k _ -> Set.member k names) $
            Map.intersectionWith TypedTerm types newTermEnv
  let env' = env { eModuleEnv = modEnv''
                 , eTermEnv = newTermEnv
                 }
  let sm' = Map.filterWithKey (\k _ -> Set.member k (MEx.eTypes (T.mExports m))) (T.mTySyns m)
  return (CryptolModule sm' tm', env')

bindCryptolModule :: (P.ModName, CryptolModule) -> CryptolEnv -> CryptolEnv
bindCryptolModule (modName, CryptolModule sm tm) env =
  env { eExtraNames = flip (foldr addName) (Map.keys tm) $
                      flip (foldr addTSyn) (Map.keys sm) $ eExtraNames env
      , eExtraTSyns = Map.union sm (eExtraTSyns env)
      , eExtraTypes = Map.union (fmap (\(TypedTerm s _) -> s) tm) (eExtraTypes env)
      , eTermEnv    = Map.union (fmap (\(TypedTerm _ t) -> t) tm) (eTermEnv env)
      }
  where
    addName name = MN.shadowing (MN.singletonE (P.mkQual modName (MN.nameIdent name)) name)
    addTSyn name = MN.shadowing (MN.singletonT (P.mkQual modName (MN.nameIdent name)) name)

lookupCryptolModule :: CryptolModule -> String -> IO TypedTerm
lookupCryptolModule (CryptolModule _ tm) name =
  case Map.lookup (packIdent name) (Map.mapKeys MN.nameIdent tm) of
    Nothing -> fail $ "Binding not found: " ++ name
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
  (m, modEnv') <-
    liftModuleM modEnv $
    case src of
      Left path -> MB.loadModuleByPath path
      Right mn -> snd <$> MB.loadModuleFrom True (MM.FromModule mn)
  checkNotParameterized m

  -- Regenerate SharedTerm environment.
  oldCryEnv <- mkCryEnv env
  let oldModNames = map ME.lmName $ ME.lmLoadedModules $ ME.meLoadedModules modEnv
  let isNew m' = T.mName m' `notElem` oldModNames
  let newModules = filter isNew $ map ME.lmModule $ ME.lmLoadedModules $ ME.meLoadedModules modEnv'
  let newDeclGroups = concatMap T.mDecls newModules
  newCryEnv <- C.importTopLevelDeclGroups sc oldCryEnv newDeclGroups
  newTermEnv <- traverse (\(t, j) -> incVars sc 0 j t) (C.envE newCryEnv)

  return env { eImports = (vis, P.Import (T.mName m) as imps) : eImports env
             , eModuleEnv = modEnv'
             , eTermEnv = newTermEnv }

bindIdent :: Ident -> CryptolEnv -> (T.Name, CryptolEnv)
bindIdent ident env = (name, env')
  where
    modEnv = eModuleEnv env
    supply = ME.meSupply modEnv
    fixity = Nothing
    (name, supply') = MN.mkDeclared interactiveName MN.UserName ident fixity P.emptyRange supply
    modEnv' = modEnv { ME.meSupply = supply' }
    env' = env { eModuleEnv = modEnv' }

bindTypedTerm :: (Ident, TypedTerm) -> CryptolEnv -> CryptolEnv
bindTypedTerm (ident, TypedTerm schema trm) env =
  env' { eExtraNames = MR.shadowing (MN.singletonE pname name) (eExtraNames env)
       , eExtraTypes = Map.insert name schema (eExtraTypes env)
       , eTermEnv    = Map.insert name trm (eTermEnv env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env

bindType :: (Ident, T.Schema) -> CryptolEnv -> CryptolEnv
bindType (ident, T.Forall [] [] ty) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] ty Nothing
bindType _ env = env -- only monomorphic types may be bound

bindInteger :: (Ident, Integer) -> CryptolEnv -> CryptolEnv
bindInteger (ident, n) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] (T.tNum n) Nothing

--------------------------------------------------------------------------------

-- FIXME: This definition was copied from a local declaration inside
-- function 'defaultRW' in module 'Cryptol.REPL.Monad'. The cryptol
-- package should probably export it so we don't have to copy it.
meSolverConfig :: ME.ModuleEnv -> TM.SolverConfig
meSolverConfig env =
  TM.SolverConfig
  { TM.solverPath = "z3"
  , TM.solverArgs = [ "-smt2", "-in" ]
  , TM.solverVerbose = 0
  , TM.solverPreludePath = ME.meSearchPath env
  }

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
    SMT.withSolver (meSolverConfig modEnv) $ \s ->
    do let minp = MM.ModuleInput True (pure defaultEvalOpts) ?fileReader modEnv
       (res, _ws) <- MM.runModuleM (minp s) $
          MM.interactive (MB.rename interactiveName nameEnv (MR.renameVar pnm))
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
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }

  -- Translate
  trm <- translateExpr sc env' expr
  return (TypedTerm schema trm)

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

    -- Label each TopDecl with the "interactive" module for unique name generation
    let (mdecls :: [MN.InModule (P.TopDecl P.PName)]) = map (MN.InModule interactiveName) topdecls
    nameEnv1 <- MN.liftSupply (MN.namingEnv' mdecls)

    -- Resolve names
    let nameEnv = nameEnv1 `MR.shadowing` getNamingEnv env
    (rdecls :: [P.TopDecl T.Name]) <- MM.interactive (MB.rename interactiveName nameEnv (traverse MR.rename topdecls))

    -- Create a Module to contain the declarations
    let rmodule = P.Module { P.mName = P.Located P.emptyRange interactiveName
                           , P.mInstance = Nothing
                           , P.mImports = []
                           , P.mDecls = rdecls
                           }

    -- Infer types
    let range = fromMaybe P.emptyRange (P.getLoc rdecls)
    prims <- MB.getPrimMap
    -- noIfaceParams because we don't support functors yet
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifaceDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (TM.runInferM tcEnv' (TI.inferModule rmodule))
    tmodule <- MM.interactive (runInferOutput out)
    return tmodule

  -- Add new type synonyms and their name bindings to the environment
  let syns' = Map.union (eExtraTSyns env) (T.mTySyns tmodule)
  let addName name = MR.shadowing (MN.singletonT (P.mkUnqual (MN.nameIdent name)) name)
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
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifDecls
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
    MN.liftSupply (MN.mkDeclared mname MN.UserName (P.getIdent pname) Nothing P.emptyRange)
  let env' = env { eModuleEnv = modEnv' }
  return (cname, env')

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec (fmap typeNoUser fields)
    T.TNewtype nt ts -> T.TNewtype nt (fmap typeNoUser ts)

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)

------------------------------------------------------------

liftModuleM ::
  (?fileReader :: FilePath -> IO ByteString) =>
  ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m =
  do let minp = MM.ModuleInput True (pure defaultEvalOpts) ?fileReader env
     SMT.withSolver (meSolverConfig env) $ \s ->
       MM.runModuleM (minp s) m >>= moduleCmdResult

defaultEvalOpts :: E.EvalOpts
defaultEvalOpts = E.EvalOpts quietLogger E.defaultPPOpts

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (print . pp) (map suppressDefaulting ws)
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> fail $ "Cryptol error:\n" ++ show (pp err) -- X.throwIO (ModuleSystemError err)
  where
    suppressDefaulting :: MM.ModuleWarning -> MM.ModuleWarning
    suppressDefaulting w =
      case w of
        MM.TypeCheckWarnings nm xs -> MM.TypeCheckWarnings nm (filter (notDefaulting . snd) xs)
        MM.RenamerWarnings xs -> MM.RenamerWarnings xs

    notDefaulting :: TE.Warning -> Bool
    notDefaulting (TE.DefaultingTo {}) = False
    notDefaulting _ = True
