{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module SAWCoreIsabelle.IsaM where

import Control.Applicative
import Control.Monad

import qualified Control.Monad.Error.Class as CME
import qualified Control.Monad.Except as CME
import           Control.Monad.RWS (asks, modify, local)
import qualified Control.Monad.RWS as RWS
import qualified Control.Monad.IO.Class as IO
import qualified Control.Concurrent as IO

import           Data.Hashable
import           Data.List (find)
import qualified Data.Map as Map
import           Data.Maybe (fromJust)
import qualified Data.Set as Set

import qualified Cryptol.ModuleSystem.Name as Cry
import qualified Cryptol.Parser.Position as Position
import qualified Cryptol.TypeCheck.AST as Cry
import           Cryptol.Utils.PP (pp)

import qualified Language.Isabelle.Decl as Decl
import qualified Language.Isabelle.Name as Name
import qualified Language.Isabelle.Syntax as Syntax
import qualified Language.Isabelle.Theory as Theory

import qualified SAWCoreIsabelle.CryptolDeps as Deps
import qualified SAWCoreIsabelle.Error as Error
import qualified SAWCoreIsabelle.Options as Options
import           SAWCore.SAWCore (SharedContext)
import           CryptolSAWCore.CryptolEnv (CryptolEnv)



data NameEnv = NameEnv
  { nameToIdent :: Map.Map Name.Name Int, identToName :: Map.Map Int Name.Name, minIdent :: Int }

emptyNameEnv :: NameEnv
emptyNameEnv = NameEnv Map.empty Map.empty (-1)

-- | Insert an identifier into the name environment, with a suggested name.
--   Does nothing if the identifier already exists, creates a variant name
--   if the name is already in the environment (with a different identifier).
insertName :: Maybe Int -> Name.Name -> NameEnv -> (Name.Name, NameEnv)
insertName midx nm env = case midx of
  Just idx | Just nm' <- Map.lookup idx (identToName env) -> (nm', env)
  _ ->
    let
      used = Set.map Name.nmStr $ Map.keysSet (nameToIdent env) 
      nm' = fromJust $ find (\nm_ -> not $ Set.member (Name.nmStr nm_) used ) (Name.variants nm)
      idx = case midx of
        Just idx' -> idx'
        Nothing -> minIdent env - 1
    in (nm', NameEnv { nameToIdent = Map.insert nm' idx (nameToIdent env), identToName = Map.insert idx nm' (identToName env), minIdent = min idx (minIdent env) })


data SAWEnv = SAWEnv
  { envCryptolSAW :: CryptolEnv
  , envSharedContext :: SharedContext
  }

data IsaEnv = IsaEnv
  { envCurTheory :: Name.TheoryName
  , envSourceRange :: Position.Range
  , envTypeEnv :: Map.Map Cry.Name Cry.Schema
  , envNameEnv :: NameEnv
  , envCryDeps ::  Deps.CryptolDeps
  , envHashCache :: IO.MVar (Map.Map Cry.Name Int)
  , envOptions :: Options.Options
  , envSAW :: Maybe SAWEnv
  }

data IsaState = IsaState { stThy :: Theory.Theory }
newtype IsaOut = IsaOut { outWarns :: [Error.TranslationError] }
  deriving (Semigroup,Monoid)

newtype IsaM_ a = IsaM { unIsaM :: (RWS.RWST IsaEnv IsaOut IsaState (CME.ExceptT Error.TranslationError IO)) a}
  deriving (Applicative, Functor, Monad, IO.MonadIO
           , RWS.MonadReader IsaEnv
           , RWS.MonadState IsaState
           , RWS.MonadWriter IsaOut)

instance CME.MonadError Error.TranslationError IsaM_ where
  catchError f hdl = IsaM (CME.catchError (unIsaM f) (\e -> unIsaM (hdl e)))
  throwError e = IsaM $ do
    rng <- asks envSourceRange
    CME.throwError $ Error.addLocation rng e

instance Alternative IsaM_ where
  empty = fail ""
  f <|> g = CME.catchError f (\_ -> g)

instance MonadPlus IsaM_

mreturn :: Alternative m => Maybe a -> m a
mreturn (Just a) = pure a
mreturn Nothing = empty

type IsaM a = Options.HasOptions => IsaM_ a

initIsaState :: IsaEnv -> IsaState
initIsaState env = IsaState (Theory.mkTheory $ envCurTheory env)

initIsaEnv :: Options.HasOptions 
           => Deps.CryptolDeps
           -> Maybe SAWEnv
           -> Name.TheoryName
           -> IO IsaEnv
initIsaEnv cryEnv sawEnv thyNm = do
  let tyenv = Deps.mkTyEnv cryEnv
  hashCacheRef <- IO.newMVar Map.empty
  return $ IsaEnv thyNm
    Position.emptyRange tyenv emptyNameEnv cryEnv 
    hashCacheRef Options.allOptions sawEnv

getSAWEnv :: IsaM SAWEnv
getSAWEnv = asks envSAW >>= \case
  Just env -> return env
  Nothing -> fail "Missing SAW environment"

execIsaM :: IsaEnv -> IsaM () -> IO (IsaState, IsaOut)
execIsaM env f = 
  let st = initIsaState env
  in runIsaM env st f >>= \case
      Left er -> return (st, IsaOut { outWarns = [er] })
      Right ((), st', w) -> return (st', w)

runIsaM :: IsaEnv -> IsaState -> IsaM a -> IO (Either Error.TranslationError (a, IsaState, IsaOut))
runIsaM env st f = Options.withOptions (envOptions env) $ do
  CME.runExceptT $  RWS.runRWST (unIsaM f) env st

withConstraints :: IsaM a -> IsaM_ a
withConstraints f = do
  opts <- asks envOptions
  Options.withOptions opts $ f

instance MonadFail IsaM_ where
  fail str = CME.throwError $ Error.MonadFailure str

addDecl :: Decl.Decl -> IsaM ()
addDecl d = modify $ \st -> st { stThy = Theory.addDecl d (stThy st)  }

addHashDecl :: Cry.Name -> Name.Name -> IsaM ()
addHashDecl _crynm _isanm = do
  -- FIXME: disabled for now until this workflow is finalized
  return ()
  --h <- deepHashOf crynm
  --addDecl $ Decl.HashDecl isanm h

withTheory :: Name.TheoryName -> IsaM a -> IsaM a
withTheory thynm f = local (\env -> env { envCurTheory = thynm }) f

curTheory :: IsaM Name.TheoryName
curTheory = asks envCurTheory

withPosition :: Position.Range -> IsaM a -> IsaM a
withPosition rng f = local (\env -> env { envSourceRange = rng }) f

maybeWith :: (b -> IsaM a -> IsaM a) -> Maybe b -> IsaM a -> IsaM a
maybeWith  _ Nothing f = f
maybeWith g (Just b) f = g b f

withBindings :: [(Cry.Name, Cry.Schema)] -> IsaM a -> IsaM a
withBindings [] f =f
withBindings ((nm,s):nms) f = local (\env -> env { envTypeEnv = Map.insert nm s (envTypeEnv env) }) $ withBindings nms f

withDecl :: Cry.Decl -> IsaM a -> IsaM a
withDecl d = withBindings [(Cry.dName d,Cry.dSignature d)]

withDeclGroups :: [Cry.DeclGroup] -> IsaM a -> IsaM a
withDeclGroups [] f = f
withDeclGroups ds f =
  let nms = map (\d -> (Cry.dName d, Cry.dSignature d)) $ concat (map Cry.groupDecls ds)
  in withBindings nms f

withFreshName :: Name.IsaKind -> (Name.Name -> IsaM a) -> IsaM a
withFreshName k f = do
  nmEnv <- asks envNameEnv
  nm <- simpleName k ""
  let (nm', nmEnv') = insertName Nothing nm nmEnv
  local (\env -> env { envNameEnv = nmEnv' }) $ f nm'


withNames :: [(Int, Name.Name)] -> IsaM a -> IsaM a
withNames [] f = f
withNames ((idx,nm):nms) f = local (\env -> env { envNameEnv = snd (insertName (Just idx) nm (envNameEnv env)) })
  $ withNames nms f

lookupName :: Int -> IsaM Name.Name
lookupName idx = do
  nmEnv <- asks envNameEnv
  case Map.lookup idx (identToName nmEnv) of
    Just nm -> return nm
    Nothing -> CME.throwError $ Error.UnknownVariableIdent idx

simpleName :: Name.IsaKind -> String -> IsaM Name.Name
simpleName k nm = do
  thy <- curTheory
  return $ Name.Name thy nm Syntax.NoSyn k

simpleNameExpr :: String -> IsaM Name.Name
simpleNameExpr = simpleName Name.Term

simpleNameType :: String -> IsaM Name.Name
simpleNameType = simpleName Name.Typ

rethrow' :: Error.TranslationError -> IsaM a -> IsaM a
rethrow' er f = CME.catchError (wrapWarns er f) $ \er_inner -> 
  CME.throwError (Error.innerErrors er [er_inner])

wrapWarns :: Error.TranslationError -> IsaM a -> IsaM a
wrapWarns er f = do
  rng <- asks envSourceRange
  RWS.censor (\w -> IsaOut{outWarns = case outWarns w of
      [] -> []
      _ -> [Error.addLocation rng $ Error.innerErrors er (outWarns w)]}) f

rethrow :: (t -> Error.TranslationError) -> (t -> IsaM a) -> t -> IsaM a
rethrow mkerr f t = rethrow' (mkerr t) (f t)

warn :: Error.TranslationError -> IsaM ()
warn err = do
  rng <- asks envSourceRange
  RWS.tell (IsaOut $ [Error.addLocation rng err])

catchMaybe :: IsaM a -> (Error.TranslationError -> IsaM a) -> IsaM a
catchMaybe f hdl = if Options.keepGoing then CME.catchError f hdl else f


shallowHashOf :: Cry.Name -> IsaM Int
shallowHashOf crynm = do
  ref <- asks envHashCache
  cache <- IO.liftIO $ IO.readMVar ref
  case Map.lookup crynm cache of
    Just h -> return h
    Nothing -> getCryEntity crynm >>= \case
      Just (ce,_) -> do
        let h = hash ce
        IO.liftIO $ IO.modifyMVar_ ref (\cache_ -> return $ Map.insert crynm h cache_)
        return h
      Nothing -> return $ hash (show $ pp crynm)

deepHashOf :: Cry.Name -> IsaM Int
deepHashOf crynm = getCryEntity crynm >>= \case
  Just (ce,deps) -> do
    ce_deps <- mapM shallowHashOf (Set.toList deps)
    return $ (hash (ce, ce_deps))
  Nothing -> CME.throwError $ Error.MissingCryName crynm

getCryEntity :: Cry.Name -> IsaM  (Maybe (Deps.CryEntity, Set.Set Cry.Name))
getCryEntity crynm = do
  m <- asks envCryDeps
  return $ Map.lookup crynm (Deps.entityDeps m)

deepHashFromEnv :: Deps.CryptolDeps -> Cry.Name -> IO (Maybe Int)
deepHashFromEnv cryEnv cryNm = Options.withOptions Options.emptyOpts $ do
  env <- initIsaEnv cryEnv Nothing (Name.TheoryName "<interactive>" False)
  runIsaM env (initIsaState env) (deepHashOf cryNm) >>= \case
    Right (a,_,_) -> return $ Just a
    Left{} -> return Nothing
