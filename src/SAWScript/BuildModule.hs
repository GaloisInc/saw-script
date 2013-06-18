{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.BuildModule
  ( buildModule
  ) where

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Import (LoadedModules (..))

import Control.Applicative
import Control.Arrow
import Control.Monad
--import Control.Monad.State
--import Data.Monoid
import Data.Foldable (foldrM)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as T

-- Types -----------------------------------------------------------------------

type Incoming = (ModuleName,LoadedModules)
--type Incoming = (ModuleName,[TopStmtSimple RawT])
type Outgoing = ModuleSimple RawT RawT

type ModuleBuilder = (Env ExprAssoc,Env RawT,S.Set ModuleName)
type ExprAssoc = (Maybe (ExprSimple RawT),Maybe RawSigT)

type ModuleParts = (Env (ExprSimple RawT),Env RawT,S.Set ModuleName)

-- BuildEnv --------------------------------------------------------------------

buildModule :: Compiler Incoming Outgoing
buildModule = compiler "BuildEnv" $ \(mn,ms) -> let mss = M.assocs $ modules ms in
  T.traverse (build >=> check) >=> assemble mn
    $ mss

-- stage1: build tentative environment. expression vars may or may not have bound expressions,
--   but may not have multiple bindings.
--build :: [TopStmtSimple RawT] -> ModuleBuilder
build :: (ModuleName,[TopStmtSimple RawT]) -> Err (ModuleName,ModuleBuilder)
build (nm,ts) = (,) <$> pure nm <*> foldrM modBuilder (M.empty, M.empty, S.empty) ts
-- stage2: force every expression var to have exactly one bound expression.
check :: (ModuleName,ModuleBuilder) -> Err (ModuleName,ModuleParts)
check (nm,(ee,te,ds)) = (,) <$> pure nm <*> mps
  where
  mps = (,,) <$> traverseWithKey ensureExprPresent ee <*> pure te <*> pure ds
-- stage3: make a module out of the resulting envs
assemble :: ModuleName -> [(ModuleName,ModuleParts)] -> Err Outgoing
assemble mn envs = go mn
  where
  go n = case lookup n envs of
    Nothing         -> fail $ "Module " ++ renderModuleName n ++ " was not loaded"
    Just (ee,te,ds) -> return (Module n ee te $ fromSet dummyModule ds)

-- TODO: build a reasonable module
dummyModule :: ModuleName -> ValidModule
dummyModule mn = Module mn M.empty M.empty M.empty

-- Every expression name must be bound to something
ensureExprPresent :: Name -> ExprAssoc -> Err (ExprSimple RawT)
ensureExprPresent n met = case met of
  (Just e,Just t) -> return $ updateAnnotation (Just t) e
  (Just e,_     ) -> return e
  _               -> noBindingErr n

modBuilder :: TopStmtSimple RawT -> ModuleBuilder -> Err ModuleBuilder
modBuilder t (ee,te,ds) = case t of
  -- TypeDecls may not fail
  TopTypeDecl n pt -> case M.lookup n ee of
                      Just (_,Just _) -> multiDeclErr n
                      _               -> return (intoExprEnv (newTypeDecl pt) n ee,te,ds)
  -- Multiple binds to the same name will fail
  TopBind n e      -> case M.lookup n ee of
                      Just (Just _,_) -> multiDeclErr n
                      _               -> return (intoExprEnv (newBind e) n ee,te,ds)
  -- Multiple declarations of the same type synonym will fail
  TypeDef n pt     -> if M.member n te
                      then multiDeclErr n
                      else return (ee,intoTypeEnv n (newTypeSyn pt) te,ds)
  -- Multiple declarations of an abstract type will fail
  AbsTypeDecl n    -> if M.member n te
                      then multiDeclErr n
                      else return (ee,intoTypeEnv n newAbsType te,ds)
  -- Imports show dependencies
  Import mn _ _    -> return (ee,te,addDependency mn ds)

-- BuildEnv --------------------------------------------------------------------

intoExprEnv :: (Maybe ExprAssoc -> ExprAssoc) -> Name -> Env ExprAssoc -> Env ExprAssoc
intoExprEnv f n = M.alter (Just . f) n

intoTypeEnv :: Name -> RawT -> Env RawT -> Env RawT
intoTypeEnv n a = M.insert n a

-- If the name is bound already, add the RawSigT to the others,
--  otherwise start a new list.
newTypeDecl :: RawSigT -> Maybe ExprAssoc -> ExprAssoc
newTypeDecl pt = maybe (Nothing,Just pt) (second (Just pt `mplus`))

-- The fst of the resulting tuple will always be (Just e).
--  If the name wasn't bound already, bind it.
newBind :: ExprSimple RawT -> Maybe ExprAssoc -> ExprAssoc
newBind e = maybe (Just e,Nothing) (first $ const $ Just e)

newTypeSyn :: RawSigT -> RawT
newTypeSyn = Just

newAbsType :: RawT
newAbsType = Nothing

addDependency :: ModuleName -> S.Set ModuleName -> S.Set ModuleName
addDependency = S.insert

-- Error Messages --------------------------------------------------------------

multiDeclErr :: Name -> Err a 
multiDeclErr n = fail ("Multiple declarations of '" ++ n ++ "'")

noBindingErr :: Name -> Err a
noBindingErr n = fail ("The type signature for '" ++ n ++ "' lacks an accompanying binding.")

-- Backward Compatibility ------------------------------------------------------

#if __GLASGOW_HASKELL__ < 706
fromSet :: Eq k => (k -> a) -> S.Set k -> M.Map k a
fromSet f s = M.fromAscList [ (x, f x) | x <- S.toAscList s ]

traverseWithKey :: (Applicative t, Ord k) => (k -> a -> t b) -> M.Map k a -> t (M.Map k b)
traverseWithKey f s =
  fmap M.fromList (T.traverse (\(k, v) -> fmap ((,) k) (f k v)) (M.toList s))
#else
fromSet :: (k -> a) -> S.Set k -> M.Map k a
fromSet = M.fromSet

traverseWithKey :: Applicative t => (k -> a -> t b) -> M.Map k a -> t (M.Map k b)
traverseWithKey = M.traverseWithKey
#endif
