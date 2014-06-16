{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.BuildModules
  ( buildModules
  , ModuleParts (..)
  , preludeName
  ) where

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Import (LoadedModules (..))

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Foldable (foldrM)
import qualified Data.Graph as G
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as T

-- Types -----------------------------------------------------------------------

type Incoming = LoadedModules
type Outgoing = [ModuleParts CheckedExpr]

type UncheckedExpr = (Maybe (ExprSimple RawT),Maybe RawSigT)
type CheckedExpr   = ExprSimple RawT

data ModuleParts e = ModuleParts
  { modName :: ModuleName
  , modExprEnv :: Env e
  , modPrimEnv :: Env RawT
  , modTypeEnv :: Env RawT
  , modDeps    :: S.Set ModuleName
  } deriving (Show)

newtype ModMap e = ModMap
  { modMap :: M.Map ModuleName (ModuleParts e)
  } deriving (Show)

-- BuildEnv --------------------------------------------------------------------

buildModules :: Compiler Incoming Outgoing
buildModules = compiler "BuildEnv" $ \ms -> T.traverse (build >=> addPreludeDependency >=> check) >=> assemble
  $ M.assocs $ modules ms

addPreludeDependency :: ModuleParts UncheckedExpr -> Err (ModuleParts UncheckedExpr)
addPreludeDependency mparts@(ModuleParts mn ee pe te ds)
  | mn == preludeName = return mparts
  | otherwise = return $ ModuleParts mn ee pe te $ S.insert preludeName ds

preludeName :: ModuleName
preludeName = ModuleName [] "Prelude"

-- stage1: build tentative environment. expression vars may or may not have bound expressions,
--   but may not have multiple bindings.
build :: (ModuleName,[TopStmtSimple RawT]) -> Err (ModuleParts UncheckedExpr)
build (mn,ts) = foldrM modBuilder (ModuleParts mn M.empty M.empty M.empty S.empty) ts

-- stage2: force every expression var to have exactly one bound expression.
check :: ModuleParts UncheckedExpr -> Err (ModuleParts CheckedExpr)
check (ModuleParts mn ee pe te ds) = ModuleParts mn <$> traverseWithKey ensureExprPresent ee <*> pure pe <*> pure te <*> pure ds

-- stage3: make a module out of the resulting envs
assemble :: [ModuleParts CheckedExpr] -> Err Outgoing
assemble mods = return $ buildQueue modM
  where
  modM = ModMap $ M.fromList [ (modName m,m) | m <- mods ]


-- Every expression name must be bound to something
ensureExprPresent :: Name -> UncheckedExpr -> Err (ExprSimple RawT)
ensureExprPresent n met = case met of
  (Just e,Just t) -> return $ updateAnnotation (Just t) e
  (Just e,_     ) -> return e
  _               -> noBindingErr n


modBuilder :: TopStmtSimple RawT -> ModuleParts UncheckedExpr -> Err (ModuleParts UncheckedExpr)
modBuilder t (ModuleParts mn ee pe te ds) = case t of
  -- TypeDecls may not fail
  TopTypeDecl n pt -> case M.lookup n ee of
                      Just (_,Just _) -> multiDeclErr n
                      _               -> return $ ModuleParts mn (intoExprEnv (newTypeDecl pt) n ee) pe te ds
  -- Multiple binds to the same name will fail
  TopBind n e      -> case M.lookup n ee of
                      Just (Just _,_) -> multiDeclErr n
                      _               -> return $ ModuleParts mn (intoExprEnv (newBind e) n ee) pe te ds
  -- Multiple declarations of the same type synonym will fail
  TypeDef n pt     -> if M.member n te
                      then multiDeclErr n
                      else return $ ModuleParts mn ee pe (M.insert n (newTypeSyn pt) te) ds
  -- Multiple declarations of an abstract type will fail
  AbsTypeDecl n    -> if M.member n te
                      then multiDeclErr n
                      else return $ ModuleParts mn ee pe (M.insert n newAbsType te) ds
  Prim n ty        -> if M.member n pe
                      then multiDeclErr n
                      else return $ ModuleParts mn ee (M.insert n ty pe) te ds
  -- Imports show dependencies
  Import n _ _     -> return $ ModuleParts mn ee pe te (S.insert n ds)

-- BuildEnv --------------------------------------------------------------------

intoExprEnv :: (Maybe UncheckedExpr -> UncheckedExpr) -> Name -> Env UncheckedExpr -> Env UncheckedExpr
intoExprEnv f n = M.alter (Just . f) n

-- If the name is bound already, add the RawSigT to the others,
--  otherwise start a new list.
newTypeDecl :: RawSigT -> Maybe UncheckedExpr -> UncheckedExpr
newTypeDecl pt = maybe (Nothing,Just pt) (second (Just pt `mplus`))

-- The fst of the resulting tuple will always be (Just e).
--  If the name wasn't bound already, bind it.
newBind :: ExprSimple RawT -> Maybe UncheckedExpr -> UncheckedExpr
newBind e = maybe (Just e,Nothing) (first $ const $ Just e)

newTypeSyn :: RawSigT -> RawT
newTypeSyn = Just

newAbsType :: RawT
newAbsType = Nothing

-- Error Messages --------------------------------------------------------------

multiDeclErr :: Name -> Err a 
multiDeclErr n = fail ("Multiple declarations of '" ++ n ++ "'")

noBindingErr :: Name -> Err a
noBindingErr n = fail ("The type signature for '" ++ n ++ "' lacks an accompanying binding.")

-- Dependency Analysis ---------------------------------------------------------

buildQueue :: ModMap e -> [ModuleParts e]
buildQueue mm = map (flip findModule mm . (findInMap vertModMap)) depOrder
  where
  modNms     = M.keys $ modMap mm
  numMs      = length modNms - 1
  modVertMap = M.fromList $ zip modNms [0..]
  vertModMap = M.fromList $ zip [0..] modNms

  depOrder   = G.topSort $ G.buildG bounds edges
  bounds     = (0,numMs)
  edges      = [ (from,to)
               | fromM    <- modNms
               , let from =  findInMap modVertMap fromM
               , toM      <- S.toList $ modDeps $ findModule fromM mm
               , let to   =  findInMap modVertMap toM
               ]

findModule :: ModuleName -> ModMap e -> ModuleParts e
findModule mn mm = findInMap (modMap mm) mn

findInMap :: (Ord k, Show k) => M.Map k a -> k -> a
findInMap m k = case M.lookup k m of
  Just a  -> a
  Nothing -> error $ "Couldn't find element " ++ show k ++ " in Map"

-- Backward Compatibility ------------------------------------------------------

#if __GLASGOW_HASKELL__ < 706
traverseWithKey :: (Applicative t, Ord k) => (k -> a -> t b) -> M.Map k a -> t (M.Map k b)
traverseWithKey f s =
  fmap M.fromList (T.traverse (\(k, v) -> fmap ((,) k) (f k v)) (M.toList s))
#else
traverseWithKey :: Applicative t => (k -> a -> t b) -> M.Map k a -> t (M.Map k b)
traverseWithKey = M.traverseWithKey
#endif
