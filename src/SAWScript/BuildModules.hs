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
import Control.Monad
import Data.Foldable (foldrM)
import qualified Data.Graph as G
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as T

-- Types -----------------------------------------------------------------------

type Incoming = LoadedModules
type Outgoing = [ModuleParts]

type CheckedExpr   = ExprSimple RawT

data ModuleParts = ModuleParts
  { modName :: ModuleName
  , modExprEnv :: [(LName, CheckedExpr)]
  , modPrimEnv :: LEnv RawT
  , modTypeEnv :: LEnv RawT
  , modDeps    :: S.Set ModuleName
  , modCryDeps :: [FilePath]
  } deriving (Show)

newtype ModMap = ModMap
  { modMap :: M.Map ModuleName ModuleParts
  } deriving (Show)

--------------------------------------------------------------------------------

-- | Combine every top-level type signature with the immediately
-- following value binding. The final result contains no occurrences
-- of TopTypeDecl.
combineTopTypeDecl :: [TopStmtSimple RawT] -> Err [TopStmtSimple RawT]
combineTopTypeDecl [] = return []
combineTopTypeDecl (TopTypeDecl name ty : TopBind name' e : stmts)
  | name == name' = (:) (TopBind name' (updateAnnotation (Just ty) e)) <$> combineTopTypeDecl stmts
combineTopTypeDecl (TopTypeDecl name _ : _) = noBindingErr name
combineTopTypeDecl (stmt : stmts) = (:) stmt <$> combineTopTypeDecl stmts

-- BuildEnv --------------------------------------------------------------------

buildModules :: Compiler Incoming Outgoing
buildModules = compiler "BuildEnv" $ \ms -> T.traverse (build >=> addPreludeDependency) >=> assemble
  $ M.assocs $ modules ms

addPreludeDependency :: ModuleParts -> Err ModuleParts
addPreludeDependency mparts@(ModuleParts mn ee pe te ds cs)
  | mn == preludeName = return mparts
  | otherwise = return $ ModuleParts mn ee pe te (S.insert preludeName ds) cs

preludeName :: ModuleName
preludeName = ModuleName [] "Prelude"

-- stage1: build tentative environment. expression vars may or may not have bound expressions,
--   but may not have multiple bindings.
build :: (ModuleName, [TopStmtSimple RawT]) -> Err ModuleParts
build (mn, ts) = foldrM modBuilder (ModuleParts mn [] M.empty M.empty S.empty []) =<< combineTopTypeDecl ts

-- stage3: make a module out of the resulting envs
assemble :: [ModuleParts] -> Err Outgoing
assemble mods = return $ buildQueue modM
  where
  modM = ModMap $ M.fromList [ (modName m,m) | m <- mods ]

modBuilder :: TopStmtSimple RawT -> ModuleParts -> Err ModuleParts
modBuilder t (ModuleParts mn ee pe te ds cs) = case t of
  -- Type signatures should have been translated away by this point
  TopTypeDecl _ _  -> fail "modBuilder: precondition failed (TopTypeDecl)"
  -- Duplicate declarations are listed multiple times; later ones should shadow earlier ones
  TopBind n e      -> return $ ModuleParts mn ((n, e) : ee) pe te ds cs
  -- Multiple declarations of the same type synonym will fail
  TypeDef n pt     ->
    if M.member n te
      then multiDeclErr n
      else return $ ModuleParts mn ee pe (M.insert n (newTypeSyn pt) te) ds cs
  -- Multiple declarations of an abstract type will fail
  AbsTypeDecl  n   ->
    if M.member n te
      then multiDeclErr n
      else return $ ModuleParts mn ee pe (M.insert n newAbsType te) ds cs
  Prim n ty -> if M.member n pe
                         then multiDeclErr n
                         else return $ ModuleParts mn ee (M.insert n ty pe) te ds cs
  -- Imports show dependencies
  Import n _ _     -> return $ ModuleParts mn ee pe te (S.insert n ds) cs
  ImportCry path   -> return $ ModuleParts mn ee pe te ds (path : cs)

-- BuildEnv --------------------------------------------------------------------

newTypeSyn :: RawSigT -> RawT
newTypeSyn = Just

newAbsType :: RawT
newAbsType = Nothing

-- Error Messages --------------------------------------------------------------

multiDeclErr :: LName -> Err a
multiDeclErr n = fail ("Multiple declarations of '" ++ getVal n ++ "' at " ++ show (getPos n))

noBindingErr :: LName -> Err a
noBindingErr n = fail ("The type signature for '" ++ getVal n ++ "' lacks an accompanying binding at " ++ show (getPos n))

-- Dependency Analysis ---------------------------------------------------------

buildQueue :: ModMap -> [ModuleParts]
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

findModule :: ModuleName -> ModMap -> ModuleParts
findModule mn mm = findInMap (modMap mm) mn

findInMap :: (Ord k, Show k) => M.Map k a -> k -> a
findInMap m k = case M.lookup k m of
  Just a  -> a
  Nothing -> error $ "Couldn't find element " ++ show k ++ " in Map"
