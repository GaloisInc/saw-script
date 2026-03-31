{-# LANGUAGE LambdaCase #-}
module SAWCoreIsabelle.CryptolDeps 
  ( mkCryptolDeps 
  , mkTyEnv
  , stripProofApps
  , containsName
  , moduleDepsOf
  , nameToModName
  , foldMapNames
  , CryptolDeps(..)
  , CryEntity(..) )
where

import           Control.Monad.Writer (execWriter, tell)

import qualified Data.Graph as Graph
import           Data.Hashable
import qualified Data.Map as Map
import           Data.Monoid (Any(..))
import qualified Data.Set as Set

import qualified Cryptol.ModuleSystem.Env as Cry
import qualified Cryptol.ModuleSystem.Name as Cry

import qualified Cryptol.TypeCheck.AST as Cry
import           Cryptol.IR.TraverseExprs
import           Cryptol.IR.TraverseNames
import           Cryptol.Utils.PP (pp)
import qualified Cryptol.Utils.Ident as Cry
import Data.Maybe (fromMaybe, fromJust)


instance Hashable CryEntity where
  hashWithSalt s = \case
    CryDecl d -> hashWithSalt s (show $ pp $ stripProofApps d)
    CryTySyn t -> hashWithSalt s (show $ pp t)
    CryNominalType nt -> hashWithSalt s (show $ pp nt)

data CryEntity = 
    CryDecl Cry.Decl
  | CryTySyn Cry.TySyn
  | CryNominalType Cry.NominalType

instance TraverseNames CryEntity where
  traverseNamesIP = \case
    CryDecl d -> CryDecl <$> traverseNamesIP d
    CryTySyn t -> CryTySyn <$> traverseNamesIP t
    CryNominalType nt -> CryNominalType <$> traverseNamesIP nt

cryEntityName :: CryEntity -> Cry.Name
cryEntityName = \case
  CryDecl d -> Cry.dName d
  CryTySyn t -> Cry.tsName t
  CryNominalType nt -> Cry.ntName nt

instance Eq CryEntity where
  ce1 == ce2 = (cryEntityName ce1 == cryEntityName ce2)

stripProofApps :: TraverseExprs t => t -> t
stripProofApps = mapSubExprs go
  where
    go = \case
      Cry.EProofAbs _ e -> e
      Cry.EProofApp e -> e
      e -> e

foldMapNames :: (TraverseNames t, Monoid m) => (Cry.Name -> m) -> t -> m
foldMapNames f t = execWriter $ traverseNames (\e -> tell (f e) >> return e) t

containsName :: TraverseNames t => Cry.Name -> t -> Bool
containsName nm t = getAny $ foldMapNames (\nm_ -> Any (nm == nm_)) t

modulesToCryEnv :: [Cry.Module] -> [CryEntity]
modulesToCryEnv ms = 
  let 
    decls = concat $ concatMap (map Cry.groupDecls . Cry.mDecls) ms
    tys = concatMap (Map.elems . Cry.mTySyns) ms
    tnms = concatMap (Map.elems . Cry.mNominalTypes) ms
  in map CryDecl decls ++ map CryTySyn tys ++ map CryNominalType tnms

data CryptolDeps = CryptolDeps 
  { entityDeps :: Map.Map Cry.Name (CryEntity, Set.Set Cry.Name)
  , moduleDeps :: Map.Map Cry.ModName (Cry.LoadedModule, Set.Set Cry.ModName)
  }

nameToModName :: Cry.Name -> Maybe Cry.ModName
nameToModName nm = case Cry.nameInfo nm of
  Cry.GlobalName _ og | Cry.TopModule mnm <- Cry.ogModule og -> Just mnm
  _ -> Nothing

collapseMaybeSet :: Ord a => Set.Set (Maybe a) -> Set.Set a
collapseMaybeSet = Set.map fromJust . Set.delete Nothing

moduleDepsOf :: TraverseNames t => CryptolDeps -> t -> Set.Set Cry.ModName
moduleDepsOf d = foldMapNames $ \nm -> 
  let dep_nms = fromMaybe Set.empty $ fmap snd $ Map.lookup nm (entityDeps d)
      dep_mods = collapseMaybeSet $ Set.map nameToModName dep_nms
      acc_deps mnm = Set.union (fromMaybe Set.empty $ fmap snd $ Map.lookup mnm (moduleDeps d))
  in Set.fold acc_deps Set.empty dep_mods

stripGuard :: Cry.Schema -> Cry.Schema
stripGuard (Cry.Forall vs _ t) = Cry.Forall vs [] t

mkTyEnv :: CryptolDeps -> Map.Map Cry.Name Cry.Schema
mkTyEnv ces = Map.mapMaybe go (entityDeps ces)
  where
    go = \case
      (CryDecl d,_) -> Just (stripGuard $ Cry.dSignature d)
      _ -> Nothing

mkCryptolDeps :: [Cry.LoadedModule] -> [Cry.DeclGroup] -> [Cry.TySyn] -> CryptolDeps
mkCryptolDeps lms extraDecls extraTys = 
  let edeps = cryEntityDeps $ modulesToCryEnv (map Cry.lmModule lms) 
       ++ map CryDecl (concat $ map Cry.groupDecls extraDecls)
       ++ map CryTySyn extraTys
      mdeps = cryModuleDeps lms
  in CryptolDeps edeps mdeps

collectNames :: TraverseNames t => t -> Set.Set Cry.Name
collectNames = foldMapNames $ \nm -> 
  case Cry.nameInfo nm of 
    Cry.LocalName{} -> Set.empty
    _ -> Set.singleton nm

cryEntityDeps :: 
  [CryEntity] ->
  Map.Map Cry.Name (CryEntity, Set.Set Cry.Name)
cryEntityDeps nes = 
  let
    raw_graph = map (\ne -> (ne, cryEntityName ne, Set.toList $ collectNames ne)) nes
    (gr,vert_to_node,nm_to_vert) = Graph.graphFromEdges raw_graph
    get_deps ne = case nm_to_vert (cryEntityName ne) of
      Just v -> foldr (\v' acc -> 
            let (_,_,deps) = vert_to_node v' in foldr Set.insert acc deps)
            Set.empty
            (Graph.reachable gr v) 
      Nothing -> Set.empty
  in Map.fromList $ map (\ne -> (cryEntityName ne, (ne, get_deps ne))) nes

cryModuleDeps :: 
  [Cry.LoadedModule] ->
  Map.Map Cry.ModName (Cry.LoadedModule, Set.Set Cry.ModName)
cryModuleDeps nes = 
  let
    raw_graph = map (\ne -> (ne, Cry.lmName ne, Set.toList $ Cry.fiImportDeps (Cry.lmFileInfo ne))) nes
    (gr,vert_to_node,nm_to_vert) = Graph.graphFromEdges raw_graph
    get_deps ne = case nm_to_vert (Cry.lmName ne) of
      Just v -> foldr (\v' acc -> 
            let (_,_,deps) = vert_to_node v' in foldr Set.insert acc deps)
            (Set.singleton (Cry.lmName ne))
            (Graph.reachable gr v) 
      Nothing -> Set.singleton (Cry.lmName ne)
  in Map.fromList $ map (\ne -> (Cry.lmName ne, (ne, get_deps ne))) nes