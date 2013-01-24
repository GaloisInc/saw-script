{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE DeriveTraversable #-} 
{-# LANGUAGE GADTs  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Verifier.SAW.Typechecker
  ( unsafeMkModule
  ) where

import Control.Applicative
import Control.Arrow ((***), first, second)
import Control.Exception (assert)

import Control.Monad (liftM2, liftM3, zipWithM_)
import Control.Monad.State hiding (forM, forM_, mapM, mapM_, sequence, sequence_)
import Control.Monad.Identity (Identity)
import Control.Monad.ST

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import Data.Traversable
import Data.Vector (Vector)
import qualified Data.Vector as V

import Prelude hiding ( all
                      , concat
                      , concatMap
                      , foldl
                      , foldr
                      , mapM
                      , mapM_
                      , sequence
                      , sequence_
                      , sum)

import Text.PrettyPrint

import Debug.Trace


import Verifier.SAW.Utils

import Verifier.SAW.Position
import Verifier.SAW.UntypedAST ( PosPair(..))
import Verifier.SAW.Typechecker.Common
import Verifier.SAW.TypedAST
import qualified Verifier.SAW.UntypedAST as Un

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y) 

mkEdgeMap :: Ord a => [(a,a)] -> Map a [a]
mkEdgeMap = foldl' fn Map.empty
  where fn m (x,y) = Map.insertWith (++) x [y] m

-- | Given a project function returning a key and a list of values, return a map
-- from the keys to values.
projMap :: Ord k => (a -> k) -> [a] -> Map k a
projMap f l = Map.fromList [ (f e,e) | e <- l ] 

flipPair :: (a,b) -> (b,a)
flipPair (x,y) = (y,x)

-- | Given a list of keys and values, construct a map that maps each key to the list
-- of values.
multiMap :: Ord k => [(k,a)] -> Map k [a]
multiMap = foldl' fn Map.empty
  where fn m (k,v) = Map.insertWith (++) k [v] m

orderedListMap :: Ord a => [a] -> Map a Int
orderedListMap l = Map.fromList (l `zip` [0..])

sepKeys :: Map k v -> ([k],[v])
sepKeys m = (Map.keys m, Map.elems m)

topSort :: forall a . Ord a
        => Set a -- List of vertices.
        -> [(a,a)] -- List of edges
        -> Either (Map a Int) [a]
topSort vertices e = go (initNulls, initMap) []
  where vl = Set.toList vertices
        outEdgeMap = mkEdgeMap e
        outEdges v = Map.findWithDefault [] v outEdgeMap
        inEdgeMap = mkEdgeMap (flipPair <$> e)
        -- Nodes that have edge to the given node. 
        inEdges :: a -> [a]
        inEdges v = Map.findWithDefault [] v inEdgeMap
        initNulls = filter (null . inEdges) vl
        initMap = Map.fromList [  (v,l) | v <- vl
                               , let l = length (inEdges v)
                               , l > 0
                               ]
        decInEdgeCount :: ([a], Map a Int) -> a -> ([a], Map a Int)
        decInEdgeCount (l,zm) v = 
            case Map.lookup v zm of
                    Nothing -> error "internal: topSort did not maintain edge count"
                    Just 1 -> (v:l, Map.delete v zm)
                    Just n -> assert (n > 1) $ (l, Map.insert v (n-1) zm)
        go :: ([a], Map a Int) -> [a] -> Either (Map a Int) [a]
        go ([],zm) r | Map.null zm = Right (reverse r)
                     | otherwise = Left zm
        go (h:l,zm) r = go (foldl' decInEdgeCount (l,zm) (outEdges h)) (h:r)

mapDefEqn :: (p -> q) -> (s -> t) -> DefEqnGen p s -> DefEqnGen q t
mapDefEqn pfn tfn (DefEqnGen pl rhs) = DefEqnGen (pfn <$> pl) (tfn rhs)

failPos :: Monad m => Pos -> String -> m a
failPos p msg = fail $ show p ++ ": " ++ msg
 

type DeBruijnLevel = DeBruijnIndex

-- Global context declarations.

-- | Rigid variable used during pattern unification.
data RigidVarRef s 
   = RigidVarRef { rvrIndex :: !Int
                 , rvrPos :: Pos
                 , rvrName :: String
                 , rvrType :: VarIndex s
                 }

instance Eq (RigidVarRef s) where
  (==) = lift2 rvrIndex (==)

instance Ord (RigidVarRef s) where
  compare = lift2 rvrIndex compare

instance Show (RigidVarRef s) where
  showsPrec p r = showParen (p >= 10) f
    where f = (++) (ppPos (rvrPos r) ++ " " ++ rvrName r)

-- | Local definition in its most generic form.
-- n is the identifier for name, p is the pattern, and t is the type.
-- The
-- The equations are typed in the context after all local variables are
data LocalDefGen n p t
   = -- | A Local function definition with position, name, type, and equations.
     -- Type is typed in context before let bindings.
     -- Equations are typed in context after let bindings.
     LocalFnDefGen Pos n t [DefEqnGen p t]
  deriving (Show)

localVarNamesCount :: [LocalDefGen n p e] -> DeBruijnLevel
localVarNamesCount = length

localVarNamesGen :: [LocalDefGen n p e] -> [n]
localVarNamesGen = fmap go
  where go (LocalFnDefGen _ nm _ _) = nm

data DefEqnGen p t
   = DefEqnGen [p]  -- ^ List of patterns
                t -- ^ Right hand side.
  deriving (Show)

-- | Type synonyms in untyped world.
type UnPat = (Un.ParamType, [Un.Pat])
type UnCtor = Ctor (PosPair String) Un.Term
type UnDataType = DataType (PosPair String) Un.Term
type UnDefEqn = DefEqnGen Un.Pat Un.Term
type UnLocalDef = LocalDefGen String Un.Pat Un.Term

-- | Global binding
data Binding t e
  = CtorIdent Ident t
  | DataTypeIdent Ident t
  | DefIdent Ident t e
    -- | A bound variable with its deBrujin level and type.
  | BoundVar String Int TCTerm
    -- | A local variable with its deBrujin level and equations.
  | LocalDef String Int TCTerm e

gbIdent :: Binding t e -> Ident
gbIdent (CtorIdent i _) = i
gbIdent (DataTypeIdent i _) = i
gbIdent (DefIdent i _ _) = i

mapBinding :: Applicative f
           => (tx -> f ty)
           -> (ex -> f ey)
           -> Binding tx ex
           -> f (Binding ty ey) 
mapBinding ft fe b =
  case b of
    CtorIdent i tp -> CtorIdent i <$> ft tp
    DataTypeIdent i tp -> DataTypeIdent i <$> ft tp
    DefIdent i tp eql -> liftA2 (DefIdent i) (ft tp) (fe eql)

type TCBinding r = Binding (r TCTerm) (r [TCDefEqn])

type TCRefGlobalBinding s = TCBinding (TCRef s)

data TermContext s = TermContext {
    -- | Typed module built from imports.
    tcModule :: Module
  , tcBindings :: Map Un.Ident (TCBinding (TCRef s))
   -- | Maps global typed identifiers to definitions.
  , tcIdentBindings :: Map Ident (TCBinding (TCRef s))
  , tcIndexedBindings :: ![TCBinding (TCRef s)]
  , tcLevel :: Int
  }

tcModuleName :: TermContext s -> ModuleName
tcModuleName = moduleName . tcModule

-- | Add a bound var to the context.
consBoundVar :: String -> TCTerm -> TermContext s -> TermContext s
consBoundVar nm tp tc = 
     tc { tcBindings = Map.insert (Un.localIdent nm) b (tcBindings tc)
        , tcIndexedBindings = b:tcIndexedBindings tc
        , tcLevel = tcLevel tc + 1
        }
 where b = BoundVar nm (tcLevel tc) tp

{-
tcFindLocalBinding :: PosPair Un.Ident -> TermContext s -> TC s UnifyTerm
tcFindLocalBinding pi tc = do
  let localRes = fst <$> Map.lookup (val pi) (tcVarBindings tc)
  let globalRes = do
        DefIdent i _ _ <- Map.lookup (val pi) (tcGlobalBindings tc)
        return $ UGlobal i
  case mplus localRes globalRes of
    Just t -> return t
    Nothing -> failPos (pos pi) $ show (val pi) ++ " unbound in current context."
-}

{-
bindLocalTerm :: String -> UnifyTerm -> UnifyTerm -> TermContext s -> TermContext s
bindLocalTerm nm t tp ctx = ctx { tcVarBindings = Map.insert (Un.localIdent nm) (t,tp) m }
  where m = tcVarBindings ctx

addLocalBindings :: TermContext s -> [RigidVarRef] -> TermContext s
addLocalBindings tc l = tc { tcBindings = foldl' fn (tcBindings ctx) l }
  where fn m r = Map.insert (Un.localIdent (rvrName r))
                            (URigidVar r, UUndefinedVar (rvrType r))
                            m
-}

-- | Organizes information about local declarations.
type LocalDeclsGroup = [UnLocalDef]

type GroupLocalDeclsState = ( Map String (PosPair String, Un.Term)
                            , Map String [UnDefEqn]
                            )

groupLocalDecls :: [Un.Decl] -> LocalDeclsGroup
groupLocalDecls = finalize . foldl groupDecl (Map.empty,Map.empty)
  where finalize :: GroupLocalDeclsState -> LocalDeclsGroup
        finalize (tpMap,eqMap) = fn <$> Map.elems tpMap
          where fn :: (PosPair String, Un.Term) -> UnLocalDef
                fn (PosPair p nm,tp) = LocalFnDefGen p nm tp eqs
                  where Just eqs = Map.lookup nm eqMap
        groupDecl :: GroupLocalDeclsState -> Un.Decl -> GroupLocalDeclsState
        gr oupDecl (tpMap,eqMap) (Un.TypeDecl idl tp) = (tpMap',eqMap)
          where tpMap' = foldr (\k -> Map.insert (val k) (k,tp)) tpMap idl
        groupDecl (tpMap,eqMap) (Un.TermDef pnm pats rhs) = (tpMap, eqMap')
          where eq = DefEqnGen (snd <$> pats) rhs
                eqMap' = Map.insertWith (++) (val pnm) [eq] eqMap
        groupDecl _ Un.DataDecl{} = error "Unexpected data declaration in let binding"

data PatF p
   = UPTuple [p]
   | UPRecord (Map FieldName p)
   | UPCtor Ident [p]
  deriving (Functor, Foldable, Traversable, Show)

zipWithPatF :: (x -> y -> z) -> PatF x -> PatF y -> Maybe (PatF z)
zipWithPatF f = go
  where go (UPTuple lx) (UPTuple ly)
          | length lx == length ly = Just $ UPTuple (zipWith f lx ly)
        go (UPRecord mx) (UPRecord my)
          | Map.keys mx == Map.keys my =Just $ UPRecord (Map.intersectionWith f mx my)
        go (UPCtor cx lx) (UPCtor cy ly)
          | cx == cy = Just $ UPCtor cx (zipWith f lx ly)
        go _ _ = Nothing

{-
upatToTerm :: UPat  -> UnifyTerm
upatToTerm (UPVar r) = URigidVar r
upatToTerm (UPUnused i) = UUndefinedVar i
upatToTerm (UPatF _ pf) =
  case pf of
    UPTuple l  -> UTF $ UTupleValue  (upatToTerm <$> l)
    UPRecord m -> UTF $ URecordValue (upatToTerm <$> m)
    UPCtor c l -> UTF $ UCtorApp c   (upatToTerm <$> l)
-}



data TCTermF t
    -- | A global definition identifier.
  = UGlobal Ident

  | UApp t t

  | UTupleValue [t]
  | UTupleType [t]

  | URecordValue (Map FieldName t)
  | URecordSelector t FieldName
  | URecordType (Map FieldName t)

  | UCtorApp Ident [t]
  | UDataType Ident [t]

  | USort Sort
 
  | UIntLit Integer
  | UArray t (Vector t)

  deriving (Show, Functor, Foldable, Traversable)

zipWithTCTermF :: (x -> y -> z) -> TCTermF x -> TCTermF y -> Maybe (TCTermF z)
zipWithTCTermF f = go
  where go (UGlobal x) (UGlobal y) | x == y = pure $ UGlobal x
        go (UApp fx vx) (UApp fy vy) = pure $ UApp (f fx fy) (f vx vy)

        go (UTupleValue lx) (UTupleValue ly)
          | length lx == length ly = pure $ UTupleValue (zipWith f lx ly)
        go (UTupleType lx) (UTupleType ly)
          | length lx == length ly = pure $ UTupleType (zipWith f lx ly)

        go (URecordValue mx) (URecordValue my)
          | Map.keys mx == Map.keys my = 
              pure $ URecordValue $ Map.intersectionWith f mx my 
        go (URecordSelector x fx) (URecordSelector y fy)
          | fx == fy = pure $ URecordSelector (f x y) fx
        go (URecordType mx) (URecordType my)
          | Map.keys mx == Map.keys my = 
              pure $ URecordType (Map.intersectionWith f mx my) 

        go (UCtorApp cx lx) (UCtorApp cy ly)
          | cx == cy = pure $ UCtorApp cx (zipWith f lx ly)
        go (UDataType dx lx) (UDataType dy ly)
          | dx == dy = pure $ UDataType dx (zipWith f lx ly)
        go (USort sx) (USort sy) | sx == sy = pure (USort sx)
        go (UIntLit ix) (UIntLit iy) | ix == iy = pure (UIntLit ix)
        go (UArray tx vx) (UArray ty vy)
          | V.length vx == V.length vy = pure $ UArray (f tx ty) (V.zipWith f vx vy)

        go _ _ = Nothing

type TCLocalDef = LocalDefGen Ident (TCPat TCTerm) TCTerm

{-
-- | TCLocalInfo defines the total number 
data TCLocalInfo = TCLocalInfo { tcliTotal :: DeBruijnLevel
                               , tcliLevel :: DeBruijnLevel
                               , tcliEqns :: [TCDefEqn]
                               } deriving (Show)
-}

data TCTerm
  = TCF Pos (TCTermF TCTerm)
  | TCLambda (TCPat TCTerm) TCTerm TCTerm
  | TCPi (TCPat TCTerm) TCTerm TCTerm
  | TCLet Pos [TCLocalDef] TCTerm
    -- | A local variable with its deBruijn index and type in the current context.
  | TCVar Pos String DeBruijnIndex TCTerm
    -- | A reference to a let bound function with equations.
  | TCLocalDef Pos
               -- | Name
               String
               -- | Index of variable.
               DeBruijnIndex 
               -- | Type 
               TCTerm
 deriving (Show)

data TCPat tp = TCPVar Pos String DeBruijnIndex tp
              | TCPUnused Pos -- ^ Unused pattern
              | TCPatF Pos (PatF (TCPat tp))
  deriving (Show)

instance Positioned (TCPat tp) where
  pos (TCPVar p _ _ _) = p
  pos (TCPUnused p) = p
  pos (TCPatF p _) = p

data UVarState s
    -- | Indicates this var is equivalent to another.
  = UVar (VarIndex s)
  | URigidVar (RigidVarRef s) -- ^ Rigid variable that cannot be instantiated.
    -- | A unused pattern variable with its type.
  | UUnused String (VarIndex s)
    -- | A free variable with no name.
  | UFreeType String
    -- | A higher order term that is not parsed during unification, possibly with
    -- some of the free variables substituted by indices.
    -- The term may be assumed to be a type expression, and the variables are arguments
    -- to instantiate it.
  | UHolTerm TCTerm -- Type with free variables.
             TCTerm -- Type as pi expression
             [VarIndex s] -- Variables bound to type.
  | UTF (TCTermF (VarIndex s))
    -- A variable bound outside the context of the unification problem with name and type
    -- relative to when before unification began.
  | UOuterVar String
              -- Number of variables quantified during parsing before this one.
              DeBruijnLevel
              -- DeBruijnIndex in original context.
              DeBruijnIndex
              -- Type of term in original context.
              TCTerm
 deriving (Show)  

{-
data UPi = UPi (TCPat (VarIndex s)) (VarIndex 
-}

data UPat s
  = UPVar (RigidVarRef s)
  | UPUnused (VarIndex s)
  | UPatF Un.Pos (PatF (UPat s))
  deriving (Show)

{-
upatBoundVars :: UPat s -> [RigidVarRef s]
upatBoundVars (UPVar v) = [v]
upatBoundVars UPUnused{} = []
upatBoundVars (UPatF _ pf) = concatMap upatBoundVars pf

upatBoundVarCount :: UPat s -> DeBruijnIndex
upatBoundVarCount UPVar{} = 1
upatBoundVarCount UPUnused{} = 0
upatBoundVarCount (UPatF _ pf) = sumBy upatBoundVarCount pf
-}

{-
addUnifyTermVars :: Set UVar -> UnifyTerm -> Set UVar
addUnifyTermVars = go
  where go s (URigidVar sym) = Set.insert (UPRigid sym) s
        go s (ULambda _ x y) = go (go s x) y
        go s (UApp x y)      = go (go s x) y
        go s (UPi _ x y)     = go (go s x) y
        go s (UTupleValue l) = foldl' go s l
        go s (UTupleType l)  = foldl' go s l
        go s (URecordValue m) = foldl' go s m
        go s (URecordSelector x _) = go s x
        go s (URecordType m) = foldl' go s m
        go s (UCtorApp _ l) = foldl' go s l
        go s (UDataType _ l) = foldl' go s l
        go s (ULet _ x) = go s x
        go s (UArray x v) = foldl' go (go s x) v
        go s (UUndefinedVar i) = Set.insert (UIVar i) s
        go s _ = s

data UnifyEq
    -- | Assert two terms are equal types (i.e., have type Set a for some a).
  = UnifyPatHasType UPat UnifyTerm

data VarBinding = TypeBinding UnifyTerm
                  -- | ValueBinding contains term and type.
                | ValueBinding UnifyTerm UnifyTerm

varBindingTerm :: VarBinding -> UnifyTerm
varBindingTerm (TypeBinding t) = t
varBindingTerm (ValueBinding t _) = t

type UnifyDefEqn = DefEqnGen (UPat RigidVarRef VarIndex) UnifyTerm
-}

data DefGen t e = DefGen !Ident !t !e


type TCDataType = DataType Ident TCTerm
type TCDef = DefGen TCTerm [TCDefEqn]
type TCDefEqn = DefEqnGen (TCPat TCTerm) TCTerm

type TCRefDataType s = DataType Ident (TCRef s TCTerm)
type TCRefCtor s = Ctor Ident (TCRef s TCTerm)
type TCRefDef s = DefGen (TCRef s TCTerm) (TCRef s [TCDefEqn])

incTCPatVars :: DeBruijnLevel -> DeBruijnIndex -> TCPat TCTerm -> TCPat TCTerm
incTCPatVars l j (TCPVar p nm i tp) = TCPVar p nm i (incTCVars (l+i) j tp)
incTCPatVars l j (TCPUnused p) = TCPUnused p
incTCPatVars l j (TCPatF p pf) = TCPatF p (incTCPatVars l j <$> pf)

tcPatVarCount :: TCPat TCTerm -> DeBruijnLevel
tcPatVarCount TCPVar{} = 1 
tcPatVarCount TCPUnused{} = 0
tcPatVarCount (TCPatF _ pf) = sum (tcPatVarCount <$> pf)

incTCDefEqn :: DeBruijnLevel -> DeBruijnIndex -> TCDefEqn -> TCDefEqn
incTCDefEqn l j (DefEqnGen pl r) = DefEqnGen pl' r'
  where pl' = incTCPatVars l j <$> pl
        r' = incTCVars (l+ sum (tcPatVarCount <$> pl)) j r

incTCLocalDefs :: DeBruijnLevel -> DeBruijnIndex -> [TCLocalDef] -> [TCLocalDef]
incTCLocalDefs l j defs = go <$> defs
  where l' = l + length defs
        go (LocalFnDefGen p nm tp eqs) = LocalFnDefGen p nm tp' eqs'
          where tp' = incTCVars l j tp
                eqs' = incTCDefEqn l' j <$> eqs

-- | Increment free vars in TC term by given amount if the index is at least the given level.
-- This is used for inserting extra variables to a context.
incTCVars :: DeBruijnLevel -> DeBruijnIndex -> TCTerm -> TCTerm
incTCVars l j (TCF p tf) = TCF p $ incTCVars l j <$> tf
incTCVars l j (TCLambda p tp r) = TCLambda p' tp' r'
  where p' = incTCPatVars l j p
        tp' = incTCVars l j tp
        r' = incTCVars (l+tcPatVarCount p) j r
incTCVars l j (TCPi p tp r) = TCPi p' tp' r'
  where p' = incTCPatVars l j p
        tp' = incTCVars l j tp
        r' = incTCVars (l+tcPatVarCount p) j r
incTCVars l j (TCLet p lcls t) = TCLet p lcls' t'
  where lcls' = incTCLocalDefs l j lcls
        t' = incTCVars (l+localVarNamesCount lcls) j t
incTCVars l j (TCVar p nm i tp) = TCVar p nm i' (incTCVars l j tp)
  where i' = if i >= l then i+j else i
incTCVars l j (TCLocalDef p nm i tp) = TCLocalDef p nm i' (incTCVars l j tp)
  where i' = if i >= l then i+j else i

tcApply :: TCTerm -> [TCTerm] -> TCTerm
tcApply t l = unimpl "tcApply"

instance Positioned TCTerm where
  pos (TCF p tf) = p
  pos (TCLambda p _ _) = pos p
  pos (TCPi p _ _) = pos p
  pos (TCLet p _ _) = p
  pos (TCVar p _ _ _) = p
  pos (TCLocalDef p _ _ _) = p

tctFail :: TCTerm -> Doc -> TC s a
tctFail t d = tcFail (pos t) $ show d

{-
-- | Add untyped pat bindings to context, each of which have the given type,
consPatVars :: TermContext s
            -> [Un.Pat]
            -> UnifyTerm
            -> TC s (TermContext s, [UPat])
consPatVars ctx upl tp = do
  pl <- mapM indexUnPat upl
  mapM_ (\p -> hasType p tp) pl
  let ctx' = addLocalBindings ctx (concatMap upatBoundVars pl)
  return (ctx', pl)

-- | Create a set of constraints for matching a list of patterns against a given pi type.
instPiType :: [UPat] -- ^ Patterns to match
           -> UnifyTerm -- ^ Expected pi type 
           -> TC s UnifyTerm
instPiType = go
  where go [] ltp = return ltp
        go (p:pl) ltp =
          case ltp of
            UPi pat lhs rhs -> do
              hasType p lhs
              let lhsSub = matchPat (upatToTerm p) pat
              rhs' <- applyUnifyPatSub lhsSub rhs
              go pl rhs' 
            _ -> internalError $ "Could not parse " ++  show ltp ++ " as pi type"

convertEqn :: TermContext s
           -> UnifyTerm
           -> UnDefEqn
           -> TC s UnifyDefEqn
convertEqn ctx tp (DefEqnGen unpats unrhs) = do
  pats <- mapM indexUnPat unpats
  rhsTp <- instPiType pats tp
  let ctx' = addLocalBindings ctx (concatMap upatBoundVars pats)
  rhs <- typecheckTerm ctx' unrhs rhsTp
  return (DefEqnGen pats rhs)

-- | Insert local definitions the terms belong to the given context.
consLocalDecls :: TermContext s -> [Un.Decl] -> TC s (TermContext s, [UnifyLocalDef])
consLocalDecls tc udl = do
  let procDef (LocalFnDefGen pnm utp ueqs) = do
        let nm = val pnm
        r <- newRigidVar (Just (pos pnm)) nm
        (tp,_) <- typecheckAnyTerm tc utp
        setRigidVarType r tp
        return (r, (r, tp, ueqs))
  (nl,dl') <- unzip <$> mapM procDef (groupLocalDecls udl)
  let tc1 = addLocalBindings tc nl
  let procEqns (r, tp, ueqs) = do
        res <- forM ueqs $ \(DefEqnGen unpat unrhs) -> do
          pat <- mapM indexUnPat unpat
          rhsTp <- instPiType pat tp
          let tc2 = addLocalBindings tc1 (concatMap upatBoundVars pat)
          rhs <- typecheckTerm tc2 unrhs rhsTp
          return (DefEqnGen pat rhs)
        return (LocalFnDefGen r tp res)
  dl <- mapM procEqns dl'
  return (tc1, dl)

headNormalForm :: UnifyTerm -> TC s UnifyTerm
headNormalForm t =
  case t of
    UUndefinedVar i -> do
      vb <- gets usVarBindings
      case Map.lookup i vb of
        Nothing -> return t
        Just (TypeBinding u) -> headNormalForm u
        Just (ValueBinding u _) -> headNormalForm u 
    ULambda{} -> return t
    UPi{} -> return t

    UTupleValue{} -> return t
    UTupleType {} -> return t

    URecordValue{} -> return t
    URecordSelector x f -> do
      hnf <- headNormalForm x
      case hnf of
        URecordValue m | Just v <- Map.lookup f m ->
          return v
        _ -> return t
    URecordType{} -> return t
    UCtorApp{} -> return t
    UDataType{} -> return t
    USort{} -> return t
    _ -> error $ "headNormalForm\n" ++ show t

lookupTermRef :: UnifyTermRef -> TC s UnifyTerm
lookupTermRef r = do
  s <- get
  case Map.lookup r (usTermRefMap s) of
    Nothing -> internalError "Could not find value for ref" 
    Just (WellTypedTerm t) -> return t
    Just (UntypedTerm ctx ut) -> do
      put s { usTermRefMap = Map.insert r ActiveRef (usTermRefMap s)
            , usUntypedTerms = Set.delete r (usUntypedTerms s)
            }
      (t,_) <- typecheckAnyTerm ctx ut
      modify $ \s' ->
          s' { usTermRefMap = Map.insert r (WellTypedTerm t) (usTermRefMap s)
             }
      return t
    Just ActiveRef -> fail $ ppPos (pos sym) ++ " Cycle detected during typechecking: "
                               ++ show (val sym)
      where sym = utrIdent r

-- | @chkPiUnTermList@ checks 
chkPiUnTermList :: TermContext s -> [Un.Term] -> UnifyTerm -> TC s ([UnifyTerm],UnifyTerm)
chkPiUnTermList ctx = go []
  where go al [] rhs = return (reverse al, rhs)
        go al (ua:r) (UPi lhs lhsType rhs) = do
          a <- typecheckTerm ctx ua lhsType
          let sub = matchPat a lhs
          rhs' <- headNormalForm =<< applyUnifyPatSub sub rhs
          go (a:al) r rhs'
-}

{-
typecheckEq :: UnifyTerm -> UnifyTerm -> TC s ()
--typecheckEq x y = error $ "typecheckEq undefined\n" ++ show x
typecheckEq _ _ = return ()
-}

--data UVarRepState = UVRS { uvrs :: 

data VarIndex s = VarIndex { viIndex :: !Int
                           , viPos :: Pos
                           , viName :: String
                           , viRef :: STRef s (UVarState s)
                           }

instance Eq (VarIndex s) where
  (==) = lift2 viIndex (==)

instance Ord (VarIndex s) where
  compare = lift2 viIndex compare

instance Show (VarIndex s) where
  show = unimpl "Show VarIndex"

instance Positioned (VarIndex s) where
  pos = viPos

data UnifierState s =
  US { usGlobalContext :: TermContext s
     , usBoundCtors :: Map Un.Ident (Ident,VarIndex s)
     , usVarCount :: Int
     , usRigidCount :: Int
     }

type Unifier s = StateT (UnifierState s) (TC s)

unFail :: Pos -> Doc -> Unifier s a
unFail p msg = lift (tcFail p (show msg))

mkVar :: Pos -> String -> UVarState s -> Unifier s (VarIndex s)
mkVar p nm vs = do
  vr <- lift $ liftST $ newSTRef vs
  s <- get
  let vidx = usVarCount s
      v = VarIndex { viIndex  = vidx
                   , viPos = p
                   , viName = nm
                   , viRef = vr
                   }
  v <$ put s { usVarCount = vidx + 1 }
 
newRigidVar :: Un.Pos -> String -> VarIndex s -> Unifier s (RigidVarRef s)
newRigidVar p nm tp = do
  s <- get
  let idx = usRigidCount s
  let rv = RigidVarRef { rvrIndex = idx
                       , rvrPos = p
                       , rvrName = nm
                       , rvrType = tp
                       }
  rv <$ put s { usRigidCount = idx + 1 }

-- | Lookup ctor returning identifyies and type.
lookupUnifyCtor :: PosPair Un.Ident -> Int -> Unifier s (Ident, TCTerm)
lookupUnifyCtor (PosPair p nm) argc = do
  -- TODO: Check argument count matches expected.
  bm <- gets (tcBindings . usGlobalContext)
  case Map.lookup nm bm of
    Just (CtorIdent c tp) -> (c,) <$> lift (eval p tp)
    Just DataTypeIdent{} -> unFail p $ text $ "Cannot match data types."
    Just _ -> fail "Unexpected ident type"
    Nothing -> unFail p $ text $ "Unknown symbol: " ++ show nm ++ "."

ppUTerm :: UVarState s -> Doc
ppUTerm _ = unimpl "ppUTerm"

usetEqual :: VarIndex s -> VarIndex s -> Unifier s ()
usetEqual vx vy | viRef vx == viRef vy = pure ()
usetEqual vx vy = do
  x <- lift $ liftST $ readSTRef (viRef vx)
  y <- lift $ liftST $ readSTRef (viRef vy)
  case (x,y) of
    (UVar vz,_) -> usetEqual vz vy
    (_,UVar vz) -> usetEqual vx vz
    (URigidVar rx, URigidVar ry) | rx == ry -> pure ()
    (UTF ufx, UTF ufy)
      | Just ufz <- zipWithTCTermF usetEqual ufx ufy -> sequence_ ufz
  
    (UFreeType nm, _) -> lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    (_, UFreeType nm) -> lift $ liftST $ writeSTRef (viRef vy) (UVar vx)
    -- We only merge unused with counterparts that are not free types.
    (UUnused nm _, _) -> lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    (_, UUnused nm _) -> lift $ liftST $ writeSTRef (viRef vy) (UVar vx)
    -- We have very limited support for dealing with higher-order types.
    -- They must match exactly.
    (UHolTerm _ txf cx, UHolTerm _ tyf cy) | length cx == length cy -> do
      -- Check that txf and tyf are equivalent
      tc <- gets usGlobalContext
      lift $ checkTypesEqual tc txf tyf
      -- Unify corresponding entries in cx and cy.
      zipWithM usetEqual cx cy
      -- Set vx to point to vy.
      lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    _ -> unFail (pos vy) $ vcat [ text "Do not support unifying types:"
                                , text "Type 1"
                                , nest 2 (ppUTerm x)
                                , text "Type 2"
                                , nest 2 (ppUTerm y)
                                ]
{-
-- | @usetEqual x y@ attempts to unify @x@ and @y2.
-- Positions in @y@ are used for pretty printing purposes.
usetEqual :: UnifyTerm s -> UnifyTerm s -> Unifier s ()
usetEqual tx@(URigidVar x) ty@(URigidVar y) =
  unless (x == y) $ unFail (rvrPos y) $
     text "Failed to unify distinct terms" <+> ppUTerm tx <+> text "and"
                                           <+> ppUTerm ty <> char '.'
usetEqual (UFlexVar v) t = unimpl "usetEqual"
usetEqual t (UFlexVar v) = usetEqual (UFlexVar v) t
usetEqual x y = unimpl "usetEqual" x y
-}

-- | Return true if set has duplicates.
hasDups :: Ord a => [a] -> Bool
hasDups l = Set.size (Set.fromList l) < length l

ppUnPat :: Un.Pat -> Doc
ppUnPat _ = unimpl "ppUnPat"

-- | Create a upat from a untyped pat, and return term representing it's type.
indexUnPat :: Un.Pat -> Unifier s (UPat s, VarIndex s)
indexUnPat upat =
  case upat of
    Un.PVar (PosPair p nm) -> do
        tp <- mkVar p ("type of " ++ nm) (UFreeType nm)
        let fn r = (UPVar r,tp)
        fn <$> newRigidVar p nm tp
    Un.PUnused (PosPair p nm) -> do
      tpv <- mkVar p ("type of " ++ nm) (UFreeType nm)
      (\v -> (UPUnused v, tpv)) <$> mkVar p nm (UUnused nm tpv)
    Un.PTuple p l -> fn . unzip =<< traverse indexUnPat l
      where fn (up,utp) =
              (UPatF p (UPTuple up),) <$> mkVar p (show (ppUnPat upat)) (UTF (UTupleType utp))
    Un.PRecord p fpl
        | hasDups fl -> unFail p $ text "Duplicate field names in pattern."
        | otherwise -> fn . unzip =<< traverse indexUnPat pl
      where (fmap val -> fl,pl) = unzip fpl
            vfn upl = UPatF p $ UPRecord   $ Map.fromList $ fl `zip` upl
            fn (upl,tpl) =
              (vfn upl,) <$> mkVar p (show (ppUnPat upat))
                                     (UTF $ URecordType $ Map.fromList $ fl `zip` tpl)
    Un.PCtor pnm pl -> do
      (c,tp) <- lookupUnifyCtor pnm (length pl)
      let vfn upl = UPatF (pos pnm) (UPCtor c upl)
      tc <- gets usGlobalContext
      first vfn <$> indexPiPats tc pl tp

-- | Match a typed pat against an untyped pat.
-- The types in the pattern are relative to the given unify local context.
matchUnPat :: UnifyLocalCtx s
           -> TCPat TCTerm
           -> Un.Pat
           -> Unifier s (UPat s,UnifyLocalCtx s)
matchUnPat il itcp iup = do
    (up,m) <- runStateT (go itcp iup) Map.empty
    (up,) <$> extendLocalCtx (Map.elems m) il
  where err p = lift $ unFail p $ text "Failed to match pattern against type."
        go :: TCPat TCTerm -> Un.Pat
           -> StateT (Map Int (LocalCtxBinding s))
                     (Unifier s)
                     (UPat s) 
        go (TCPVar p nm i tp) unpat = StateT $ \m -> second (fn m) <$> indexUnPat unpat
           where fn m utp = Map.insert i (utp,p,nm,tp) m
        go TCPUnused{} unpat = StateT $ \m ->
           second (const m) <$> indexUnPat unpat
        go (TCPatF _ pf) unpat =
          case (pf, unpat) of
            (UPTuple pl, Un.PTuple p upl)
              | length pl == length upl ->
                 UPatF p . UPTuple <$> zipWithM go pl upl
            (UPRecord pm, Un.PRecord p fpl)
                | Map.size um < length fpl -> lift $
                    unFail p $ text "Duplicate field names in pattern."
                | Map.keys pm == Map.keys um ->
                    UPatF p . UPRecord <$> sequence (Map.intersectionWith go pm um)
              where um = Map.fromList $ first val <$> fpl
            (UPCtor c pl, Un.PCtor pnm upl) -> do
              (c',_) <- lift $ lookupUnifyCtor pnm (length upl)
              unless (c == c') (err (pos pnm))
              UPatF (pos pnm) . UPCtor c <$> zipWithM go pl upl
            _ -> err (pos unpat)

-- | The term should be typed to be valid in the global term context for the unifier.
indexPiPats :: TermContext s -> [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
indexPiPats tc = go [] (emptyLocalCtx tc)
  where go :: -- | Previous patterns 
              [UPat s]
              -- | Terms for substution.
           -> UnifyLocalCtx s
           -> [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
        go ppats lctx [] tp =
          (reverse ppats,) <$> mkUnifyTerm lctx tp
        go ppats lctx (unpat:upl) tp = do
          (p,_,r) <- lift (reduceToPiExpr (ulcTC lctx) tp)
          (up,lctx') <- matchUnPat lctx p unpat
          go (up:ppats) lctx' upl r

{-
indexPiPats = go []
  where go pr [] tp = pure (reverse pr,tp)
        go pr (up:upl) tp = do
          rtp <- unReduce tp
          case rtp of
            UPi pip pilhs pirhs -> do
             -- Match up against pip and get substitution
             go (undefined pip pilhs pr) upl (undefined pirhs)
-}

{-
newFlexVar 

  case pat of
    Un.PVar pnm -> 
    Un.PUnused pnm -> UPUnused <$> newFlexVar (Just (pos pnm)) (val pnm)
    Un.PTuple p pl   -> (UPatF (Just p) . UPTuple) <$> mapM indexUnPat pl
    Un.PRecord p fpl -> (UPatF (Just p) . UPRecord . Map.fromList . zip (val <$> fl))
                                   <$> mapM indexUnPat pl
      where (fl,pl) = unzip fpl
    Un.PCtor i l -> do
      tc <- gets usGlobalContext
      case Map.lookup (val i) (tcBindings tc) of
        Just (CtorIdent c _) -> do
          (UPatF (Just (pos i)) . UPCtor c) <$> mapM indexUnPat l 
        Just _ -> fail $ show (val i) ++ " does not refer to a constructor."
        Nothing -> fail $ "Unknown symbol " ++ show (val i)
-}

runUnifier :: TermContext s -> Unifier s v -> TC s v
runUnifier tc m = evalStateT m s0
  where s0 = US { usGlobalContext = tc
                , usVarCount = 0
                , usRigidCount = 0
                }

{-
-- | A unify local context contains is a list ordered by
-- deBruijnIndex mapping local variables to the associated term. 
type UnifyLocalCtx s = [(VarIndex s, TCTerm)]
-}

type LocalCtxBinding s = (VarIndex s, Pos, String, TCTerm)
 
data UnifyLocalCtx s = UnifyLocalCtx { ulcTC :: TermContext s
                                     , ulcBindings :: [LocalCtxBinding s]
                                     }

mkHolTerm :: UnifyLocalCtx s -> TCTerm -> (TCTerm,[VarIndex s])
mkHolTerm ulc = go [] (ulcBindings ulc)
  where go pr [] tp = (tp,pr)
        go pr ((v,p,nm,tp):r) t = go (v:pr) r (TCPi (TCPVar p nm 0 tp) tp t)

emptyLocalCtx :: TermContext s -> UnifyLocalCtx s
emptyLocalCtx tc = UnifyLocalCtx { ulcTC = tc, ulcBindings = [] }

-- | Returns number of bound variables in local context.
localCtxSize :: UnifyLocalCtx s -> Int
localCtxSize = length . ulcBindings

lookupLocalCtxVarIndex :: UnifyLocalCtx s -> Int -> Maybe (VarIndex s)
lookupLocalCtxVarIndex (ulcBindings -> l) i
    | i < length l = assert (i >= 0) $ Just v 
    | otherwise = Nothing
  where (v,_,_,_) = l !! i
  
extendLocalCtx :: [LocalCtxBinding s] -> UnifyLocalCtx s -> Unifier s (UnifyLocalCtx s)
extendLocalCtx (b@(utp,_,nm,tp):r) ulc = do
  usetEqual utp =<< mkUnifyTerm ulc tp
  let ulc' = UnifyLocalCtx { ulcTC = consBoundVar nm tp (ulcTC ulc)
                           , ulcBindings = b : ulcBindings ulc
                           }
  extendLocalCtx r ulc'
extendLocalCtx [] l = pure l

-- | Create a unify term from a term.  
mkUnifyTerm :: UnifyLocalCtx s
            -> TCTerm
            -> Unifier s (VarIndex s)
mkUnifyTerm l t =
    case t of
      TCF p tf -> mkTermVar . UTF =<< traverse (mkUnifyTerm l) tf
      TCLambda{} -> holTerm
      TCPi{} -> holTerm
      TCLet{} -> holTerm
      TCVar _ nm i tp -> mkVarVar nm i tp
      TCLocalDef _ nm i tp -> mkVarVar nm i tp
  where holTerm = mkTermVar (uncurry (UHolTerm t) (mkHolTerm l t))
        mkVarVar nm i tp =
          case lookupLocalCtxVarIndex l i of
            Just utp -> mkTermVar (UVar utp)
            Nothing -> mkTermVar (UOuterVar nm (localCtxSize l) i tp)
        mkTermVar = mkVar (pos t) (show (ppTCTerm t))

data UnifyResult s
   = UR { urTermContext :: TermContext s
        , urLevel :: DeBruijnLevel
        , urBoundMap :: UResolverCache s (VarIndex s) (DeBruijnLevel, TCTerm)
        -- | Cache that maps variables to their typechecked value at the
        -- given deBruijnIndex.
        , urVarMap :: UResolverCache s (VarIndex s) (DeBruijnLevel,TCTerm)
        }

type UResolver s = StateT (UnifyResult s) (TC s)

data URRes v = URSeen v
             | URActive

type UResolverCache s k v = STRef s (Map k (URRes v))

newCache :: ST s (UResolverCache s k v)
newCache = newSTRef Map.empty

occursCheckFailure :: Pos -> String -> UResolver s a
occursCheckFailure p nm = lift $ tcFail p msg
  where msg = "Cyclic dependency detected during unification of " ++ nm

type UResolverCacheFn s k v = UnifyResult s -> UResolverCache s k v

uresolveCache :: Ord k
              => UResolverCacheFn s k v
              -> (k -> UResolver s v)
              -> Pos -> String -> k -> UResolver s v
uresolveCache gfn rfn p nm k = do
  cr <- gets gfn
  m0 <- lift $ liftST $ readSTRef cr
  case Map.lookup k m0 of
    Just (URSeen r) -> return r 
    Just URActive -> occursCheckFailure p nm
    Nothing -> do
      lift $ liftST $ writeSTRef cr $ Map.insert k URActive m0
      r <- rfn k
      lift $ liftST $ modifySTRef cr $ Map.insert k (URSeen r)
      return r

resolve :: UResolver s a -> Unifier s (a,TermContext s)
resolve m = do
  us <- get
  rmc <- lift $ liftST newCache
  vmc <- lift $ liftST newCache
  let ur0 = UR { urTermContext = usGlobalContext us
               , urLevel = 0               
               , urBoundMap = rmc
               , urVarMap = vmc
               }
  lift $ second urTermContext <$> runStateT m ur0

readVarState :: VarIndex s -> TC s (UVarState s)
readVarState v = liftST $ readSTRef (viRef v)

-- | Resolve a variable corresponding to an unused pattern variable,
-- returning index and type.
resolveBoundVar :: String -> VarIndex s -> UResolver s (DeBruijnLevel, TCTerm)
resolveBoundVar nm tpv = uresolveCache urBoundMap (resolveBoundVar' nm) (viPos tpv) nm tpv

resolveBoundVar' :: String -> VarIndex s -> UResolver s (DeBruijnLevel, TCTerm)
resolveBoundVar' nm tpv = do
  (l,tp0) <- resolveUTerm tpv
  ur <- get
  let l' = urLevel ur
  let tp = incTCVars 0 (l' - l) tp0
  put ur { urTermContext = consBoundVar nm tp (urTermContext ur)
         , urLevel = urLevel ur + 1
         }
  return (l',tp)

-- | Convert a TCTerm at a given level to be valid at the current level.
resolveCurrent :: (DeBruijnLevel, TCTerm) -> UResolver s TCTerm
resolveCurrent (l,t) = mkVar <$> gets urLevel
  where mkVar l' = incTCVars 0 (l' - l) t

-- | Resolve a unifier pat to a tcpat.
resolvePat :: UPat s -> UResolver s (TCPat TCTerm)
resolvePat (UPVar v) = fn <$> resolveBoundVar (rvrName v) (rvrType v)
  where fn = uncurry (TCPVar (rvrPos v) (rvrName v))
resolvePat (UPUnused v) = do 
  s <- lift $ readVarState v
  case s of
    UUnused nm tp -> uncurry (TCPVar (viPos v) nm) <$> resolveBoundVar nm tp
    _ -> return $ TCPUnused (viPos v)
resolvePat (UPatF p pf) = TCPatF p <$> traverse resolvePat pf

traverseResolveUTerm :: Traversable t
                     => t (VarIndex s)
                     -> UResolver s (DeBruijnLevel, t TCTerm)
traverseResolveUTerm tv = do
  ttf <- traverse resolveUTerm tv
  l <- gets urLevel
  let update (i,t) = incTCVars 0 (l-i) t
  return $ (l, update <$> ttf)

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm :: VarIndex s -> UResolver s (DeBruijnLevel,TCTerm)
resolveUTerm v = uresolveCache urVarMap resolveUTerm' (viPos v) (viName v) v

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm' :: VarIndex s -> UResolver s (DeBruijnLevel,TCTerm)
resolveUTerm' v = do
  let p = viPos v
  -- Returns a refernce to a pattern variable with the given name, index, and type.
  let mkPatVarRef nm tpv = fn <$> resolveBoundVar nm tpv
        where fn (i,tp) = (i+1, TCVar p nm 0 (incTCVars 0 1 tp))
  uvs <- lift $ liftST $ readSTRef (viRef v)
  case uvs of
    URigidVar r -> mkPatVarRef (rvrName r) (rvrType r)
    UVar v -> resolveUTerm v
    UUnused nm tpv -> mkPatVarRef nm tpv
    UFreeType nm -> fail "Free type variable unbound during unification"
    UHolTerm ft _ c -> resolve <$> traverseResolveUTerm c
      where resolve (l,c') = (l,tcApply (incTCVars 0 l ft) c')
    UTF utf -> second (TCF p) <$> traverseResolveUTerm utf
    UOuterVar nm lvl i tp -> pure (lvl,TCVar p nm i tp)

typecheckPats :: TermContext s
              -> [Un.Pat]
              -> TCTerm
              -> TC s ([TCPat TCTerm], TermContext s)
typecheckPats tc upl tp = runUnifier tc $ do
  utp <- mkUnifyTerm (emptyLocalCtx tc) =<< lift (reduce tp)
  (pl,utpl) <- unzip <$> traverse indexUnPat upl
  traverse_ (usetEqual utp) utpl
  resolve $ traverse resolvePat pl

-- | Typecheck pats against the given expected type.
typecheckPiPats :: TermContext s
                -> [Un.Pat]
                -> TCTerm
                -> TC s (([TCPat TCTerm],TCTerm), TermContext s)
typecheckPiPats tc pats tp = do
  tp' <- reduce tp
  runUnifier tc $ do
    (pl,utp') <- indexPiPats tc pats tp'
    resolve $ do
      pl' <-traverse resolvePat pl
      fmap (pl',) $ resolveCurrent =<< resolveUTerm utp'

{-
error $ "typecheckPiPats unimplemented\n" ++ show pats ++ "\n" ++ show (ppTCTerm tp)
typecheckPats _ctx unpats tp = do
  let s0 = undefined
  flip evalStateT s0 $ do
    upats <- mapM indexUnPat unpats
    -- Get result
    v <- newFlexVar Nothing "_"
    undefined upats v
  -- Parse untyped patterns to start unification
  -- Run unification.
  -- Extend term context with extra variables.
  -- Extract typececked pats
-}

typecheckEqn :: TermContext s -> TCTerm -> UnDefEqn -> TC s TCDefEqn
typecheckEqn ctx tp (DefEqnGen unpats unrhs) = do
  ((pats,rhsTp), ctx') <- typecheckPiPats ctx unpats tp
  DefEqnGen pats <$> typecheckTerm ctx' unrhs rhsTp

typecheckTerm :: TermContext s
                 -- Typecheck term
              -> Un.Term
                 -- Expected type
              -> TCTerm
                 -- Typechecked term.
              -> TC s TCTerm
typecheckTerm _ _ _ = unimpl "typecheckTerm"

{-
typecheckTerm tc ut tp = do
  (t,tp') <- inferTerm tc ut
  t <$ checkTypesEqual tc tp' tp
-}

ppTCPat :: TCPat TCTerm -> Doc
ppTCPat _ = unimpl "ppTCPat"

ppTCTermF :: (t -> Doc) -> TCTermF t -> Doc
ppTCTermF pp tf =
  case tf of
    UGlobal i -> ppIdent i
    UApp l r -> pp l <+> pp r
    UTupleValue l -> parens (commaSepList (pp <$> l))
    UTupleType l -> char '#' <> parens (commaSepList (pp <$> l))
    URecordValue m -> braces (semiTermList $ ppFld <$> Map.toList m)
      where ppFld (fld,v) = text fld <+> equals <+> pp v
    URecordSelector t f -> pp t <> char '.' <> text f
    URecordType m -> char '#' <> braces (semiTermList $ ppFld <$> Map.toList m)
      where ppFld (fld,v) = text fld <+> equals <+> pp v
    UCtorApp c l -> hsep (ppIdent c : fmap pp l)
    UDataType dt l -> hsep (ppIdent dt : fmap pp l)
    USort s -> text (show s)
    UIntLit i -> text (show i)
    UArray _ vl -> brackets (commaSepList (pp <$> V.toList vl))

ppTCTerm :: TCTerm -> Doc
ppTCTerm (TCF _ tf) = ppTCTermF ppTCTerm tf
ppTCTerm (TCLambda p l r) = 
  char '\\' <> parens (ppTCPat p <+> colon <+> ppTCTerm l) 
             <+> text "->" <+> ppTCTerm r
ppTCTerm (TCPi p l r) =
  parens (ppTCPat p <+> colon <+> ppTCTerm l) 
    <+> text "->" <+> ppTCTerm r
ppTCTerm (TCLet _ bindings t) = unimpl "ppTCTerm Let"
ppTCTerm (TCVar _ nm i _) = text (show nm)
ppTCTerm (TCLocalDef _ nm _ _) = text (show nm)


reduce :: TCTerm -> TC s TCTerm
reduce t@(TCF _ tf) =
  case tf of
    UGlobal _ -> unimpl "reduce UGlobal"
    UApp l r -> unimpl "reduce UApp"
    URecordSelector{} -> unimpl "reduce URecordSelector"
    _ -> pure t
reduce t@TCLambda{} = pure t
reduce t@TCPi{} = pure t
reduce t@TCLet{} = unimpl "reduce TCLet"
reduce t@TCVar{} = pure t
reduce t@TCLocalDef{} = pure t

{-
reduce (TCLocalDef _ _ i _) 
    | DefEqnGen [] rhs:l <- tcliEqns tcli
    = let rhs' = incTCVars 0 (i + tcliTotal tcli - tcliLevel tcli - 1) rhs
       in assert (null l) $ reduce rhs'
-}



-- | Check that term is equivalent to Sort i for some i.
checkIsSort :: TermContext s -> TCTerm -> TC s Sort
checkIsSort _ = checkIsSort' <=< reduce

-- | checkIsSort applied to reduced terms.
checkIsSort' :: TCTerm -> TC s Sort
checkIsSort' t@(TCF _ tf) =
  case tf of
    UGlobal _ -> unimpl "checkIsSet UGlobal"
    UApp lhs rhs -> unimpl "checkIsSet UApp"
    USort s -> return s
    _ -> tctFail t $ ppTCTerm t <+> text "is not a sort."
checkIsSort' t =
  tctFail t $ ppTCTerm t <+> text "is not a sort."

-- | Checks that term has type @Sort i@ for some @i@.
checkIsType :: TermContext s -> TCTerm -> TC s ()
checkIsType tc = checkIsType' tc <=< reduce
 
-- | Check is type applied to reduced terms.
checkIsType' :: TermContext s -> TCTerm -> TC s ()
checkIsType' tc t@(TCF p tf) =
  case tf of
    UGlobal i ->
      case Map.lookup i (tcIdentBindings tc) of
        Just (DefIdent _ rtp _) -> do
          tp <- eval p rtp
          void $ checkIsSort tc tp
        _ -> fail "Could not find global symbol." 
    UApp{} -> unimpl "checkIsType App"
    UTupleType{} -> pure ()
    URecordSelector{} -> unimpl "checkIsType RecSel"
    URecordType{} -> pure ()
    UDataType{} -> pure ()
    USort{} -> pure ()
    _ -> tctFail t $ ppTCTerm t <+> text "is not a type."
checkIsType' _ TCPi{} = pure ()
checkIsType' tc (TCVar _ _ _ tp) = void $ checkIsSort tc tp
checkIsType' tc t = tctFail t $ ppTCTerm t <+> text "is not a type."

-- | Typecheck a term as a type, returning a term equivalent to it, and
-- with the same type as the term.
tcType :: TermContext s -> Un.Term -> TC s TCTerm
tcType tc t = tcType' tc t []


tcLookupIdent :: TermContext s -> PosPair Un.Ident -> TC s ([TCTerm] -> TCTerm, TCTerm)
tcLookupIdent tc (PosPair p i) =
  case Map.lookup i (tcBindings tc) of
    Nothing -> tcFail p $ "Unknown identifier " ++ show i ++ "."
    Just (DefIdent gi rtp _) -> (mkApp (TCF p (UGlobal gi)),) <$> eval p rtp
    Just (BoundVar nm lvl tp) -> pure (mkApp (TCVar p nm (d - 1) tp'), tp)
      where d = tcLevel tc - lvl
            tp' = incTCVars 0 d tp
    Just (LocalDef nm lvl tp _) -> pure (mkApp (TCLocalDef p nm (d - 1) tp'), tp')
      where d = tcLevel tc - lvl
            tp' = incTCVars 0 d tp
    Just (CtorIdent c rtp) -> (TCF p . UCtorApp c,) <$> eval p rtp
    Just (DataTypeIdent dt rtp) -> (TCF p . UDataType dt,) <$> eval p rtp
    Just _ -> fail "Unexpected local type"
  where mkApp v = foldl (\a f -> TCF (pos f) (UApp f a)) v

tcBinding :: TermContext s -> PosPair Un.Ident -> [Un.Term] -> TC s TCTerm
tcBinding tc i uargs = do
  (v,tp) <- tcLookupIdent tc i
  (args,tp') <- inferPiArgs tc uargs tp
  tp' <$ checkIsType' tc tp'

tcLambdaType  :: TermContext s
              -> [(Un.ParamType, [Un.Pat], Un.Term)] -- PAtterns.
              -> Un.Term -- Right hand side of lambda expression
              -> [Un.Term] -- Terms to match.
              -> TC s TCTerm
tcLambdaType tc [] uf uargs = tcType' tc uf uargs
tcLambdaType tc ((_,patl,utp):l) uf0 uargs0 = do
  tp <- tcType tc utp
  (pl0,tc') <- typecheckPats tc patl tp
  let matchPatList (p:pl) _ [] = tcFail (pos p) "Lambda expression where type expected"
      matchPatList (p:pl) uf (ut:utl) = do
        tl <- matchPat tc p ut
        unimpl "tcLambdaType"
      matchPatList [] uf args = tcLambdaType tc l uf args
  matchPatList pl0 uf0 uargs0

tcType' :: TermContext s -> Un.Term -> [Un.Term] -> TC s TCTerm
tcType' tc uut uargs =
  case uut of
    Un.Var i -> tcBinding tc i uargs
    Un.Unused{} -> fail "Pattern syntax when type expected"
    Un.Con i -> tcBinding tc i uargs
    Un.Sort p s -> return $ TCF p (USort s)
    Un.Lambda p pl r -> tcLambdaType tc pl r uargs
    Un.App uf _ uv -> tcType' tc uf (uv:uargs)
    _ -> unimpl "tcType'"

-- | Check types in two terms are equal.
checkTypesEqual :: TermContext s -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual = unimpl "checkTypesEqual"

unimpl :: String -> a
unimpl nm = error (nm ++ " unimplemented")

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.
matchPat :: TermContext s -> TCPat TCTerm -> Un.Term -> TC s [TCTerm]
matchPat _tc t p = unimpl "matchPat" t p

-- | Attempt to reduce a term to a  pi expression, returning the pattern, type
-- of the pattern and the right-hand side.
-- Reports error if htis fails.
reduceToPiExpr :: TermContext s -> TCTerm -> TC s (TCPat TCTerm, TCTerm, TCTerm)
reduceToPiExpr _ tp = do
  rtp <- reduce tp
  case rtp of
    TCPi p l r -> return (p,l,r)
    _ -> tctFail rtp $ text "Unexpected argument to term with type:" 
                           <+> doubleQuotes (ppTCTerm rtp)

-- | Given a list of arguments and a pi-type, returns the pi type instantiated
-- with those arguments, and the values matched against patterns in the pi type.
inferPiArgs :: TermContext s -> [Un.Term] -> TCTerm -> TC s ([TCTerm],TCTerm)
inferPiArgs tc = go []
   where go pr [] tp = return (reverse pr,tp)
         go pr (ut:ur) tp = do
           (p,_,r) <- reduceToPiExpr tc tp
           args <- matchPat tc p ut
           go (args ++ pr) ur (tcApply r args)

{-
-- | Returns a typechecked term and its type in the given context.
inferTerm :: TermContext s -> Un.Term -> TC s (TCTerm,TCTerm)
inferTerm tc (Un.asApp -> (Un.Con (PosPair p i), uargs)) = do
  case Map.lookup i (tcBindings tc) of
    Just (CtorIdent c rtp) -> fmap (first fn) $ inferPiArgs tc uargs =<< eval p rtp
      where fn args = TCF p (UCtorApp c args)
    Just (DataTypeIdent dt rtp) -> fmap (first fn) $ inferPiArgs tc uargs =<< eval p rtp
      where fn args = TCF p (UDataType dt args)
    Just _ -> fail "Found def identifier bound to constructor ident"
    Nothing -> tcFail p $ "Not in scope " ++ show i ++ "."

inferTerm tc uut =
  case uut of
    Un.Var (PosPair p i) -> 
      case Map.lookup i (tcBindings tc) of
        Nothing -> tcFail p $ "Unknown identifier " ++ show i ++ "."
        Just (DefIdent gi rtp _) -> (TCF p (UGlobal gi),) <$> eval p rtp
        Just (BoundVar nm lvl tp) -> pure (v,tp')
          where d = tcLevel tc - lvl
                tp' = incTCVars 0 d tp
                v = TCVar p nm (d - 1) tp'
        Just (LocalDef nm lvl tp _) -> pure (v,tp')
          where d = tcLevel tc - lvl
                tp' = incTCVars 0 d tp
                v = TCLocalDef p nm (d - 1) tp'
        Just _ -> fail "Unexpected local type"
    Un.Unused{} -> fail "Pattern syntax when term expected"
    Un.Con{} -> fail "Unexpected constructor"
    Un.Sort p s -> return (TCF p (USort s), TCF p (USort (sortOf s)))
    Un.Lambda _ args rhs -> procArgs tc args
      where procArgs :: TermContext s
                     -> [(Un.ParamType, [Un.Pat], Un.Term)]
                     -> TC s (TCTerm,TCTerm)
            procArgs lctx [] = inferTerm lctx rhs 
            procArgs lctx ((_,patl,utp):l) = do
              tp <- typecheckType lctx utp
              (pl,lctx') <- typecheckPats lctx patl tp
              let foldPats fn v = foldr (flip fn tp) v pl
              (foldPats TCLambda *** foldPats TCPi) <$> procArgs lctx' l 
    Un.App uf _ uv -> do
      ((ft, ftp), (vt,vtp)) <- liftA2 (,) (inferTerm tc uf) (inferTerm tc uv)
      (p,ltp,r) <- reduceToPiExpr tc ftp
      checkTypesEqual tc ltp vtp

-} 

{-

    Un.Pi _ pats utp _ rhs -> do
      tp <- typecheckType tc utp
      (pl, tc') <- typecheckPats tc pats tp
      rest <- typecheckType tc' rhs
      return $ foldr (\pat r -> TCPi pat tp r) rest pl

    Un.TupleValue p tl -> (TCF p . UTupleValue) <$> traverse (inferTerm tc) tl
    Un.TupleType p tl  -> (TCF p . UTupleType)  <$> traverse (typecheckType tc) tl

    Un.RecordValue p fl -> fn <$> traverse (inferTerm tc) uterms
      where  (fields,uterms) = unzip fl
             fn terms = TCF p $ URecordValue (Map.fromList (fmap val fields `zip` terms))
    Un.RecordSelector _ux _i -> unimpl "inferTerm record selector"
      -- (flip URecordSelector (val i)) <$> inferTerm tc ux
    Un.RecordType p fl -> fn <$> traverse (typecheckType tc) uterms
      where (fields,uterms) = unzip fl
            fn terms = TCF p $ URecordType (Map.fromList (fmap val fields `zip` terms))
    Un.TypeConstraint ut _ utp -> do
      typecheckTerm tc ut =<< inferTerm tc utp
    Un.Paren _ t -> inferTerm tc t
    Un.LetTerm _ _udl _urhs -> unimpl "inferTerm LetTerm"
-}

{-
      (tc',dl) <- consLocalDecls tc udl
      rhs <- inferTerm tc' urhs
      return $ ULet dl rhs
-}
{-
    Un.IntLit p i -> pure $ TCF p $ UIntLit i
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p
-}

{-
-- | Typecheck that this term has a sort type.
typecheckAnyType :: TermContext s -> Un.Term -> TC s (TCTerm,Sort)
typecheckAnyType ctx ut = do 
  (t,tp) <- typecheckAnyTerm ctx ut
  hnf <- headNormalForm tp
  let errMsg = fail $ "Could not get sort of:\n" ++ show (t,hnf)
  case hnf of
    UUndefinedVar i -> do
      vb <- gets usVarBindings
      case Map.lookup i vb of
        Nothing -> fail $ "Cannot get sort of unbound variable\n" ++ show hnf
        Just (TypeBinding u) -> fail $ "Cannot get sort of type bound variable\n" ++ show hnf
        Just (ValueBinding u _) -> fail $ "Unexpected value bound variable\n" ++ show hnf
    USort s -> return (t,s)
    _ -> errMsg

-- | Typecheck that this term has a type.
typecheckAnyTerm :: TermContext s -> Un.Term -> TC s (UnifyTerm,UnifyTerm)
typecheckAnyTerm tc (Un.asApp -> (Un.Con i, uargs)) = do
  case Map.lookup (val i) (tcGlobalBindings tc) of
    Just (CtorIdent c r) -> do
      tp <- lookupTermRef r
      (args,rhsTp) <- chkPiUnTermList tc uargs =<< headNormalForm tp
      return (UCtorApp c args, rhsTp)
    Just (DataTypeIdent dt r) -> do
      tp <- lookupTermRef r
      (args,rhsTp) <- chkPiUnTermList tc uargs =<< headNormalForm tp
      return (UDataType dt args, rhsTp)
    Just DefIdent{} -> internalError "Found def identifier bound to constructor ident"
    Nothing -> fail $ ppPos (pos i) ++ " Not in scope: \'" ++ show (val i) ++ "\'"

typecheckAnyTerm tc utp =
  case utp of
    Un.Var ui -> do
      case Map.lookup (val ui) (tcVarBindings tc) of
        Just p -> return p
        Nothing -> do
          case Map.lookup (val ui) (tcGlobalBindings tc) of
            Just (DefIdent i r _) -> do
              tp <- lookupTermRef r
              return (UGlobal i,tp)
            _ -> failPos (pos ui) $ show (val ui) ++ " unbound in current context."
    Un.Sort _ s -> return (USort s, USort (sortOf s))

    Un.App uf _ ut -> do
      (f,ftp) <- typecheckAnyTerm tc uf
      UPi lhs lhsType rhs <- headNormalForm ftp
      t <- typecheckTerm tc ut lhsType
      let sub = matchPat t lhs
      rhs' <- applyUnifyPatSub sub rhs
      return (UApp f t, rhs')

    Un.Pi _ pats utp _ rhs -> do
      (tp, tpSort) <- typecheckAnyType tc utp
      (tc', pl) <- consPatVars tc pats tp
      (rest, restSort) <- typecheckAnyType tc' rhs
      return ( foldr (\p -> UPi p tp) rest pl
             , USort (maxSort tpSort restSort)
             )

    Un.TupleType _ tl  -> do
      pairs <- mapM (typecheckAnyType tc) tl
      let (terms,types) = unzip pairs
      let resSort = foldl' maxSort (mkSort 0) types
      return ( UTupleType terms
             , USort resSort
             )

    Un.RecordType _ fl -> do
      let (fields,uterms) = unzip fl
      pairs <- mapM (typecheckAnyType tc) uterms
      let (terms,types) = unzip pairs
      let resSort = foldl' maxSort (mkSort 0) types
      return ( URecordType (Map.fromList (fmap val fields `zip` terms))
             , USort resSort
             )

    Un.Paren _ t -> typecheckAnyTerm tc t

    _ -> error $ "typecheckAnyTerm " ++ show utp

-- | Convert an untyped expression into a term for unification.
convertTerm :: TermContext s -> Un.Term -> TC s UnifyTerm
convertTerm ctx (Un.asApp -> (Un.Con i, uargs)) = do
  bm <- gets (ctxGlobalBindings . usGlobalContext)
  case Map.lookup (val i) bm of
    Just (CtorIdent c r) -> do
      tp <- lookupTermRef r
      hnf <- headNormalForm tp
      (args,_) <- chkPiUnTermList ctx uargs hnf
      return $ UCtorApp c args
    Just (DataTypeIdent dt _) -> do
      args <- mapM (convertTerm ctx) uargs  
      return $ UDataType dt args
    Just DefIdent{} -> internalError "Found def identifier bound to constructor ident"
    Nothing -> fail $ ppPos (pos i) ++ " Not in scope: \'" ++ show (val i) ++ "\'"
convertTerm tc uut =
  case uut of
    Un.Var i -> tcFindLocalBinding i tc
    Un.Unused{} -> fail "Pattern syntax when term expected"
    Un.Con{} -> fail "Unexpected constructor"
    Un.Sort _ s -> return (USort s)
    Un.Lambda _ args rhs -> procArgs tc args
      where procArgs :: TermContext s
                     -> [(Un.ParamType, [Un.Pat], Un.Term)]
                     -> TC s UnifyTerm
            procArgs lctx [] = convertTerm lctx rhs 
            procArgs lctx ((_,patl,utp):l) = do
              tp <- convertTerm lctx utp
              (lctx',pl) <- consPatVars lctx patl tp
              rest <- procArgs lctx' l
              return $ foldr (\p -> ULambda p tp) rest pl
    Un.App f _ t -> liftM2 UApp (convertTerm tc f) (convertTerm tc t)
    Un.Pi _ pats utp _ rhs -> do
      tp <- convertTerm tc utp
      (tc', pl) <- consPatVars tc pats tp
      rest <- convertTerm tc' rhs
      return $ foldr (\p -> UPi p tp) rest pl

    Un.TupleValue _ tl -> UTupleValue <$> mapM (convertTerm tc) tl
    Un.TupleType _ tl  -> UTupleType <$> mapM (convertTerm tc) tl

    Un.RecordValue _ fl -> do
      let (fields,uterms) = unzip fl
      terms <- mapM (convertTerm tc) uterms
      return $ URecordValue (Map.fromList (fmap val fields `zip` terms))
    Un.RecordSelector ux i -> (flip URecordSelector (val i)) <$> convertTerm tc ux
    Un.RecordType _ fl -> do
      let (fields,uterms) = unzip fl
      terms <- mapM (convertTerm tc) uterms
      return $ URecordType (Map.fromList (fmap val fields `zip` terms))

    Un.TypeConstraint t _ _ -> convertTerm tc t
    Un.Paren _ t -> convertTerm tc t
    Un.LetTerm _ udl urhs -> do
      (tc',dl) <- consLocalDecls tc udl
      rhs <- convertTerm tc' urhs
      return $ ULet dl rhs
    Un.IntLit _ i -> return $ UIntLit i
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p

-- | A substitution that is applied to rigid variables in a pattern.
type UnifyPatSubst = Map RigidVarRef UnifyTerm

-- | @matchPat vpat tppat@ matches the pattern @vpat@ against the variables
-- in @tppat@.  It returns the a substituion
-- from the vars bound in tppat to terms in vpat.
-- @tppat@ is assumed to have type @pattype".
matchPat :: UnifyTerm -> UPat RigidVarRef VarIndex -> UnifyPatSubst
matchPat = go Map.empty 
  where goList :: UnifyPatSubst -> [(UnifyTerm, UPat)] -> UnifyPatSubst
        goList sub [] = sub
        goList sub ((s,p):l) = goList (go sub s p) l
        go :: UnifyPatSubst -> UnifyTerm -> UPat -> UnifyPatSubst
        go sub s (UPVar r) = Map.insert r s sub
        go sub _ UPUnused{} = sub
        go sub s p@(UPatF _ pf) =
          case (s,pf) of
            (UTupleValue sl, UPTuple pl)
              | length sl == length pl -> goList sub (zip sl pl)
            (URecordValue sm, UPRecord pm)
                | sk == pk -> goList sub (zip se pe)
              where (sk, se)  = sepKeys sm
                    (pk, pe)  = sepKeys pm
            (UCtorApp sc sl, UPCtor pc pl)
                | sc == pc -> goList sub (zip sl pl)
            _ -> internalError $ "matchPat failed to match " ++ show (s,p)  
        go _ s p = internalError $ "matchPat failed to match " ++ show (s,p)  

-- | @checkCtorType c cpl tp@ checks that the pattern @c(cpl)@ has type @tp@.
checkCtorType :: Ident -> [UPat] -> UnifyTerm -> TC s ()
checkCtorType c cpl ctorType = do
  m <- gets usCtorTypes
  case Map.lookup c m of
    Nothing -> internalError $ "Could not find ctor type for " ++ show c ++ "."
    Just  r -> do
      tp <- lookupTermRef r
      rhsTp <- instPiType cpl tp
      unifyTypes rhsTp ctorType

hasType :: UPat
        -> UnifyTerm
        -> TC s ()
hasType (UPVar v) tp = setRigidVarType v tp
hasType (UPUnused _) _ = return ()
hasType (UPatF _ pf) tp =
  case pf of
    UPTuple pl ->
      case tp of
        UTupleType tpl | length pl == length tpl ->
          zipWithM_ hasType pl tpl
        _ -> internalError $ "Could not match tuple pattern against type " ++ show tp
    UPRecord pm ->
      case tp of
        URecordType tpm | Map.keys pm == Map.keys tpm ->
          zipWithM_ hasType (Map.elems pm) (Map.elems tpm)
        _ -> internalError "Could not match record pattern"
    UPCtor c cpl -> checkCtorType c cpl tp

applyUnifyPatSub :: UnifyPatSubst -> UnifyTerm -> TC s UnifyTerm
applyUnifyPatSub sub = go 
  where boundv = Map.keys sub
        isUnbound v = Map.notMember v sub
        go :: UnifyTerm -> TC s UnifyTerm
        -- 
        go t@(URigidVar r) = return $ fromMaybe t (Map.lookup r sub)
        -- Unification variables had to be bound in an outer context, and hence cannot
        -- refer to variables in the substitution.
        go t@(UUndefinedVar v) = do
          mapM_ (\r -> addEdge (UPRigid r) (UIVar v)) boundv
          return t
        go t@UGlobal{} = return t
        go (ULambda pat tp rhs) 
          | all isUnbound (upatBoundVars pat) =
            liftM2 (ULambda pat) (go tp) (go rhs)
        go (UApp x y) = liftM2 UApp (go x) (go y)
        go (UPi pat tp rhs)
          | all isUnbound (upatBoundVars pat) =
            liftM2 (UPi pat) (go tp) (go rhs)
        go (UTupleValue l) = UTupleValue <$> mapM go l
        go (UTupleType l)  = UTupleType <$> mapM go l
        go (URecordValue m) = URecordValue <$> mapM go m
        go (URecordSelector t f) = (flip URecordSelector f) <$> go t
        go (URecordType m) = URecordType <$> mapM go m
        go (UCtorApp i l) = UCtorApp i <$> mapM go l
        go (UDataType i l) = UDataType i <$> mapM go l
        go t@USort{} = return t
        go ULet{} = internalError "applyUnifyPatSub does not support ULet"
        go t@UIntLit{} = return t
        go (UArray tp v) = liftM2 UArray (go tp) (mapM go v)

data UnifyResult = UResult {}
       UResult { -- Maps each rigid variable to the number of variables
                 -- in the patterns bound before it, and the type.
                 urRigidIndexMap :: Map RigidVarRef (Int,UnifyTerm)
                 -- | Maps unification vars to the term
               , urVarBindings :: Map VarIndex UnifyTerm
               , urModule :: Module
               , urLevel :: !DeBruijnLevel
                  -- | Maps rigid var refs in the current context to the level
                  -- and type when they were bound.
               , urRigidTypeMap :: Map RigidVarRef (DeBruijnLevel,Term)
               }

-- | Convert a unify pat into a fully-typechecked pat.
completePat :: DeBruijnLevel -> UnifyResult -> UPat -> Pat Term
completePat lvl0 r = go
  where go (UPVar v) = assert (i >= lvl0) $ PVar (rvrName v) (i-lvl0) tp
          where Just (i,tp) = Map.lookup v (urRigidTypeMap r)
        go UPUnused{} = PUnused
        go (UPatF _ pf) =
          case pf of
            UPTuple l -> PTuple (go <$> l)
            UPRecord m -> PRecord (go <$> m)
            UPCtor uc l -> PCtor c (go <$> l) 
              where Just c = findCtor (urModule r) uc

-- | Bind list of rigid variables in result.
bindPatImpl :: UnifyResult -> [RigidVarRef] -> UnifyResult
bindPatImpl r [] = r
bindPatImpl r0 bvl = rf
  where err v = internalError $ "bindPatImpl: Cannot find binding for " ++ show v
        -- Get rigid vars sorted by index
        uvl = Map.elems
            $ Map.fromList [ (i,(v,tp))
                           | v <- bvl
                           , let (i,tp) = fromMaybe (err v)
                                        $ Map.lookup v (urRigidIndexMap r0)
                           ]
        addVar :: UnifyResult -> (RigidVarRef,UnifyTerm) -> UnifyResult
        addVar r (v,utp) = r'
         where tp = completeTerm r utp
               lvl = urLevel r
               r' = r { urLevel = lvl + 1
                      , urRigidTypeMap = Map.insert v (lvl,tp) (urRigidTypeMap r)
                      }
        rf = foldl' addVar r0 uvl

bindPat :: UnifyResult -> UPat -> (UnifyResult, Pat Term)
bindPat r0 up = (r,completePat (urLevel r0) r up)
  where r = bindPatImpl r0 (upatBoundVars up)


bindPats :: UnifyResult -> [UPat] -> (UnifyResult, [Pat Term])
bindPats r0 upl = (r, completePat (urLevel r0) r <$> upl)
  where r = bindPatImpl r0 (concatMap upatBoundVars upl)
-}

topEval :: TCRef s v -> TC s v
topEval r = eval (internalError $ "Cyclic error in top level" ++ show r) r


evalDataType :: TCRefDataType s -> TC s TCDataType
evalDataType = mapM topEval

evalDef :: TCRefDef s -> TC s TCDef
evalDef (DefGen nm tpr elr) = liftA2 (DefGen nm) (topEval tpr) (topEval elr)

data CompletionContext = CC { ccModule :: Module }

{-
bindPat :: CompletionContext -> TCPat TCTerm -> (CompletionContext,Pat Term)
bindPat _ _ = undefined
-}

completeDataType :: CompletionContext
                 -> TCDataType
                 -> TypedDataType
completeDataType cc = fmap (completeTerm cc)

completeDef :: CompletionContext
            -> TCDef
            -> TypedDef
completeDef cc (DefGen nm tp el) = def
  where def = Def { defIdent = nm 
                  , defType = completeTerm cc tp
                  , defEqs = completeDefEqn cc <$> el 
                  }

completeDefEqn :: CompletionContext -> TCDefEqn -> TypedDefEqn
completeDefEqn cc (DefEqnGen pl rhs) = eqn
  where eqn = DefEqn (completePat cc <$> pl) (completeTerm cc rhs)

completePat :: CompletionContext -> TCPat TCTerm -> Pat Term
completePat _cc = unimpl "completePat" -- fmap (completeTerm cc)

-- | Returns the type of a unification term in the current context.
completeTerm :: CompletionContext -> TCTerm -> Term
completeTerm = unimpl "completeTerm undefined"
{-
completeTerm cc (TCF tf) =

  case tf of
    UGlobal i -> Term (GlobalDef d)
      where Just d = findDef m i
    ULambda p lhs rhs -> 
    ULambda p lhs rhs -> Term (Lambda p' (go cc lhs) (go cc' rhs))
      where (cc',p') = bindPat cc p
 where m = ccModule cc
-}

{-
completeTerm = go
  where go r ut =
          case ut of
            URigidVar v -> incVars 0 (urLevel r - l) t
              where err = "Could not complete term: unknown type " ++ show (v,urRigidTypeMap r)
                    (l,t) = fromMaybe (internalError err) $
                              Map.lookup v (urRigidTypeMap r)
            UUndefinedVar i -> go r t
              where Just t = Map.lookup i (urVarBindings r)
            UApp x y  -> Term $ App (go r x) (go r y)
            UPi p lhs rhs -> Term (Pi p' (go r lhs) (go r' rhs))
              where (r',p') = bindPat r p
            UTupleValue l -> Term $ TupleValue (go r <$> l)
            UTupleType l  -> Term $ TupleType  (go r <$> l)
            URecordValue m      -> Term $ RecordValue (go r <$> m)
            URecordSelector x f -> Term $ RecordSelector (go r x) f
            URecordType m       -> Term $ RecordType (go r <$> m)
            UCtorApp i l   -> Term $ CtorValue c (go r <$> l)
              where Just c = findCtor (urModule r) i
            UDataType i l -> Term $ CtorType dt (go r <$> l)
              where Just dt = findDataType (urModule r) i
            USort s   -> Term $ Sort s
            ULet dl t -> Term $ Let (completeLocalDef <$> dl) (go r' t)
              where r' = bindPatImpl r (localVarNamesGen dl)
                    completeLocalDef (LocalFnDefGen v tp eqs) =
                        LocalFnDef (rvrName v) (go r tp) (completeEqn r' <$> eqs)
            UIntLit i -> Term $ IntLit i
            UArray tp v -> Term $ ArrayValue (go r tp) (go r <$> v)

completeEqn :: UnifyResult -> UnifyDefEqn -> TypedDefEqn
completeEqn r (DefEqnGen upl urhs) = DefEqn pl (completeTerm r' urhs)
  where (r',pl) = bindPats r upl


-- | Convert a untyped pat into a unify pat.
indexUnPat :: Un.Pat -> Unifier s UPat
indexUnPat pat = 
  case pat of
    Un.PVar psym -> UPVar <$> newRigidVar (Just (pos psym)) (val psym)
    Un.PUnused s -> UPUnused <$> newUnifyVarIndex s
    Un.PTuple p pl   -> (UPatF (Just p) . UPTuple) <$> mapM indexUnPat pl
    Un.PRecord p fpl -> (UPatF (Just p) . UPRecord . Map.fromList . zip (val <$> fl))
                                   <$> mapM indexUnPat pl
      where (fl,pl) = unzip fpl

    Un.PCtor i l -> do
      ctx <- gets usGlobalContext
      case Map.lookup (val i) (ctxGlobalBindings ctx) of
        Just (CtorIdent c _) ->
          (UPatF (Just (pos i)) . UPCtor c) <$> mapM indexUnPat l 
        Just _ -> fail $ show (val i) ++ " does not refer to a constructor."
        Nothing -> fail $ "Unknown symbol " ++ show (val i)
-}

addImportNameStrings :: Un.ImportName -> Set String -> Set String
addImportNameStrings im s =
  case im of
    Un.SingleImport pnm -> Set.insert (val pnm) s
    Un.AllImport pnm -> Set.insert (val pnm) s
    Un.SelectiveImport pnm cl -> foldr Set.insert s (val <$> (pnm:cl)) 

-- | Returns set of names identified in a given list of names to import.
importNameStrings :: [Un.ImportName] -> Set String
importNameStrings = foldr addImportNameStrings Set.empty

includeNameInModule :: Maybe Un.ImportConstraint -> String -> Bool
includeNameInModule mic =
  case mic of
    Nothing -> \_ -> True
    Just (Un.SpecificImports iml) -> flip Set.member imset
      where imset = importNameStrings iml
    Just (Un.HidingImports iml) -> flip Set.notMember imset
      where imset = importNameStrings iml

{-
completeCtor :: UnifyResult -> TCCtor -> TypedCtor
completeCtor r (Ctor nm tp) = Ctor nm (completeTerm r tp)


completeDef :: TermContext s
            -> TC s 

assignDataType :: TermContext s -> UnDataType -> TC s TCDataType
assignDataType tc dt = do
  tp <- convertTerm tc (dtType dt)
  ctors <- mapM (convertCtor tc) (dtCtors dt)
  return DataType { dtName = mkIdent (tcModuleName tc) (val (dtName dt))
                  , dtType = tp
                  , dtCtors = ctors
                  }

convertCtor :: TermContext s -> UnCtor -> TC s TCCtor
convertCtor tc c = do
  (tp,_) <- typecheckAnyTerm tc (ctorType c)
  return Ctor { ctorName = mkIdent (tcModuleName tc) (val (ctorName c))
              , ctorType = tp
              }

mkModule :: Module
            -- | List of data types.
         -> [TCDataType]
            -- | List of definition types.
         -> [(String, UnifyTerm)]
         -> Map String [TCDefEqn]
         -> TC s Module
mkModule ctxm udtl defs eqnMap = do
  let mnm = moduleName ctxm
  s <- get
  let completeDef :: String -> TCTerm -> Def Term
      completeDef nm tp =
          Def { defIdent = mkIdent mnm nm
              , defType = completeTerm r tp
              , defEqs = completeEqn r <$> eqs
              } 
        where eqs = fromMaybe [] $ Map.lookup nm eqnMap
      m = flip (foldl' insDef) (uncurry completeDef <$> defs)
        $ flip (foldl' insDataType) (completeDataType r <$> udtl)
        $ ctxm
      r = UResult {}
      varSubvars :: UVar -> Set UVar
      varSubvars (UPRigid sym) = addUnifyTermVars Set.empty tp
        where err = "Could not find type for " ++ show sym
              tp = fromMaybe (internalError err) $ Map.lookup sym (usTypeMap s)
      varSubvars (UIVar i) = 
        case Map.lookup i (usVarBindings s) of
          Just t -> addUnifyTermVars Set.empty (varBindingTerm t)
          Nothing -> Set.empty
      vars = usVars s
      edges = [ (v, u)
                | u <- Set.toList vars
                , v <- Set.toList (varSubvars u)
              ]
      allOrdering =
           case topSort vars edges of
          Left zm -> error $ "Found cyclic dependencies: " ++ show zm
          Right o -> o
      ordering :: Vector RigidVarRef
      ordering = V.fromList [ i | UPRigid i <- allOrdering ]
      pIdxMap :: Map RigidVarRef DeBruijnIndex
      pIdxMap = orderedListMap (V.toList ordering)
      varUnifyTypes :: Vector UnifyTerm
      varUnifyTypes = fn <$> ordering
        where fn v = tp
                where Just tp = Map.lookup v (usTypeMap s)
      getRigidVarType i = (i,varUnifyTypes V.! i)
      r = UResult { urRigidIndexMap = getRigidVarType <$> pIdxMap
                  , urVarBindings = varBindingTerm <$> usVarBindings s
                  , urModule = m
                  , urLevel = 0
                  , urRigidTypeMap = Map.empty
                  }
  return m
-}

emptyTermContext :: ModuleName -> TermContext s
emptyTermContext nm =
  TermContext { tcModule = emptyModule nm
              , tcBindings = Map.empty
              , tcIdentBindings = Map.empty
              , tcIndexedBindings = []
              , tcLevel = 0
              }
  
-- | Creates a module from a list of untyped declarations.
unsafeMkModule :: [Module] -- ^ List of modules loaded already.
               -> Un.Module
               -> Either Doc Module
unsafeMkModule ml (Un.Module (PosPair _ nm) iml d) = do
  let moduleMap = projMap moduleName ml
{-
  -- Get data types for module.
  let mkDataType psym untp ucl = DataType { dtName = psym
                                          , dtType = untp
                                          , dtCtors = ctorDef <$> ucl
                                          }
        where ctorDef (Un.Ctor pnm ctorTp) = Ctor pnm ctorTp
      dataTypes = [ mkDataType psym untp ucl
                  | Un.DataDecl psym untp ucl <- d
                  ]
      dataTypeCount = length dataTypes
  let dtRefs = zipWith UTR (dtName <$> dataTypes) [0..]
  -- Get list of ctors.
  let ctors = concatMap dtCtors dataTypes
      ctorCount = dataTypeCount + length ctors
  let ctorIdent c = mkIdent nm (val (ctorName c))
  let ctorPair cnm r = (Un.localIdent cnm, CtorIdent (mkIdent nm cnm) r)
      ctorRefs = zipWith UTR (ctorName <$> ctors) [dataTypeCount..]

  -- Get function declarations from module.
  let typeDecls :: [([PosPair String], Un.Term)]
      typeDecls = [ (idl, tp) | Un.TypeDecl idl tp <- d ]
  -- Get equations from module.
  let defPair r = fmap fn
        where fn dnm = (Un.localIdent (val dnm), DefIdent (mkIdent nm (val dnm)) r [])
  let ctx = GlobalContext {
                gcModule = m
              , ctxGlobalBindings = Map.fromList $
                  concatMap snd imports
                    ++ zipWith dtPair (val <$> dtName <$> dataTypes) dtRefs
                    ++ zipWith ctorPair (val <$> ctorName <$> ctors) ctorRefs
                    ++ concat (zipWith defPair defRefs (fst <$> typeDecls))
              }
  let allRefs = dtRefs ++ ctorRefs ++ defRefs
      allUntypedTerms = fmap dtType dataTypes
                     ++ fmap ctorType ctors
                     ++ fmap snd typeDecls
  let us0 = US { usGlobalContext = ctx
               , usTypeMap = Map.empty
               , usVarBindings = Map.empty
               , usCtorTypes = Map.fromList (fmap ctorIdent ctors `zip` ctorRefs)
               , unifyEqs = []
               , usVars = Set.empty
               , usEdges = Set.empty
               , nextVarIndex = 0
               , nextRigidIndex = 0
               , usTermRefMap = Map.fromList $
                   zip allRefs (UntypedTerm emptyTermContext <$> allUntypedTerms)
               , usUntypedTerms = Set.fromList allRefs
               }
-}
  runTC $ do
    let tc0 = emptyTermContext nm
    let is0 = IS { isCtx = tc0
                 , isTypes = []
                 , isDefs = []
                 , isPending = []
                 }
    let eqnMap = multiMap [ (val psym, DefEqnGen (snd <$> lhs) rhs)
                          | Un.TermDef psym lhs rhs <- d
                          ]
    -- Parse imports and declarations.
    let actions = fmap (parseImport moduleMap) iml
               ++ fmap (parseDecl eqnMap) d
    is <- execStateT (sequenceA_ actions) is0
    let tc = isCtx is
    -- Execute pending assignments with final TermContext.
    sequence_ $ (($ tc) <$> isPending is)
    
    let mkFinal tps defs = m
          where cc = CC { ccModule = m
                        }
                m = flip (foldl' insDef) (completeDef cc <$> defs)
                  $ flip (foldl' insDataType) (completeDataType cc <$> tps)
                  $ tcModule tc
    liftA2 mkFinal
           (traverse evalDataType (isTypes is))
           (traverse evalDef (isDefs is))

{-
    let (defNames,untps) = unzip typeDecls
    defTypes <- mapM (fmap fst . typecheckAnyTerm tc) untps
    let defs = [ (val i,tp)
               | (idl,tp) <- defNames `zip` defTypes
               , i <- idl 
               ]
    let defTypeMap = Map.fromList defs
    let eqns = [ (val psym, DefEqnGen (snd <$> lhs) rhs)
               | Un.TermDef psym lhs rhs <- d
               ]
    eqnMap <- fmap multiMap $ 
      forM eqns $ \(sym,uneqn) -> do
        let Just tp = Map.lookup sym defTypeMap
        eqn <- convertEqn tc tp uneqn
        return (sym, eqn)
    let completeDef :: String -> TCTerm -> Def Term
        completeDef nm tp =
          Def { defIdent = mkIdent mnm nm
              , defType = completeTerm r tp
              , defEqs = completeEqn r <$> eqs
              } 
         where eqs = fromMaybe [] $ Map.lookup nm eqnMap
        r = UResult {}
-}

liftTerm :: TermContext s -> Term -> TC s TCTerm
liftTerm _ _ = unimpl "liftTerm"

liftDefEqn :: TermContext s -> TypedDefEqn -> TC s TCDefEqn
liftDefEqn _ _ = unimpl "liftDefEqn"

-- | Typechecker computation that needs input before running.
type PendingAction s a = a -> TC s ()

mkPendingAssign :: TCRef s v -> (a -> TC s v) -> PendingAction s a
mkPendingAssign r f a = assign r (f a)

data InitState s = IS { isCtx :: TermContext s
                      , isTypes :: [ TCRefDataType s ]
                      , isDefs :: [ TCRefDef s ]
                      , isPending :: [ PendingAction s (TermContext s) ]
                      }

type Initializer s a = StateT (InitState s) (TC s) a

initModuleName :: Initializer s ModuleName
initModuleName = gets (tcModuleName . isCtx)

insModule :: Module -> Module -> Module
insModule base m = flip (foldl' insDef) (moduleDefs m)
                 $ flip (foldl' insDataType) (moduleDataTypes m)
                 $ base

updateIsCtx :: (TermContext s -> TermContext s) -> Initializer s ()
updateIsCtx f = modify $ \s -> s { isCtx = f (isCtx s) }

addGlobal :: TCRefGlobalBinding s -> Initializer s ()
addGlobal g = updateIsCtx fn
  where fn tc = tc { tcIdentBindings = Map.insert (gbIdent g) g (tcIdentBindings tc) }

-- | Add untyped global with the given module names.
addUGlobal :: [Maybe ModuleName]
           -> String
           -> TCRefGlobalBinding s
           -> Initializer s ()
addUGlobal mnml nm gb = updateIsCtx fn
  where ins mnm = Map.insert (Un.mkIdent mnm nm) gb  
        fn tc = tc { tcBindings = foldr ins (tcBindings tc) mnml }

-- | Adds an untyped binding in a untyped scope without qualifiers needed.
addInscopeUGlobal :: String -> TCRefGlobalBinding s -> Initializer s ()
addInscopeUGlobal = addUGlobal [Nothing]

addType :: TCRefDataType s -> Initializer s ()
addType tp = modify $ \s -> s { isTypes = tp : isTypes s }

addDef :: TCRefDef s -> Initializer s ()
addDef d = modify $ \s -> s { isDefs = d : isDefs s }

addPending :: NodeName -> (TermContext s -> TC s r) -> Initializer s (TCRef s r)
addPending nm fn = do
  r <- lift $ newRef nm  
  r <$ modify (\s -> s { isPending = mkPendingAssign r fn : isPending s })

termRef :: String -> Term -> Initializer s (TCRef s TCTerm)
termRef nm t = addPending nm (flip liftTerm t)

eqRef :: NodeName -> [TypedDefEqn] -> Initializer s (TCRef s [TCDefEqn])
eqRef nm eqn = addPending nm (\tc -> mapM (liftDefEqn tc) eqn)

parseCtor :: Un.CtorDecl -> Initializer s (TCRefCtor s)
parseCtor (Un.Ctor pnm utp) = do
  mnm <- initModuleName
  tp <- addPending (val pnm) (\tc -> tcType tc utp)
  let ci = mkIdent mnm (val pnm)
  addUGlobal [Nothing] (val pnm) (CtorIdent ci tp)
  return Ctor { ctorName = ci, ctorType = tp }

parseDecl :: Map String [UnDefEqn] -> Un.Decl -> Initializer s ()
parseDecl eqnMap d = do
  mnm <- initModuleName
  case d of
    Un.TypeDecl idl utp -> do
      let id1:_ = idl
      tp <- addPending (val id1) (\tc -> tcType tc utp)
      for_ idl $ \(PosPair p nm) -> do
        let ueqs = fromMaybe [] $ Map.lookup nm eqnMap
        eqs <- addPending ("Equations for " ++ nm) $ \tc -> do
          etp <- eval p tp
          traverse (typecheckEqn tc etp) ueqs
        let di = mkIdent mnm nm
        addInscopeUGlobal nm (DefIdent di tp eqs)
        addDef (DefGen di tp eqs)
    Un.DataDecl psym utp ucl -> do
      tp <- addPending (val psym) (\tc -> tcType tc utp)
      let dti = mkIdent mnm (val psym)
      cl <- traverse parseCtor ucl
      addInscopeUGlobal (val psym) (DataTypeIdent dti tp)
      addType DataType { dtName = dti
                       , dtType = tp
                       , dtCtors = cl
                       }
    Un.TermDef{} -> return ()

parseImport :: Map ModuleName Module
            -> Un.Import
            -> Initializer s ()
parseImport moduleMap (Un.Import q (PosPair p nm) mAsName mcns) = do
  case Map.lookup nm moduleMap of
    Nothing -> lift $ tcFail p $ "Cannot find module " ++ show nm ++ "."
    Just m -> do
      -- Add module to context
      updateIsCtx $ \tc -> tc { tcModule = insModule (tcModule tc) m }
      -- Get list of module names to use for local identifiers.
      let mnml | q = [Just qnm]
               | otherwise = [Nothing, Just qnm]
            where qnm = maybe (moduleName m)
                              (\s -> Un.mkModuleName [s])
                              (val <$> mAsName)
      -- Adds untyped identifiers to name if this identifer should be added to module.
      let addIdent gb = do
            let inm = identName (gbIdent gb)
            gb' <- mapBinding (termRef inm) (eqRef inm) gb
            addGlobal gb'
            when (includeNameInModule mcns inm) $ do
              addUGlobal mnml inm gb'
      -- Add datatypes to module
      for_ (moduleDataTypes m) $ \dt ->
        addIdent $ DataTypeIdent (dtName dt) (dtType dt)
      -- Add constructors to module.
      for_ (concatMap dtCtors (moduleDataTypes m)) $ \c ->
        addIdent $ CtorIdent (ctorName c) (ctorType c)
      -- Add definitions to module.
      for_ (moduleDefs m) $ \def -> do
        addIdent $ DefIdent (defIdent def) (defType def) (defEqs def)