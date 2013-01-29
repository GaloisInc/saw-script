{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFoldable #-} 
{-# LANGUAGE DeriveTraversable #-} 
{-# LANGUAGE DoAndIfThenElse #-} 
{-# LANGUAGE EmptyDataDecls #-}
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
import Control.Monad.Identity (Identity(..))
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
import Verifier.SAW.Typechecker.Monad
import Verifier.SAW.Typechecker.Context
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


localVarNamesGen :: [LocalDefGen t e] -> [String]
localVarNamesGen = fmap go
  where go (LocalFnDefGen nm _ _) = nm


-- | Type synonyms in untyped world.
type UnPat = (Un.ParamType, [Un.Pat])
type UnCtor = Ctor (PosPair String) Un.Term
type UnDataType = DataType (PosPair String) Un.Term
type UnDefEqn = DefEqnGen Un.Pat Un.Term
type UnLocalDef = LocalDefGen Un.Term [UnDefEqn]

{-
getBinding :: DeBruijnIndex -> TermContext s -> Maybe (TCBinding (TCRef s))
getBinding i tc | 0 <= i && i < length bl = Just (bl !! i)
                | otherwise = Nothing
  where bl = tcIndexedBindings tc
-}

{-
localNames :: TermContext s -> [Doc]
localNames tc = fn <$> tcIndexedBindings tc
  where fn (BoundVar nm _) = text nm
        fn (LocalDef nm _) = text nm
        fn _ = error "Unexpected binding in local stack."
-}


-- | @extendModule m base@ returns base with the additional imports in @m@. 
extendModule :: Module -> Module -> Module
extendModule m base = flip (foldl' insDef) (moduleDefs m)
                    $ flip (foldl' insDataType) (moduleDataTypes m)
                    $ base


{-
-- | Add a local definition to context.
consLocalDef :: String
             -> TCTerm
             -> TCRef s [TCDefEqn]
             -> TermContext s
             -> TermContext s
consLocalDef nm tp _eqs uc = consLocalBinding nm (LocalDef nm tp) uc

lookupUntypedBinding :: Un.Ident
                     -> TermContext s
                     -> Maybe (DeBruijnIndex, TCBinding (TCRef s))
lookupUntypedBinding usym uc =
    case Map.lookup usym (ucBindings uc) of
      Nothing -> Nothing
      Just (l, r@DataTypeIdent{}) -> assert (l == 0) $ Just (lvl,r)
      Just (l, r@CtorIdent{}) -> assert (l == 0) $ Just (lvl,r)
      Just (l, r@DefIdent{}) -> assert (l == 0) $ Just (lvl,r)
      Just (l, (BoundVar nm tp)) -> assert (l < lvl) $ 
        Just $ (lvl - l, BoundVar nm (incTCVars 0 (lvl - l) tp))
      Just (l, (LocalDef nm tp)) -> assert (l < lvl) $ 
        Just $ (lvl - l, LocalDef nm (incTCVars 0 (lvl - l) tp))
  where lvl = ucLevel uc
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
                fn (PosPair _ nm,tp) = LocalFnDefGen nm tp eqs
                  where Just eqs = Map.lookup nm eqMap
        groupDecl :: GroupLocalDeclsState -> Un.Decl -> GroupLocalDeclsState
        groupDecl (tpMap,eqMap) (Un.TypeDecl idl tp) = (tpMap',eqMap)
          where tpMap' = foldr (\k -> Map.insert (val k) (k,tp)) tpMap idl
        groupDecl (tpMap,eqMap) (Un.TermDef pnm pats rhs) = (tpMap, eqMap')
          where eq = DefEqnGen (snd <$> pats) rhs
                eqMap' = Map.insertWith (++) (val pnm) [eq] eqMap
        groupDecl _ Un.DataDecl{} = error "Unexpected data declaration in let binding"

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
        go (UNatLit ix) (UNatLit iy) | ix == iy = pure (UNatLit ix)
        go (UArray tx vx) (UArray ty vy)
          | V.length vx == V.length vy = pure $ UArray (f tx ty) (V.zipWith f vx vy)

        go _ _ = Nothing

{-
-- | TCLocalInfo defines the total number 
data TCLocalInfo = TCLocalInfo { tcliTotal :: DeBruijnLevel
                               , tcliLevel :: DeBruijnLevel
                               , tcliEqns :: [TCDefEqn]
                               } deriving (Show)
-}


incTCPatVars :: DeBruijnLevel -> DeBruijnIndex -> TCPat TCTerm -> TCPat TCTerm
incTCPatVars i j p = fmapTCPat (\i' t -> incTCVars i' j t) i p

data UVarState s
    -- | Indicates this var is equivalent to another.
  = UVar (VarIndex s)
  | URigidVar (RigidVarRef s) -- ^ Rigid variable that cannot be instantiated.
    -- | A unused pattern variable with its type.
  | UUnused String (VarIndex s)
    -- | A free type variable with the name of the variable it is type for.
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

data UPat s
  = UPVar (RigidVarRef s)
  | UPUnused (VarIndex s)
  | UPatF Un.Pos (PatF (UPat s))
  deriving (Show)


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

type TCDataType = DataTypeGen TCDTType (Ctor Ident TCCtorType)
type TCDef = TCDefGen Identity
type TCLocalDef = LocalDefGen TCTerm [TCDefEqn]

-- | @tcApply t n args@ substitutes free variables [n..length args-1] with args.
-- The args are assumed to be in the same context as @t@.
tcApply :: Int -> TCTerm -> Vector TCTerm -> TCTerm
tcApply ii it v = go ii it 
  where l = V.length v
        go i (TCF tf) = TCF (go i <$> tf)
        go i (TCLambda p tp r) = TCLambda (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCPi p tp r) = TCPi (fmapTCPat go i p) (go i tp) r'
          where r' = go (i + tcPatVarCount p) r
        go i (TCLet lcls r) = TCLet (fmapTCLocalDefs go i lcls) r'
          where r' = go (i + length lcls) r
        go i (TCVar j tp) | j < i = TCVar j (go i tp)
                          | j - i >= l = TCVar (j - l) (go i tp)
                          | otherwise = incTCVars 0 i (v V.! (j - i))
        go i (TCLocalDef j tp)
          | j < i = TCVar j (go i tp)
          | j - i >= l = TCVar (j - l) (go i tp)
          | otherwise = error "Attempt to instantiate let bound definition."

tcPatApply :: Int -> TCPat TCTerm -> Vector TCTerm -> TCPat TCTerm
tcPatApply i p v = fmapTCPat (\i' t -> tcApply i' t v) i p

fmapTCApply :: Functor f => f TCTerm -> Vector TCTerm -> f TCTerm
fmapTCApply s a = (\t -> tcApply 0 t a) <$> s

tcDTTypeApply :: TCDTType -> Vector TCTerm -> TCDTType
tcDTTypeApply itp v = go 0 itp
  where go i (FPResult s) = FPResult s
        go i (FPPi p tp r) = FPPi (tcPatApply i p v) (tcApply i tp v) r'
          where r' = go (i + tcPatVarCount p) r

tcCtorTypeApply :: TCCtorType -> Vector TCTerm -> TCCtorType
tcCtorTypeApply itp v = go 0 itp
  where go i (FPResult tl) = FPResult ((\t -> tcApply i t v) <$> tl)
        go i (FPPi p tp r) = FPPi (tcPatApply i p v) (tcApply i tp v) r'
          where r' = go (i + tcPatVarCount p) r

tctFail :: Pos -> Doc -> TC s a
tctFail p d = tcFail p $ show d

{-
convertEqn :: TermContext s
           -> UnifyTerm
           -> UnDefEqn
           -> TC s UnifyDefEqn
convertEqn ctx tp (DefEqnGen unpats unrhs) = do
  pats <- mapM indexUnPat unpats
  rhsTp <- instPiType pats tp
  let ctx' = addLocalBindings ctx (concatMap upatBoundVars pats)
  rhs <- tcTerm ctx' unrhs rhsTp
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
          rhs <- tcTerm tc2 unrhs rhsTp
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
          a <- tcTerm ctx ua lhsType
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
                           , viName :: String
                           , viRef :: STRef s (UVarState s)
                           }

instance Eq (VarIndex s) where
  (==) = lift2 viIndex (==)

instance Ord (VarIndex s) where
  compare = lift2 viIndex compare

instance Show (VarIndex s) where
  show = unimpl "Show VarIndex"

data UnifierState s =
  US { usGlobalContext :: TermContext s
       -- Position where unification began.                     
     , usPos :: Pos
     , usVarCount :: Int
     , usRigidCount :: Int
     }

type Unifier s = StateT (UnifierState s) (TC s)

unFail :: Pos -> Doc -> Unifier s a
unFail p msg = lift (tcFail p (show msg))

mkVar :: String -> UVarState s -> Unifier s (VarIndex s)
mkVar nm vs = do
  vr <- lift $ liftST $ newSTRef vs
  s <- get
  let vidx = usVarCount s
      v = VarIndex { viIndex  = vidx
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

ppUTerm :: UVarState s -> TC s Doc
ppUTerm vs0 = evalStateT (go vs0) Set.empty
  where goVar :: VarIndex s -> StateT (Set (VarIndex s)) (TC s) Doc
        goVar v = do
          s <- get
          if Set.member v s then
            return $ text (viName v)
          else do
            put (Set.insert v s)
            go =<< lift (readVarState v) 
        go :: UVarState s -> StateT (Set (VarIndex s)) (TC s) Doc
        go (UVar v) = goVar v
        go (URigidVar r) = pure (text (rvrName r))
        go (UUnused nm _) = pure (text nm)
        go (UFreeType nm) = pure (text $ "typeOf(" ++ nm ++ ")")
        go (UHolTerm t _ bindings) = unimpl "ppUTerm"          
        go (UTF tf) = ppTCTermF goVar tf
        go (UOuterVar nm _ _ _) = pure (text nm)

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
      p <- gets usPos
      lift $ checkTypesEqual tc p txf tyf
      -- Unify corresponding entries in cx and cy.
      zipWithM usetEqual cx cy
      -- Set vx to point to vy.
      lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    _ -> do
      p <- gets usPos
      xd <- lift $ ppUTerm x
      yd <- lift $ ppUTerm y
      unFail p $ vcat [ text "Do not support unifying types:"
                      , text "Type 1"
                      , nest 2 xd
                      , text "Type 2"
                      , nest 2 yd
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
        tp <- mkVar ("type of " ++ nm) (UFreeType nm)
        let fn r = (UPVar r,tp)
        fn <$> newRigidVar p nm tp
    Un.PUnused (PosPair p nm) -> do
      tpv <- mkVar ("type of " ++ nm) (UFreeType nm)
      (\v -> (UPUnused v, tpv)) <$> mkVar nm (UUnused nm tpv)
    Un.PTuple p l -> fn . unzip =<< traverse indexUnPat l
      where fn (up,utp) =
              (UPatF p (UPTuple up),) <$> mkVar (show (ppUnPat upat)) (UTF (UTupleType utp))
    Un.PRecord p fpl
        | hasDups fl -> unFail p $ text "Duplicate field names in pattern."
        | otherwise -> fn . unzip =<< traverse indexUnPat pl
      where (fmap val -> fl,pl) = unzip fpl
            vfn upl = UPatF p $ UPRecord   $ Map.fromList $ fl `zip` upl
            fn (upl,tpl) =
              (vfn upl,) <$> mkVar (show (ppUnPat upat))
                                   (UTF $ URecordType $ Map.fromList $ fl `zip` tpl)
    Un.PCtor pnm pl -> do
      tc <- gets usGlobalContext
      (c,tp) <- lift $ resolveCtor tc pnm (length pl)
      let vfn upl = UPatF (pos pnm) (UPCtor c upl)
      first vfn <$> indexPiPats tc pl tp

-- | Match a typed pat against an untyped pat.
-- The types in the pattern are relative to the given unify local context.
matchUnPat :: forall s .
              UnifyLocalCtx s
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
        go (TCPVar nm i tp) unpat = StateT $ \m ->
             second (fn m) <$> indexUnPat unpat
           where fn m utp = Map.insert i (utp,nm,tp) m
        go TCPUnused{} unpat = StateT $ \m ->
           second (const m) <$> indexUnPat unpat
        go (TCPatF pf) unpat =
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
              (c',_) <- lift $ lift $ resolveCtor (ulcTC il) pnm (length upl)
              unless (c == c') (err (pos pnm))
              UPatF (pos pnm) . UPCtor c <$> zipWithM go pl upl
            _ -> err (pos unpat)

-- | The term should be typed to be valid in the global term context for the unifier.
indexPiPats :: TermContext s -> [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
indexPiPats uc = go [] (emptyLocalCtx uc)
  where go :: -- | Previous patterns 
              [UPat s]
              -- | Terms for substution.
           -> UnifyLocalCtx s
           -> [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
        go ppats lctx [] tp =
          (reverse ppats,) <$> mkUnifyTerm lctx tp
        go ppats lctx (unpat:upl) tp = do
          (p,_,r) <- lift (reduceToPiExpr (ulcTC lctx) (pos unpat) tp)
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

runUnifier :: TermContext s -> Pos -> Unifier s v -> TC s v
runUnifier uc p m = evalStateT m s0
  where s0 = US { usGlobalContext = uc
                , usPos = p
                , usVarCount = 0
                , usRigidCount = 0
                }

type LocalCtxBinding s = (VarIndex s, String, TCTerm)
 
-- | 
data UnifyLocalCtx s = UnifyLocalCtx { ulcTC :: TermContext s
                                     , ulcBindings :: [LocalCtxBinding s]
                                     }

mkHolTerm :: UnifyLocalCtx s -> TCTerm -> (TCTerm,[VarIndex s])
mkHolTerm ulc = go [] (ulcBindings ulc)
  where go pr [] tp = (tp,pr)
        go pr ((v,nm,tp):r) t = go (v:pr) r (TCPi (TCPVar nm 0 tp) tp t)

emptyLocalCtx :: TermContext s -> UnifyLocalCtx s
emptyLocalCtx tc = UnifyLocalCtx { ulcTC = tc, ulcBindings = [] }

-- | Returns number of bound variables in local context.
localCtxSize :: UnifyLocalCtx s -> Int
localCtxSize = length . ulcBindings

lookupLocalCtxVarIndex :: UnifyLocalCtx s -> Int -> Maybe (VarIndex s)
lookupLocalCtxVarIndex (ulcBindings -> l) i
    | 0 <= i && i < length l = let (v,_,_) = l !! i in Just v 
    | otherwise = Nothing

extendLocalCtx :: [LocalCtxBinding s] -> UnifyLocalCtx s -> Unifier s (UnifyLocalCtx s)
extendLocalCtx (b@(utp,nm,tp):r) ulc = do
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
      TCF tf -> mkTermVar . UTF =<< traverse (mkUnifyTerm l) tf
      TCLambda{} -> holTerm
      TCPi{} -> holTerm
      TCLet{} -> holTerm
      TCVar i tp -> mkVarVar (resolveBoundVar i (ulcTC l)) i tp
      TCLocalDef i tp -> mkVarVar (resolveLocalDef i (ulcTC l)) i tp
  where holTerm = mkTermVar (uncurry (UHolTerm t) (mkHolTerm l t))
        mkVarVar nm i tp =
          case lookupLocalCtxVarIndex l i of
            Just utp -> mkTermVar (UVar utp)
            Nothing -> mkTermVar (UOuterVar nm (localCtxSize l) i tp)
        mkTermVar = mkVar (show (ppTCTerm (ulcTC l) t))

data UnifyResult s
   = UR { urContext :: TermContext s
          -- | Position where unification occured (useful for unification errors involving
          -- the whole problem such as occurs check failures).
        , urPos :: Pos
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

occursCheckFailure :: String -> UResolver s a
occursCheckFailure nm = do
    p <- gets urPos
    lift $ tcFail p msg
  where msg = "Cyclic dependency detected during unification of " ++ nm

type UResolverCacheFn s k v = UnifyResult s -> UResolverCache s k v

uresolveCache :: Ord k
              => UResolverCacheFn s k v
              -> (k -> UResolver s v)
              -> String -> k -> UResolver s v
uresolveCache gfn rfn nm k = do
  cr <- gets gfn
  m0 <- lift $ liftST $ readSTRef cr
  case Map.lookup k m0 of
    Just (URSeen r) -> return r 
    Just URActive -> occursCheckFailure nm
    Nothing -> do
      lift $ liftST $ writeSTRef cr $ Map.insert k URActive m0
      r <- rfn k
      lift $ liftST $ modifySTRef cr $ Map.insert k (URSeen r)
      return r

resolve :: UResolver s a -> Unifier s (a, TermContext s)
resolve m = do
  us <- get
  rmc <- lift $ liftST newCache
  vmc <- lift $ liftST newCache
  let ur0 = UR { urContext = usGlobalContext us
               , urPos = usPos us
               , urLevel = 0               
               , urBoundMap = rmc
               , urVarMap = vmc
               }
  lift $ second urContext <$> runStateT m ur0

readVarState :: VarIndex s -> TC s (UVarState s)
readVarState v = liftST $ readSTRef (viRef v)

-- | Resolve a variable corresponding to an unused pattern variable,
-- returning index and type.
uresolveBoundVar :: String -> VarIndex s -> UResolver s (DeBruijnLevel, TCTerm)
uresolveBoundVar nm tpv = uresolveCache urBoundMap (uresolveBoundVar' nm) nm tpv

uresolveBoundVar' :: String -> VarIndex s -> UResolver s (DeBruijnLevel, TCTerm)
uresolveBoundVar' nm tpv = do
  (l,tp0) <- resolveUTerm tpv
  ur <- get
  let l' = urLevel ur
  let tp = incTCVars 0 (l' - l) tp0
  put ur { urContext = consBoundVar nm tp (urContext ur)
         , urLevel = urLevel ur + 1
         }
  return (l',tp)

-- | Convert a TCTerm at a given level to be valid at the current level.
resolveCurrent :: (DeBruijnLevel, TCTerm) -> UResolver s TCTerm
resolveCurrent (l,t) = mk <$> gets urLevel
  where mk l' = incTCVars 0 (l' - l) t

-- | Resolve a unifier pat to a tcpat.
resolvePat :: UPat s -> UResolver s (TCPat TCTerm)
resolvePat (UPVar v) = fn <$> uresolveBoundVar (rvrName v) (rvrType v)
  where fn = uncurry (TCPVar (rvrName v))
resolvePat (UPUnused v) = do 
  s <- lift $ readVarState v
  case s of
    UUnused nm tp -> uncurry (TCPVar nm) <$> uresolveBoundVar nm tp
    _ -> return $ TCPUnused
resolvePat (UPatF _ pf) = TCPatF <$> traverse resolvePat pf

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
resolveUTerm v = uresolveCache urVarMap resolveUTerm' (viName v) v

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm' :: VarIndex s -> UResolver s (DeBruijnLevel,TCTerm)
resolveUTerm' v = do
  -- Returns a refernce to a pattern variable with the given name, index, and type.
  let mkPatVarRef nm tpv = fn <$> uresolveBoundVar nm tpv
        where fn (i,tp) = (i+1, TCVar 0 (incTCVars 0 1 tp))
  uvs <- lift $ liftST $ readSTRef (viRef v)
  case uvs of
    URigidVar r -> mkPatVarRef (rvrName r) (rvrType r)
    UVar v -> resolveUTerm v
    UUnused nm tpv -> mkPatVarRef nm tpv
    UFreeType nm -> fail "Free type variable unbound during unification"
    UHolTerm ft _ c -> resolve <$> traverseResolveUTerm c
      where resolve (l,c') = (l,tcApply 0 (incTCVars 0 l ft) (V.fromList c'))
    UTF utf -> second TCF <$> traverseResolveUTerm utf
    UOuterVar _ lvl i tp -> pure (lvl,TCVar i tp)

-- | Typecheck pats against given expected type.
typecheckPats :: TermContext s
              -> [Un.Pat]
              -> TCTerm
              -> TC s ([TCPat TCTerm], TermContext s)
typecheckPats _ [] _ = fail "Unexpected attempt to typecheck empty list of pats"
typecheckPats tc upl@(up:_) tp = do
  rtp <- reduce tp
  runUnifier tc (pos up) $ do
    utp <- mkUnifyTerm (emptyLocalCtx tc) rtp
    (pl,utpl) <- unzip <$> traverse indexUnPat upl
    traverse_ (usetEqual utp) utpl
    resolve $ traverse resolvePat pl

-- | Typecheck pats against the given pi type.
typecheckPiPats :: TermContext s
                -> [Un.Pat]
                -> TCTerm
                -> TC s (([TCPat TCTerm],TCTerm), TermContext s)
typecheckPiPats uc [] tp = fail "Unexpected attempt to unify empty list of pi pats"
typecheckPiPats uc pats@(up:_) tp = do
  tp' <- reduce tp
  runUnifier uc (pos up) $ do
    (pl,utp') <- indexPiPats uc pats tp'
    resolve $ do
      pl' <- traverse resolvePat pl
      fmap (pl',) $ resolveCurrent =<< resolveUTerm utp'

tcEqns :: TermContext s -> TCTerm -> [UnDefEqn] -> TC s [TCDefEqn]
tcEqns tc tp ueqs = traverse (flip (tcEqn tc) tp) ueqs

-- | Typecheck equation is returns a term with the given type.
tcEqn :: TermContext s -> UnDefEqn -> TCTerm -> TC s TCDefEqn
tcEqn uc (DefEqnGen [] unrhs) tp = DefEqnGen [] <$> tcTerm uc unrhs tp
tcEqn uc (DefEqnGen unpats unrhs) tp = do
  ((pats,rhsTp), uc') <- typecheckPiPats uc unpats tp
  DefEqnGen pats <$> tcTerm uc' unrhs rhsTp

tcTerm :: TermContext s
       -- Typecheck term
       -> Un.Term
          -- | Required type type (actual type may be a subtype).
       -> TCTerm
       -- Typechecked term.
       -> TC s TCTerm
tcTerm tc ut rtp = do
  (v,tp) <- inferTypedValue tc ut
  v <$ checkTypeSubtype tc (pos ut) tp rtp

ppTCPat :: [Doc] -> TCPat TCTerm -> Doc
ppTCPat _ = unimpl "ppTCPat"

patVarNames :: TCPat TCTerm -> [Doc]
patVarNames _ = unimpl "patVarNames"

ppTCTermF :: Applicative f => (t -> f Doc) -> TCTermF t -> f Doc
ppTCTermF pp tf =
  case tf of
    UGlobal i -> pure $ ppIdent i
    UApp l r -> liftA2 (<+>) (pp l) (pp r)
    UTupleValue l -> parens . commaSepList <$> traverse pp l
    UTupleType l -> (char '#' <>) . parens . commaSepList <$> traverse pp l
    URecordValue m -> braces . semiTermList <$> traverse ppFld (Map.toList m)
      where ppFld (fld,v) = (text fld <+> equals <+>) <$> pp v
    URecordSelector t f -> (<> (char '.' <> text f)) <$> pp t
    URecordType m -> (char '#' <>) . braces . semiTermList <$> traverse ppFld (Map.toList m)
      where ppFld (fld,v) = ((text fld <+> equals) <+>) <$> pp v
    UCtorApp c l -> hsep . (ppIdent c :) <$> traverse pp l
    UDataType dt l -> hsep . (ppIdent dt :) <$> traverse pp l
    USort s -> pure $ text (show s)
    UNatLit i -> pure $ text (show i)
    UArray _ vl -> brackets . commaSepList <$> traverse pp (V.toList vl)

-- | Pretty print TC term with doc used for free variables.
ppTCTermGen :: [Doc] -> TCTerm -> Doc
ppTCTermGen d (TCF tf) = runIdentity $ ppTCTermF (Identity . ppTCTermGen d) tf
ppTCTermGen d (TCLambda p l r) = 
  char '\\' <> parens (ppTCPat d p <+> colon <+> ppTCTermGen d l) 
             <+> text "->" <+> ppTCTermGen (d ++ patVarNames p) r
ppTCTermGen d (TCPi p l r) =
  parens (ppTCPat d p <+> colon <+> ppTCTermGen d l) 
    <+> text "->" <+> ppTCTermGen (d ++ patVarNames p) r
ppTCTermGen d (TCLet bindings t) = unimpl "ppTCTerm Let"
ppTCTermGen d (TCVar i _) | 0 <= i && i < length d = d !! i
ppTCTermGen d (TCLocalDef i _) | 0 <= i && i < length d = d !! i

ppTCTerm :: TermContext s -> TCTerm -> Doc
ppTCTerm tc = ppTCTermGen (text <$> contextNames tc)

reduce :: TCTerm -> TC s TCTerm
reduce t@(TCF tf) =
  case tf of
{-
    UGlobal _ -> unimpl "reduce UGlobal"
    UApp l r -> unimpl "reduce UApp"
    URecordSelector{} -> unimpl "reduce URecordSelector"
-}
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
checkIsSort :: TermContext s -> Pos -> TCTerm -> TC s Sort
checkIsSort tc p = checkIsSort' tc p <=< reduce

-- | checkIsSort applied to reduced terms.
checkIsSort' :: TermContext s -> Pos -> TCTerm -> TC s Sort
checkIsSort' tc p t =
  case t of
    TCF (USort s) -> return s
    _ -> tctFail p $ ppTCTerm tc t <+> text "could not be interpreted as a sort."

-- | Typecheck a term as a type, returning a term equivalent to it, and
-- with the same type as the term.
tcType :: TermContext s -> Un.Term -> TC s (TCTerm,Sort)
tcType tc t = do
  (v,tp) <- inferTypedValue tc t
  (v,) <$> checkIsSort tc (pos t) tp

tcSort :: TermContext s -> Un.Term -> TC s Sort
tcSort tc t = checkIsSort tc (pos t) . fst =<< inferTypedValue tc t

tcSpecificDataType :: Ident -> TermContext s -> Un.Term -> TC s [TCTerm]
tcSpecificDataType expected uc ut = do
  (v,_) <- inferTypedValue uc ut
  rtp <- reduce v
  case rtp of
    TCF (UDataType i tl) | i == expected -> pure tl
    _ -> tcFail (pos ut) $ "Expected " ++ show expected

tcFixedPiType :: (TermContext s -> Un.Term -> TC s r)
              -> TermContext s -> Un.Term -> TC s (FixedPiType r)
tcFixedPiType fn = go 
  where go tc (Un.Pi _ pats@(fp:_) utp _ rhs) = do
          (tp,tps) <- tcType tc utp
          (pl, tc') <- typecheckPats tc pats tp
          (\r -> foldr (\pat -> FPPi pat tp) r pl) <$> go tc' rhs
        go tc ut = FPResult <$> fn tc ut

tcDTType :: TermContext s -> Un.Term -> TC s TCDTType
tcDTType = tcFixedPiType tcSort

tcCtorType :: Ident -> TermContext s -> Un.Term -> TC s TCCtorType
tcCtorType i = tcFixedPiType (tcSpecificDataType i)

maximumSort :: Foldable f => f Sort -> Sort
maximumSort = foldl' maxSort (mkSort 0)


inferTypedValue :: TermContext s -> Un.Term -> TC s (TCTerm, TCTerm)
inferTypedValue tc ut = do
  r <- inferTerm tc ut
  case r of
    PartialCtor{} ->
      tcFail (pos ut) $ "Expected additional argument to constructor."
    PartialDataType{} ->
      tcFail (pos ut) $ "Expected additional argument to data type."
    TypedValue v tp -> pure (v, tp)


inferLambda  :: TermContext s
             -> Pos
             -> [(Un.ParamType, [Un.Pat], Un.Term)] -- Patterns.
             -> Un.Term -- Right hand side of lambda expression
             -> TC s InferResult
inferLambda tc0 p pl0 urhs = go [] tc0 pl0
  where go args tc [] = mkRes <$> inferTypedValue tc urhs
          where mkRes (v,tp) = TypedValue v' tp'
                  where v'  = foldr (uncurry TCLambda) v args
                        tp' = foldr (uncurry TCPi) tp args
        go args tc1 ((_,patl,utp):l) = do
          (tp,_) <- tcType tc1 utp
          (pl,tc') <- typecheckPats tc1 patl tp
          let typedPL = (,tp) <$> pl 
          go (args ++ typedPL) tc' l

inferTerm :: TermContext s -> Un.Term -> TC s InferResult
inferTerm tc uut = do
  case uut of
    Un.Var i -> resolveIdent tc i
    Un.Unused{} -> fail "Pattern syntax when type expected."
    Un.Con i -> resolveIdent tc i
    Un.Sort p s -> return $ TypedValue (TCF (USort s)) (TCF (USort (sortOf s)))
    Un.Lambda p pl r -> inferLambda tc p pl r
    Un.App uf _ ua -> mkRes =<< inferTerm tc uf
      where mkRes (PartialCtor dt i rargs pat tp cur) = do
              (a,args) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              case cur of
                FPResult dtArgs -> pure $ TypedValue v tp'
                  where v = TCF (UCtorApp i (reverse (a:rargs)))
                        tp' = TCF (UDataType dt (fmapTCApply dtArgs args))
                FPPi p tp next -> pure $ PartialCtor dt i (a:rargs) p' tp' next'
                  where p' = tcPatApply 0 p args
                        tp' = tcApply 0 tp args
                        next' = tcCtorTypeApply next args
            mkRes (PartialDataType dt rargs pat tp cur) = do
              (a,args) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              case cur of
                FPResult s -> pure $ TypedValue v (TCF (USort s))
                  where v = TCF (UDataType dt (reverse (a:rargs)))
                FPPi p tp next -> pure $ PartialDataType dt (a:rargs) p' tp' next'
                  where p' = tcPatApply 0 p args
                        tp' = tcApply 0 tp args
                        next' = tcDTTypeApply next args
            mkRes (TypedValue v tp0) = do
              (pat,patTp,tp) <- reduceToPiExpr tc (pos uf) tp0
              let vfn a = TCF (UApp v a)
                  tpfn args = tcApply 0 tp args
              fmap (uncurry TypedValue . (vfn *** tpfn)) $
                matchPat tc (pos ua) pat =<< tcTerm tc ua patTp

    Un.Pi _ [] _ _ _ -> fail "Pi with no paramters encountered."
    Un.Pi _ pats@(fp:_) utp _ rhs -> do
      (tp,tps) <- tcType tc utp
      (pl, tc') <- typecheckPats tc pats tp
      (rest,rps) <- tcType tc' rhs
      let v' = foldr (\pat -> TCPi pat tp) rest pl
      return $ TypedValue v' (TCF (USort (maxSort tps rps)))

    Un.TupleValue _ tl -> do
      (vl,tpl) <- unzip <$> traverse (inferTypedValue tc) tl
      return $ TypedValue (TCF (UTupleValue vl)) (TCF (UTupleType tpl))
    Un.TupleType p tl  -> do
      (tpl,sl) <- unzip <$> traverse (tcType tc) tl
      return $ TypedValue (TCF (UTupleType tpl))
                          (TCF (USort (maximumSort sl)))

    Un.RecordValue p (unzip -> (fmap val -> fl,vl))
        | hasDups fl -> tcFail p "Duplicate fields in record"
        | otherwise -> uncurry TypedValue . mkRes . unzip <$> traverse (inferTypedValue tc) vl
      where mkMap fn vals = TCF (fn (Map.fromList (fl `zip` vals)))
            mkRes = mkMap URecordValue *** mkMap URecordType
    Un.RecordSelector ux (PosPair p f) -> do
      (x,tp) <- inferTypedValue tc ux
      m <- reduceToRecordType tc p tp
      case Map.lookup f m of
        Nothing -> tcFail p $ "No field named " ++ f ++ " in record."
        Just ftp -> return $ TypedValue (TCF (URecordSelector x f)) ftp
    Un.RecordType p (unzip -> (fmap val -> fl,vl))
        | hasDups fl -> tcFail p "Duplicate fields in record"
        | otherwise -> uncurry TypedValue . mkRes . unzip <$> traverse (tcType tc) vl
      where mkMap fn vals = TCF (fn (Map.fromList (fl `zip` vals)))
            mkRes = (mkMap URecordType) *** (TCF . USort . maximumSort)
    Un.TypeConstraint ut _ utp -> do
      (tp,_) <- tcType tc utp
      flip TypedValue tp <$> tcTerm tc ut tp
    Un.Paren _ t -> uncurry TypedValue <$> inferTypedValue tc t
    Un.LetTerm p udl urhs -> do
      (tc', lcls) <- tcLocalDecls tc p udl
      uncurry TypedValue <$> inferTypedValue tc' urhs
    Un.IntLit p i | i < 0 -> fail $ ppPos p ++ " Unexpected negative natural number literal."
                  | otherwise -> pure $ TypedValue (TCF (UNatLit i)) nattp
      where natIdent = mkIdent (mkModuleName ["Prelude"]) "Nat"
            nattp = TCF (UDataType natIdent [])
    Un.BadTerm p -> fail $ "Encountered bad term from position " ++ show p


tcLocalDecls :: TermContext s
             -> Pos
             -> [Un.Decl]
             -> TC s (TermContext s, [TCLocalDef])
tcLocalDecls tc0 p lcls = do
    (tps,pending) <- unzip <$> traverse tcLclType (groupLocalDecls lcls)
    let tc = consLocalDefs tps tc0
    traverse_ ($ tc) pending
    let mkDef (LocalFnDefGen nm tp r) = LocalFnDefGen nm tp <$> eval p r
    (tc,) <$> traverse mkDef tps
  where tcLclType (LocalFnDefGen nm utp ueqs) = do
          (tp,_) <- tcType tc0 utp
          r <- newRef nm
          let pendingFn tc = assign r (tcEqns tc tp ueqs)
          return (LocalFnDefGen nm tp r, pendingFn)

tcAsApp :: TCTerm -> (TCTerm, [TCTerm])
tcAsApp = go []
  where go r (TCF (UApp f v)) = go (v:r) f
        go r f = (f,r) 

-- | Check types in two terms are equal.
checkTypesEqual :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual tc p x y = do
  xr <- reduce x
  yr <- reduce y
  checkTypesEqual' tc p xr yr

-- | Check types applied to reduced terms.
checkTypesEqual' :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual' tc p x y = do
  let checkAll :: Foldable t => t (TCTerm, TCTerm) -> TC s ()
      checkAll = mapM_ (uncurry (checkTypesEqual tc p))
  case (tcAsApp x, tcAsApp y) of
    ( (TCF (UGlobal xg), xa), (TCF (UGlobal yg), ya))
      | xg == yg && length xa == length ya -> do
        checkAll (zip xa ya)

    ( (TCF (UTupleValue xa), []), (TCF (UTupleValue ya), []))
      | length xa == length ya ->
        checkAll (zip xa ya)
    ( (TCF (UTupleType xa), []), (TCF (UTupleType ya), []))
      | length xa == length ya ->
        checkAll (zip xa ya)

    ( (TCF (URecordValue xm), []), (TCF (URecordValue ym), []))
      | Map.keys xm == Map.keys ym ->
        checkAll (Map.intersectionWith (,) xm ym)
    ( (TCF (URecordSelector xr xf), []), (TCF (URecordSelector yr yf), []))
      | xf == yf ->
        checkTypesEqual tc p xr yr
    ( (TCF (URecordType xm), []), (TCF (URecordType ym), []))
      | Map.keys xm == Map.keys ym ->
        checkAll (Map.intersectionWith (,) xm ym)

                 
    ( (TCF (UCtorApp xc xa), []), (TCF (UCtorApp yc ya), []))
      | xc == yc ->
        checkAll (zip xa ya)
    ( (TCF (UDataType xdt xa), []), (TCF (UDataType ydt ya), []))
      | xdt == ydt ->
        checkAll (zip xa ya)

    ( (TCF (USort xs), []), (TCF (USort ys), [])) | xs == ys -> return ()

    ( (TCF (UNatLit xi), []), (TCF (UNatLit yi), [])) | xi == yi -> return ()
    ( (TCF (UArray xtp xv), []), (TCF (UArray ytp yv), []))
      | V.length xv == V.length yv ->
         checkTypesEqual tc p xtp ytp *> checkAll (V.zip xv yv)

    ( (TCVar xi _, xa), (TCVar yi _, ya))
      | xi == yi && length xa == length ya ->
        checkAll (zip xa ya)

    _ -> do
       tcFail p $ show $ text "Equivalence check failed during typechecking:"  $$
          nest 2 (text $ show x) $$ text "and\n" $$
          nest 2 (text $ show y)

-- | @checkTypeSubtype tc p x y@ checks that @x@ is a subtype of @y@.
checkTypeSubtype :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypeSubtype tc p x y = do
  xr <- reduce x
  yr <- reduce y
  let ppFailure = tcFail p (show msg)
        where msg = ppTCTerm tc xr <+> text "is not a subtype of" <+> ppTCTerm tc yr <> char '.'
  case (tcAsApp xr, tcAsApp yr) of
    ( (TCF (USort xs), []), (TCF (USort ys), []) )
      | xs <= ys -> return ()
      | otherwise -> ppFailure
    _ -> checkTypesEqual' tc p xr yr

unimpl :: String -> a
unimpl nm = error (nm ++ " unimplemented")

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
matchPat :: TermContext s -> Pos -> TCPat TCTerm -> TCTerm -> TC s (TCTerm, Vector TCTerm)
matchPat tc p pat t = second finish <$> runStateT (go (pat, t)) Map.empty
  where finish = V.reverse . V.fromList . Map.elems 
        go :: (TCPat TCTerm, TCTerm) -> StateT (Map Int TCTerm) (TC s) TCTerm
        go (TCPVar _ i _, t) = t <$ modify (Map.insert i t)
        go (TCPUnused, t) = return t
        go (TCPatF pf, t) = do
          rt <- lift $ reduce t
          case (pf,rt) of
            (UPTuple pl, TCF (UTupleValue tl)) | length pl == length tl ->
              TCF . UTupleValue <$> traverse go (zip pl tl)
              
            (UPRecord pm, TCF (URecordValue tm)) | Map.keys pm == Map.keys tm ->
              TCF . URecordValue <$> traverse go (Map.intersectionWith (,) pm tm)
            (UPCtor pc pl, TCF (UCtorApp tc tl)) | pc == tc ->
              TCF . UCtorApp tc <$> traverse go (zip pl tl)
            _ -> lift $ tcFail p $ "Pattern match failed."

-- | Attempt to reduce a term to a  pi expression, returning the pattern, type
-- of the pattern and the right-hand side.
-- Reports error if htis fails.
reduceToPiExpr :: TermContext s -> Pos -> TCTerm -> TC s (TCPat TCTerm, TCTerm, TCTerm)
reduceToPiExpr tc p tp = do
  rtp <- reduce tp
  case rtp of
    TCPi pat l r -> return (pat,l,r)
    _ -> tctFail p $ text "Unexpected argument to term with type:" $$
                         nest 2 (ppTCTerm tc rtp)

reduceToRecordType :: TermContext s -> Pos -> TCTerm -> TC s (Map FieldName TCTerm)
reduceToRecordType tc p tp = do
  rtp <- reduce tp
  case rtp of
    TCF (URecordType m) -> return m
    _ -> tctFail p $ text "Attempt to dereference field of term with type:" $$ 
                       nest 2 (ppTCTerm tc rtp)


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
      tcTerm tc ut =<< inferTerm tc utp
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
      t <- tcTerm tc ut lhsType
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
evalDataType (DataTypeGen n tp ctp) =
  liftM2 (DataTypeGen n)
         (topEval tp) 
         (traverse (traverse topEval) ctp)

evalDef :: TCRefDef s -> TC s TCDef
evalDef (DefGen nm tpr elr) =
  liftA2 (DefGen nm) (Identity <$> topEval tpr) (Identity <$> topEval elr)

data CompletionContext = CC { ccModule :: Module }

{-
bindPat :: CompletionContext -> TCPat TCTerm -> (CompletionContext,Pat Term)
bindPat _ _ = undefined
-}

completeDataType :: CompletionContext
                 -> TCDataType
                 -> TypedDataType
completeDataType cc (DataTypeGen dt tp cl) = 
  DataType { dtName = dt
           , dtType = completeTerm cc (termFromTCDTType tp)
           , dtCtors = fmap (completeTerm cc . termFromTCCtorType dt) <$> cl
           }

completeDef :: CompletionContext
            -> TCDef
            -> TypedDef
completeDef cc (DefGen nm tp el) = def
  where def = Def { defIdent = nm 
                  , defType = completeTerm cc (runIdentity tp)
                  , defEqs = completeDefEqn cc <$> (runIdentity el) 
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

includeNameInModule :: Maybe Un.ImportConstraint -> Ident -> Bool
includeNameInModule mic = fn . identName
  where fn = case mic of
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
    let gc0 = emptyGlobalContext
    let is0 = IS { isModuleName = nm
                 , isCtx = gc0
                 , isPending = []
                 }
    let eqnMap = multiMap [ (val psym, DefEqnGen (snd <$> lhs) rhs)
                          | Un.TermDef psym lhs rhs <- d
                          ]
    -- Parse imports and declarations.
    let actions = fmap (parseImport moduleMap) iml
               ++ fmap (parseDecl eqnMap) d
    is <- execStateT (sequenceA_ actions) is0
    let gc = isCtx is
    let tc = emptyTermContext gc
    -- Execute pending assignments with final TermContext.
    sequence_ $ (($ tc) <$> isPending is)
    
    let mkFinal tps defs = m
          where cc = CC { ccModule = m
                        }
                m = flip (foldl' insDef) (completeDef cc <$> defs)
                  $ flip (foldl' insDataType) (completeDataType cc <$> tps)
                  $ emptyModule nm
    liftA2 mkFinal
           (traverse evalDataType (gcTypes gc))
           (traverse evalDef (gcDefs gc))

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

liftTCTerm :: TermContext s -> Term -> TC s TCTerm
liftTCTerm _ _ = unimpl "liftTCTerm"

liftTCDefEqn :: TermContext s -> TypedDefEqn -> TC s TCDefEqn
liftTCDefEqn _ _ = unimpl "liftTCDefEqn"

liftTCDataType :: TermContext s -> Term -> TC s TCDTType
liftTCDataType _ = unimpl "liftTCDataType"

liftTCCtorType :: TermContext s -> Term -> TC s TCCtorType
liftTCCtorType _ = unimpl "liftTCCtorType"


-- | Typechecker computation that needs input before running.
type PendingAction s a = a -> TC s ()

mkPendingAssign :: TCRef s v -> (a -> TC s v) -> PendingAction s a
mkPendingAssign r f a = assign r (f a)

data InitState s = IS { isModuleName :: ModuleName
                      , isCtx :: GlobalContext s
                      , isPending :: [ PendingAction s (TermContext s) ]
                      }

type Initializer s a = StateT (InitState s) (TC s) a

initModuleName :: Initializer s ModuleName
initModuleName = gets isModuleName

updateIsCtx :: (GlobalContext s -> GlobalContext s) -> Initializer s ()
updateIsCtx f = modify $ \s -> s { isCtx = f (isCtx s) }

addPending :: NodeName -> (TermContext s -> TC s r) -> Initializer s (TCRef s r)
addPending nm fn = do
  r <- lift $ newRef nm  
  r <$ modify (\s -> s { isPending = mkPendingAssign r fn : isPending s })

parseCtor :: Ident -> Un.CtorDecl -> Initializer s (Bool, TCRefCtor s)
parseCtor dt (Un.Ctor pnm utp) = do
  mnm <- initModuleName
  tp <- addPending (val pnm) (\tc -> tcCtorType dt tc utp)
  let ci = mkIdent mnm (val pnm)
  return (True, Ctor { ctorName = ci, ctorType = tp })

parseDecl :: Map String [UnDefEqn] -> Un.Decl -> Initializer s ()
parseDecl eqnMap d = do
  mnm <- initModuleName
  case d of
    Un.TypeDecl idl utp -> do
      let id1:_ = idl
      rtp <- addPending (val id1) (\uc -> fst <$> tcType uc utp)
      for_ idl $ \(PosPair p nm) -> do
        let ueqs = fromMaybe [] $ Map.lookup nm eqnMap
        eqs <- addPending ("Equations for " ++ nm) $ \tc -> do
          tp <- eval p rtp
          tcEqns tc tp ueqs
        let di = mkIdent mnm nm
        updateIsCtx $ insertDef [Nothing] True (DefGen di rtp eqs)
    Un.DataDecl psym utp ucl -> do
      let dti = mkIdent mnm (val psym)
      dt <- liftA2 (DataTypeGen dti)
                   (addPending (val psym) (\tc -> tcDTType tc utp))
                   (traverse (parseCtor dti) ucl)
      updateIsCtx $ insertDataType [Nothing] True dt
    Un.TermDef{} -> return ()

parseImport :: Map ModuleName Module
            -> Un.Import
            -> Initializer s ()
parseImport moduleMap (Un.Import q (PosPair p nm) mAsName mcns) = do
  case Map.lookup nm moduleMap of
    Nothing -> lift $ tcFail p $ "Cannot find module " ++ show nm ++ "."
    Just m -> do
      -- Get list of module names to use for local identifiers.
      let mnml | q = [Just qnm]
               | otherwise = [Nothing, Just qnm]
            where qnm = maybe (moduleName m)
                              (\s -> Un.mkModuleName [s])
                              (val <$> mAsName)
      -- Add datatypes to module
      for_ (moduleDataTypes m) $ \dt -> do
        let dtnm = dtName dt
        dtr <- addPending (identName dtnm) $ \tc ->
          liftTCDataType tc (dtType dt)
        -- Add constructors to module.
        cl <- for (dtCtors dt) $ \c -> do
          let cnm = ctorName c
              cfn tc = liftTCCtorType tc (ctorType c)
          let use = includeNameInModule mcns cnm
          (use,) . Ctor cnm <$> addPending (identName cnm) cfn
        let dtuse = includeNameInModule mcns dtnm
        updateIsCtx $ insertDataType mnml dtuse (DataTypeGen dtnm dtr cl)
      -- Add definitions to module.
      for_ (moduleDefs m) $ \def -> do
        let inm = identName (defIdent def)
        tpr <- addPending inm $ \tc ->
          liftTCTerm tc (defType def)
        eqr <- addPending inm $ \tc ->
          traverse (liftTCDefEqn tc) (defEqs def)
        let use = includeNameInModule mcns (defIdent def)
        updateIsCtx $ insertDef mnml use (DefGen (defIdent def) tpr eqr)