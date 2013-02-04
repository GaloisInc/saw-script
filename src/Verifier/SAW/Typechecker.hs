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
import Control.Arrow ((***), first, second, (+++), right)
import Control.Exception (assert)

import Control.Monad (liftM2, liftM3, zipWithM_)
import Control.Monad.Error (ErrorT, runErrorT, throwError)
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
        Just $ (lvl - l, BoundVar nm (incTCVars (lvl - l) tp))
      Just (l, (LocalDef nm tp)) -> assert (l < lvl) $ 
        Just $ (lvl - l, LocalDef nm (incTCVars (lvl - l) tp))
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
                  where eqs = fromMaybe [] $ Map.lookup nm eqMap
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
  | UHolTerm (TermContext s,TCTerm) -- Type with free variables.
             [VarIndex s] -- Variables bound to type.
  | UTF (TCTermF (VarIndex s))
    -- A variable bound outside the context of the unification problem with name and type
    -- relative to when before unification began.
  | UOuterVar String DeBruijnIndex

  | UOuterLet DeBruijnIndex -- DeBruijnIndex in outer context.

data UPat s
  = UPVar (RigidVarRef s)
  | UPUnused (VarIndex s)
  | UPatF Un.Pos (PatF (UPat s))
  deriving (Show)

type TCDataType = DataTypeGen TCDTType (Ctor Ident TCCtorType)
type TCDef = TCDefGen Identity

fmapTCApply :: Functor f
             => (TermContext s, f TCTerm)
             -> (TermContext s, Vector TCTerm)
             -> f TCTerm
fmapTCApply (sTC, s) (vTC,v) = (\t -> tcApply vTC (sTC,t) (vTC,v)) <$> s

type PatVarParser = State (Map Int (String,TCTerm)) ()

addPatBindings :: TCPat -> PatVarParser
addPatBindings (TCPVar nm i tp) = modify $ Map.insert i (nm,tp)
addPatBindings TCPUnused{} = return ()
addPatBindings (TCPatF pf) = traverse_ addPatBindings pf 

runPatVarParser :: PatVarParser -> [(String,TCTerm)]
runPatVarParser pvp = Map.elems (execState pvp Map.empty)

patBoundVars :: TCPat -> [(String,TCTerm)]
patBoundVars pat = runPatVarParser (addPatBindings pat)

extendPatContext :: TermContext s -> TCPat -> TermContext s
extendPatContext tc0 pat = foldr (uncurry consBoundVar) tc0 (patBoundVars pat)

tcFixedPiApply :: ((TermContext s, r) -> (TermContext s, Vector TCTerm) -> r)
               -> (TermContext s, FixedPiType r)
               -> (TermContext s, Vector TCTerm)
               -> FixedPiType r
tcFixedPiApply base = go
  where go (itc, FPResult r) v = FPResult (base (itc, r) v)
        go (itc, FPPi pat tp r) (vtc, v) = FPPi pat' tp' r'
          where pat' = tcPatApply vtc (itc, pat) (vtc, v)
                tp' = tcApply vtc (itc, tp) (vtc, v)
                itc' = extendPatContext itc pat
                vtc' = extendPatContext vtc pat'
                v' = fmap (\t -> applyExt (vtc,t) vtc') v
                r' = go (itc', r) (vtc', v')


tcDTTypeApply :: (TermContext s, TCDTType)
              -> (TermContext s, Vector TCTerm) -> TCDTType
tcDTTypeApply = tcFixedPiApply (\(_,s) _ -> s)

tcCtorTypeApply :: (TermContext s, TCCtorType)
                -> (TermContext s, Vector TCTerm)
                -> TCCtorType
tcCtorTypeApply = tcFixedPiApply base
  where base (itc, tl) (vtc,v) = (\t -> tcApply vtc (itc,t) (vtc, v)) <$> tl

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
-}

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
 
newRigidVar :: Un.Pos -> String -> Unifier s (RigidVarRef s, VarIndex s)
newRigidVar p nm = do
  tp <- mkVar ("type of " ++ nm) (UFreeType nm)
  s <- get
  let idx = usRigidCount s
  let rv = RigidVarRef { rvrIndex = idx
                       , rvrPos = p
                       , rvrName = nm
                       , rvrType = tp
                       }
  (rv,tp) <$ put s { usRigidCount = idx + 1 }

ppUTerm :: UVarState s -> TC s Doc
ppUTerm vs0 = evalStateT (go vs0) Set.empty
  where goVar :: VarIndex s -> StateT (Set (VarIndex s)) (TC s) Doc
        goVar v = do
          s <- get
          if Set.member v s then
            return $ text (viName v)
          else do
            put (Set.insert v s)
            go =<< lift (liftST (readSTRef (viRef v)))
        go :: UVarState s -> StateT (Set (VarIndex s)) (TC s) Doc
        go (UVar v) = goVar v
        go (URigidVar r) = pure (text (rvrName r))
        go (UUnused nm _) = pure (text nm)
        go (UFreeType nm) = pure (text $ "typeOf(" ++ nm ++ ")")
        go (UHolTerm t bindings) = unimpl "ppUTerm"          
        go (UTF tf) = ppTCTermF goVar tf
        go (UOuterVar nm _) = pure (text nm)



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
    (UHolTerm (tc1,t1) c1, UHolTerm (tc2,t2) c2) | length c1 == length c2 -> do
      -- Check that txf and tyf are equivalent
      tc <- gets usGlobalContext
      p <- gets usPos
      let t1' = boundFreeVarsWithPi (tc1,t1) tc
          t2' = boundFreeVarsWithPi (tc2,t2) tc
      lift $ checkTypesEqual p [] tc t1' t2'
      -- Unify corresponding entries in cx and cy.
      zipWithM usetEqual c1 c2
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

-- | Return true if set has duplicates.
hasDups :: Ord a => [a] -> Bool
hasDups l = Set.size (Set.fromList l) < length l

ppUnPat :: Un.Pat -> Doc
ppUnPat _ = unimpl "ppUnPat"

upatToTerm :: UPat s -> Unifier s (VarIndex s)
upatToTerm (UPVar r) = mkVar (rvrName r) (URigidVar r)
upatToTerm (UPUnused v) = pure v
upatToTerm (UPatF _ pf) =
  case pf of
    UPTuple l -> do
      lv <- traverse upatToTerm l
      mkVar "tuple" . UTF . UTupleValue =<< traverse upatToTerm l
    UPRecord m -> do
      mkVar "record" . UTF . URecordValue =<< traverse upatToTerm m
    UPCtor c l -> do
      mkVar "ctor" . UTF . UCtorApp c =<< traverse upatToTerm l

-- | Create a upat from a untyped pat, and return and it's type.
indexUnPat :: Un.Pat -> Unifier s (UPat s, VarIndex s)
indexUnPat upat =
  case upat of
    Un.PVar (PosPair p nm) -> first UPVar <$> newRigidVar p nm
    Un.PUnused (PosPair p nm) -> do
      tpv <- mkVar ("type of " ++ nm) (UFreeType nm)
      v <- mkVar nm (UUnused nm tpv)
      return (UPUnused v, tpv)
    Un.PTuple p l -> do
        (up,utp) <- unzip <$> traverse indexUnPat l
        tpv <-  mkVar (show (ppUnPat upat)) (UTF (UTupleType utp))
        return (UPatF p (UPTuple up), tpv)
    Un.PRecord p fpl
        | hasDups (val . fst <$> fpl) ->
           unFail p $ text "Duplicate field names in pattern."
        | otherwise -> do
           rm <- traverse indexUnPat (Map.fromList (first val <$> fpl))
           tpv <- mkVar (show (ppUnPat upat))
                        (UTF $ URecordType (fmap snd rm))
           return (UPatF p (UPRecord (fmap fst rm)), tpv)
    Un.PCtor pnm pl -> do
      tc <- gets usGlobalContext
      (c,tp) <- lift $ resolveCtor tc pnm (length pl)
      let vfn upl = UPatF (pos pnm) (UPCtor c upl)
      first vfn <$> indexPiPats pl tp

-- | Match a typed pat against an untyped pat.
-- The types in the pattern are relative to the given unify local context.
matchUnPat :: forall s .
              UnifyLocalCtx s
           -> TCPat
           -> Un.Pat
           -> Unifier s (UPat s,UnifyLocalCtx s)
matchUnPat il itcp iup = do
    (up,m) <- runStateT (go itcp iup) Map.empty
    (up,) <$> extendLocalCtx (Map.elems m) il
  where err p = lift $ unFail p $ text "Failed to match pattern against type."
        go :: TCPat -> Un.Pat
           -> StateT (Map Int (LocalCtxBinding s))
                     (Unifier s)
                     (UPat s) 
        go (TCPVar nm i tp) unpat = StateT $ \m -> do
             (up,utp) <- indexUnPat unpat
             u <- upatToTerm up
             return (up, Map.insert i (u,utp,nm,tp) m)
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
              tc <- lift $ gets usGlobalContext
              (c',_) <- lift $ lift $ resolveCtor tc pnm (length upl)
              unless (c == c') (err (pos pnm))
              UPatF (pos pnm) . UPCtor c <$> zipWithM go pl upl
            _ -> err (pos unpat)

-- | This 
indexPiPats :: [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
indexPiPats unpats0 tp0 = do
    tc <- gets usGlobalContext
    go [] unpats0 (emptyLocalCtx tc, tp0)
  where go :: -- | Previous patterns 
              [UPat s]
              -- | Terms for substution.
           -> [Un.Pat]
           -> (UnifyLocalCtx s, TCTerm) -> Unifier s ([UPat s], VarIndex s)
        go ppats [] (lctx, tp) =
          (reverse ppats,) <$> mkUnifyTerm lctx tp
        go ppats (unpat:upl) (lctx,tp) = do
          (p,_,r) <- lift $ reduceToPiExpr (ulcTC lctx) (pos unpat) tp
          (up,lctx') <- matchUnPat lctx p unpat
          go (up:ppats) upl (lctx', r)

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

runUnifier :: TermContext s -> Pos -> Unifier s v -> TC s v
runUnifier uc p m = evalStateT m s0
  where s0 = US { usGlobalContext = uc
                , usPos = p
                , usVarCount = 0
                , usRigidCount = 0
                }

-- | Variable, the type, and name, and type.
type LocalCtxBinding s = (VarIndex s, VarIndex s, String, TCTerm)
 
-- | 
data UnifyLocalCtx s = UnifyLocalCtx { ulcTC :: TermContext s
                                     , ulcBindings :: [LocalCtxBinding s]
                                     }

mkHolTerm :: UnifyLocalCtx s -> TCTerm -> UVarState s
mkHolTerm ulc t = UHolTerm (ulcTC ulc, t) (go <$> ulcBindings ulc)
  where go (v,_,_,_) = v

emptyLocalCtx :: TermContext s -> UnifyLocalCtx s
emptyLocalCtx tc = UnifyLocalCtx { ulcTC = tc, ulcBindings = [] }

-- | Returns number of bound variables in local context.
localCtxSize :: UnifyLocalCtx s -> Int
localCtxSize = length . ulcBindings

lookupLocalCtxVar :: UnifyLocalCtx s -> Int -> Maybe (VarIndex s)
lookupLocalCtxVar (ulcBindings -> l) i
    | 0 <= i && i < length l = let (v,_,_,_) = l !! i in Just v 
    | otherwise = Nothing

extendLocalCtx :: [LocalCtxBinding s] -> UnifyLocalCtx s -> Unifier s (UnifyLocalCtx s)
extendLocalCtx (b@(v,vtp,nm,tp):r) ulc = do
  usetEqual vtp =<< mkUnifyTerm ulc tp
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
      TCVar i -> do        
          case lookupLocalCtxVar l i of
            Just v -> return v
            Nothing -> mkTermVar (UOuterVar nm (i - localCtxSize l))
        where nm = resolveBoundVar i (ulcTC l)
      TCLocalDef i | i >= localCtxSize l -> mkTermVar (UOuterLet (i - localCtxSize l))
                   | otherwise -> error "mkUnifyTerm encountered unexpected local def."
  where holTerm = mkTermVar (mkHolTerm l t)
        mkTermVar = mkVar "intermediate term"

data UnifyResult s
   = UR { -- | Context when unification began
          urOuterContext :: TermContext s
          -- Current context
        , urContext :: TermContext s
        , urBoundMap :: UResolverCache s (VarIndex s) (TermContext s, TCTerm)
        -- | Cache that maps variables to their typechecked value at the
        -- given deBruijnIndex.
        , urVarMap :: UResolverCache s (VarIndex s) (TermContext s, TCTerm)
        }

newtype UResolver s v
  = URR { unURR :: UnifyResult s -> ST s (Either String (v, UnifyResult s)) }

instance Functor (UResolver s) where
  fmap f (URR fn) = URR $ \r -> fmap (right (first f)) (fn r)

instance Applicative (UResolver s) where 
  pure = return
  (<*>) = ap

instance Monad (UResolver s) where
  fail msg = URR $ \_ -> return (Left msg)
  return v = URR $ \r -> return (Right (v,r))
  URR f >>= h = URR $ \r -> do
    c <- f r
    case c of
      Left msg -> return (Left msg)
      Right (v,r') -> unURR (h v) r'

instance MonadState (UnifyResult s) (UResolver s) where
  get = URR $ \r -> return (Right (r,r))
  put r = URR $ \_ -> return (Right ((), r))

urST :: ST s v -> UResolver s v
urST m = URR $ \r -> fmap (\v -> Right (v,r)) m

data URRes v = URSeen v
             | URActive

type UResolverCache s k v = STRef s (Map k (URRes v))

newCache :: ST s (UResolverCache s k v)
newCache = newSTRef Map.empty

occursCheckFailure :: String -> UResolver s a
occursCheckFailure nm = fail msg
  where msg = "Cyclic dependency detected during unification of " ++ nm

type UResolverCacheFn s k v = UnifyResult s -> UResolverCache s k v

uresolveCache :: Ord k
              => UResolverCacheFn s k v
              -> (k -> UResolver s v)
              -> String
              -> k
              -> UResolver s v
uresolveCache gfn rfn nm k = do
  cr <- gets gfn
  m0 <- urST $ readSTRef cr
  case Map.lookup k m0 of
    Just (URSeen r) -> return r 
    Just URActive -> occursCheckFailure nm
    Nothing -> do
      urST $ writeSTRef cr $ Map.insert k URActive m0
      r <- rfn k
      urST $ modifySTRef cr $ Map.insert k (URSeen r)
      return r

resolve :: UResolver s a -> Unifier s (Either String (a, TermContext s))
resolve (URR m) = do
  us <- get
  lift $ do
    rmc <- liftST newCache
    vmc <- liftST newCache
    let ur0 = UR { urOuterContext = usGlobalContext us
                 , urContext = usGlobalContext us
                 , urBoundMap = rmc
                 , urVarMap = vmc
                 }
    right (second urContext) <$> liftST (m ur0)

readVarState :: VarIndex s -> UResolver s (UVarState s)
readVarState v = urST $ readSTRef (viRef v)

-- | Resolve a variable corresponding to an unused pattern variable,
-- returning index and type.
uresolveBoundVar :: String -> VarIndex s -> UResolver s (TermContext s, TCTerm)
uresolveBoundVar nm tpv = uresolveCache urBoundMap (uresolveBoundVar' nm) nm tpv

uresolveBoundVar' :: String -> VarIndex s -> UResolver s (TermContext s, TCTerm)
uresolveBoundVar' nm tpv = do
  tp <- resolveCurrent =<< resolveUTerm tpv
  ur <- get
  put ur { urContext = consBoundVar nm tp (urContext ur)
         }
  return (urContext ur, tp)

-- | Convert a TCTerm at a given level to be valid at the current level.
resolveCurrent :: (TermContext s, TCTerm) -> UResolver s TCTerm
resolveCurrent p = mk <$> gets urContext
  where mk tc = applyExt p tc

-- | Resolve a unifier pat to a tcpat.
resolvePat :: UPat s -> UResolver s TCPat
resolvePat (UPVar v) = do
  (tc,tp) <- uresolveBoundVar (rvrName v) (rvrType v)
  tc0 <- gets urOuterContext
  return $ TCPVar (rvrName v) (boundVarDiff tc tc0) tp
resolvePat (UPUnused v) = do 
  s <- readVarState v
  case s of
    UUnused nm vtp -> do
     (tc,tp) <- uresolveBoundVar nm vtp
     tc0 <- gets urOuterContext
     return $ TCPVar nm (boundVarDiff tc tc0) tp
    _ -> return $ TCPUnused
resolvePat (UPatF _ pf) = TCPatF <$> traverse resolvePat pf

traverseResolveUTerm :: Traversable t
                     => t (VarIndex s)
                     -> UResolver s (TermContext s, t TCTerm)
traverseResolveUTerm tv = do
  ttf <- traverse resolveUTerm tv
  tc <- gets urContext
  return $ (tc, flip applyExt tc <$> ttf)

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm :: VarIndex s -> UResolver s (TermContext s, TCTerm)
resolveUTerm v = uresolveCache urVarMap resolveUTerm' (viName v) v

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm' :: VarIndex s -> UResolver s (TermContext s, TCTerm)
resolveUTerm' v = do
  -- Returns a refernce to a pattern variable with the given name, index, and type.
  let mkPatVarRef nm tpv = fn <$> uresolveBoundVar nm tpv
        where fn (tc,tp) = (consBoundVar nm tp tc, TCVar 0)
  uvs <- urST $ readSTRef (viRef v)
  case uvs of
    URigidVar r -> mkPatVarRef (rvrName r) (rvrType r)
    UVar v -> resolveUTerm v
    UUnused nm tpv -> mkPatVarRef nm tpv
    UFreeType nm -> fail "Free type variable unbound during unification"
    UHolTerm f c -> do
      baseTC <- gets urOuterContext
      let resolve p@(tc,_) = (tc, tcApply baseTC f p)      
      resolve <$> traverseResolveUTerm (V.fromList c)
    UTF utf -> second TCF <$> traverseResolveUTerm utf
    UOuterVar _ i -> do
      tc <- gets urOuterContext              
      return (tc, TCVar i)
    UOuterLet i   -> do
      tc <- gets urOuterContext
      return (tc, TCLocalDef i)

-- | Typecheck pats against given expected type.
typecheckPats :: TermContext s
              -> [Un.Pat]
              -> TCTerm
              -> TC s ([TCPat], TermContext s)
typecheckPats _ [] _ = fail "Unexpected attempt to typecheck empty list of pats"
typecheckPats tc upl@(up:_) tp = do
  rtp <- reduce tc tp
  r <- runUnifier tc (pos up) $ do
    utp <- mkUnifyTerm (emptyLocalCtx tc) rtp
    (pl,utpl) <- unzip <$> traverse indexUnPat upl
    traverse_ (usetEqual utp) utpl
    resolve $ traverse resolvePat pl
  case r of
    Left msg -> tcFail (pos up) msg
    Right rv -> return rv

-- | Typecheck pats against the given pi type.
typecheckPiPats :: TermContext s
                -> [Un.Pat]
                -> TCTerm
                -> TC s (([TCPat], TCTerm), TermContext s)
typecheckPiPats tc [] tp = fail "Unexpected attempt to unify empty list of pi pats"
typecheckPiPats tc pats@(up:_) tp = do
  tp' <- reduce tc tp
  r <- runUnifier tc (pos up) $ do
      (pl,utp') <- indexPiPats pats tp'
      resolve $ do
        pl' <- traverse resolvePat pl
        fmap (pl',) $ resolveCurrent =<< resolveUTerm utp'
  case r of
    Left msg -> tcFail (pos up) msg
    Right rv -> return rv
  

tcEqns :: TermContext s -> [UnDefEqn] -> TCTerm -> TC s [TCDefEqn]
tcEqns tc ueqs tp = traverse (\eq -> tcEqn tc eq tp) ueqs

-- | Typecheck equation is returns a term with the given type.
tcEqn :: TermContext s -> UnDefEqn -> TCTerm -> TC s TCDefEqn
tcEqn tc (DefEqnGen [] unrhs) tp = DefEqnGen [] <$> tcTerm tc unrhs tp
tcEqn tc (DefEqnGen unpats unrhs) tp = do
  ((pats,rhsTp), tc') <- typecheckPiPats tc unpats tp
  DefEqnGen pats <$> tcTerm tc' unrhs rhsTp

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

reduce :: TermContext s -> TCTerm -> TC s TCTerm
reduce tc t =
  case tcAsApp t of
    (TCF (URecordSelector r f), a) -> do
      r' <- reduce tc r
      case r' of
        TCF (URecordValue m) ->
          case Map.lookup f m of
            Just v -> reduce tc (tcMkApp v a)
            Nothing -> fail "Missing record field in reduce"
        _ -> return t
    (TCLambda pat tp rhs, a0:al) -> do
      r <- tryMatchPat tc pat a0
      case r of
        Nothing -> return t
        Just (tc',sub,_) -> reduce tc (tcMkApp t' al)
          where t' = tcApply tc (tc',rhs) (tc,sub)
    (TCF (UGlobal g), al) -> do
        -- Get global equations.
        m <- tryEval (globalDefEqns g tc)
        case m of
          Nothing -> return t
          Just eqs -> procEqs eqs
      where procEqs [] = return t
            procEqs (DefEqnGen pats rhs:eql) = do
              m <- tryMatchPatList tc pats al
              case m of
                Nothing -> procEqs eql
                Just (tc', sub, rest) -> reduce tc (tcMkApp g' rest)
                  where g' = tcApply tc (tc',rhs) (tc,V.reverse sub)
    _ -> return t
 
-- | Check that term is equivalent to Sort i for some i.
checkIsSort :: TermContext s -> Pos -> TCTerm -> TC s Sort
checkIsSort tc p t0 = do
  t <- reduce tc t0
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
tcSpecificDataType expected tc ut = do
  (v,_) <- inferTypedValue tc ut
  rtp <- reduce tc v
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
              (tc1, args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              case cur of
                FPResult dtArgs -> pure $ TypedValue v tp'
                  where v = TCF (UCtorApp i (reverse (a:rargs)))
                        tp' = TCF (UDataType dt (fmapTCApply (tc1, dtArgs) (tc,args)))
                FPPi pat1 tp next -> pure $ PartialCtor dt i (a:rargs) pat' tp' next'
                  where pat' = tcPatApply tc (tc1,pat1) (tc,args)
                        tp' = tcApply tc (tc1,tp) (tc,args)
                        tc2 = extendPatContext tc1 pat1
                        next' = tcCtorTypeApply (tc2,next) (tc,args)
            mkRes (PartialDataType dt rargs pat tp cur) = do
              (tc1, args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua tp
              case cur of
                FPResult s -> pure $ TypedValue v (TCF (USort s))
                  where v = TCF (UDataType dt (reverse (a:rargs)))
                FPPi pat1 tp next -> pure $ PartialDataType dt (a:rargs) pat' tp' next'
                  where pat' = tcPatApply tc (tc1,pat1) (tc, args)
                        tp' = tcApply tc (tc1,tp) (tc, args)
                        tc2 = extendPatContext tc1 pat1
                        next' = tcDTTypeApply (tc2,next) (tc,args)
            mkRes (TypedValue v tp0) = do
              (pat,patTp,tp) <- reduceToPiExpr tc (pos uf) tp0
              (tc1, args, a) <- matchPat tc (pos ua) pat =<< tcTerm tc ua patTp
              return $ TypedValue (TCF (UApp v a)) (tcApply tc (tc1,tp) (tc, args))

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
      (rhs,rhsTp) <- inferTypedValue tc' urhs
      return $ TypedValue (TCLet lcls rhs) (TCLet lcls rhsTp)
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
  where l = length lcls
        tcLclType (LocalFnDefGen nm utp ueqs) = do
          (tp,_) <- tcType tc0 utp
          r <- newRef nm
          let pendingFn tc = do
                let tp' = applyExt (tc0,tp) tc
                assign r (tcEqns tc ueqs tp')
          return (LocalFnDefGen nm tp r, pendingFn)

tcMkApp :: TCTerm -> [TCTerm] -> TCTerm
tcMkApp = go
  where go t [] = t
        go t (a:l) = go (TCF (UApp t a)) l

tcAsApp :: TCTerm -> (TCTerm, [TCTerm])
tcAsApp = go []
  where go r (TCF (UApp f v)) = go (v:r) f
        go r f = (f,r) 

-- | Check types in two terms are equal.
checkTypesEqual :: forall s . Pos -> CheckTypesCtx s
                -> TermContext s -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual p ctx tc x y = do
  xr <- reduce tc x
  yr <- reduce tc y
  checkTypesEqual' p ctx tc xr yr

type CheckTypesCtx s = [(TermContext s, TCTerm, TCTerm)]

evaluatedRefLocalDef :: [TCLocalDef] -> TC s [TCRefLocalDef s]
evaluatedRefLocalDef lcls = traverse go lcls
   where go (LocalFnDefGen nm tp eqns) = LocalFnDefGen nm tp <$> evaluatedRef nm eqns

type Subst = Vector TCTerm

type VarIndexMap s = Map Int (VarIndex s)

type VarSubst s = Vector (VarIndex s)

type MergeComputation s = StateT (VarIndexMap s, VarIndexMap s) (ErrorT String (Unifier s))

mergePats :: Pos
          -> TCPat
          -> TCPat
          -> Unifier s (Maybe (VarSubst s, VarSubst s))
mergePats p p10 p20 = do
    r <- runErrorT $ execStateT (go p10 p20) (Map.empty, Map.empty)
    return $
      case r of
        Left _ -> Nothing
        Right (m1,m2) -> Just (mfn m1, mfn m2)
          where mfn m = V.fromList (Map.elems m)
  where instPat :: TCPat -> StateT (VarIndexMap s) (Unifier s) (VarIndex s) 
        instPat (TCPVar nm j _) = StateT $ \m -> do
          r <- newRigidVar p nm
          v <- mkVar nm (URigidVar (fst r))
          return (v, Map.insert j v m)
        instPat TCPUnused = lift $ do
          tpv <- mkVar ("type of unused") (UFreeType "unused")
          mkVar "unused" (UUnused "unused" tpv)
        instPat (TCPatF pf) = lift . mkVar "unnamed" . UTF =<< mapM instPat (pfToTF pf)
          where pfToTF (UPTuple l) = UTupleValue l
                pfToTF (UPRecord m) = URecordValue m
                pfToTF (UPCtor c l) = UCtorApp c l
        go :: TCPat
           -> TCPat
           -> StateT (VarIndexMap s, VarIndexMap s) (ErrorT String (Unifier s)) ()
        go (TCPVar _ i _) p2 = do
          (m1,m2) <- get
          (v,m2') <- lift $ lift $ runStateT (instPat p2) m2
          put (Map.insert i v m1, m2')
        go p1 (TCPVar _ i _) = do
          (m1,m2) <- get
          (v,m1') <- lift $ lift $ runStateT (instPat p1) m1
          put (m1', Map.insert i v m2)
        go TCPUnused p2 = do
          (m1,m2) <- get
          m2' <- lift $ lift $ snd <$> runStateT (instPat p2) m2
          put (m1, m2')
        go p1 TCPUnused = do
          (m1,m2) <- get
          (v,m1') <- lift $ lift $ runStateT (instPat p1) m1
          put (m1', m2)
        go (TCPatF pf1) (TCPatF pf2) = do
          case (pf1, pf2) of
            (UPTuple l1, UPTuple l2)
              | length l1 == length l2 -> zipWithM_ go l1 l2
            (UPRecord m1, UPRecord m2)
              | Map.keys m1 == Map.keys m2 -> sequence_ (Map.intersectionWith go m1 m2)
            (UPCtor c1 l1, UPCtor c2 l2)
              | c1 == c2 && length l1 == length l2 -> zipWithM_ go l1 l2 
            _ -> lift $ throwError "Pattern merging failed"

instantiatePats :: Pos -> TermContext s -> TCPat -> TCPat
                -> TC s (Maybe (TermContext s, Subst, Subst))
instantiatePats p tc x y = do
  runUnifier tc p $ do
    mr <- mergePats p x y
    case mr of
      Nothing -> return Nothing 
      Just (xv,yv) -> do
        mr' <- resolve $ do
          xsv <- traverse resolveUTerm xv
          ysv <- traverse resolveUTerm yv
          tc <- gets urContext
          return (flip applyExt tc <$> xsv, flip applyExt tc <$> ysv)
        case mr' of
          Left _ -> return Nothing
          Right ((xs,ys),tc') -> return $ Just (tc', xs, ys)

-- | Check types applied to reduced terms.
checkTypesEqual' :: forall s . Pos -> CheckTypesCtx s
                 -> TermContext s -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual' p ctx tc x y = do
  let check' = checkTypesEqual p ((tc,x,y):ctx)
      checkAll :: Foldable t => t (TCTerm, TCTerm) -> TC s ()
      checkAll = mapM_ (uncurry (check' tc))
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
        check' tc xr yr
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
         check' tc xtp ytp *> checkAll (V.zip xv yv)

    ( (TCPi xp xtp xr, []), (TCPi yp ytp yr, []) ) -> do
       check' tc xtp ytp
       mr <- instantiatePats p tc xp yp 
       case mr of
         Nothing -> return ()
         Just (tc', xsub, ysub) -> do
           let xr' = tcApply tc (extendPatContext tc xp, xr) (tc', xsub)
           let yr' = tcApply tc (extendPatContext tc yp, yr) (tc', ysub)
           check' tc' xr' yr'
    ( (TCLet lcls xv, xa), _) -> do
       rlcls <- evaluatedRefLocalDef lcls
       let tc' = consLocalDefs rlcls tc
       let x' = tcMkApp xv (fmap (\t -> applyExt (tc,t) tc') xa)         
       check' tc' x' (applyExt (tc,y) tc')
    (_, (TCLet lcls yv, ya)) -> do
       rlcls <- evaluatedRefLocalDef lcls
       let tc' = consLocalDefs rlcls tc
       let y' = tcMkApp yv (fmap (\t -> applyExt (tc,t) tc') ya)         
       check' tc' (applyExt (tc,x) tc') y'

    ( (TCVar xi, xa), (TCVar yi, ya))
      | xi == yi && length xa == length ya ->
        checkAll (zip xa ya)

    ( (TCLocalDef xi, xa), (TCLocalDef yi, ya))
      | xi == yi && length xa == length ya ->
        checkAll (zip xa ya)

    _ -> do
       tcFail p $ show $ text "Equivalence check failed during typechecking:"  $$
          nest 2 (text $ show x) $$ text "and\n" $$
          nest 2 (text $ show y) $$ text "in context\n" $$
          nest 4 (ppTermContext tc) $$ 
          nest 2 (vcat (ppScope <$> ctx))
      where ppScope (tc',x',y') =
             text "while typechecking" $$
             nest 2 (text $ show x') $$ text "and\n" $$
             nest 2 (text $ show y') $$ text "in context\n" $$
             nest 4 (ppTermContext tc')

-- | @checkTypeSubtype tc p x y@ checks that @x@ is a subtype of @y@.
checkTypeSubtype :: forall s . TermContext s -> Pos -> TCTerm -> TCTerm -> TC s ()
checkTypeSubtype tc p x y = do
  xr <- reduce tc x
  yr <- reduce tc y
  let ppFailure = tcFail p (show msg)
        where msg = ppTCTerm tc xr <+> text "is not a subtype of" <+> ppTCTerm tc yr <> char '.'
  case (tcAsApp xr, tcAsApp yr) of
    ( (TCF (USort xs), []), (TCF (USort ys), []) )
      | xs <= ys -> return ()
      | otherwise -> ppFailure
    _ -> checkTypesEqual' p [] tc xr yr

unimpl :: String -> a
unimpl nm = error (nm ++ " unimplemented")

type MatchAttempt s = StateT (Map Int TCTerm) (ErrorT String (TC s))

-- | Attempt to match term against a pat, returns reduced term that matches.
attemptMatch :: TermContext s -> TCPat -> TCTerm -> MatchAttempt s TCTerm
attemptMatch _ (TCPVar _ i _) t = t <$ modify (Map.insert i t)
attemptMatch _ TCPUnused t = return t
attemptMatch tc (TCPatF pf) t = do
  let go = attemptMatch tc
  rt <- lift $ lift $ reduce tc t
  case (pf, rt) of
    (UPTuple pl, TCF (UTupleValue tl)) | length pl == length tl ->
      TCF . UTupleValue <$> sequenceA (zipWith go pl tl)
    (UPRecord pm, TCF (URecordValue tm)) | Map.keys pm == Map.keys tm ->
      TCF . URecordValue <$> sequenceA (Map.intersectionWith go pm tm)
    (UPCtor cp pl, TCF (UCtorApp ct tl)) | cp == ct ->
      TCF . UCtorApp ct <$> sequenceA (zipWith go pl tl)
    _ -> lift $ throwError "Pattern match failed."

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
tryMatchPat :: TermContext s
            -> TCPat -> TCTerm -> TC s (Maybe (TermContext s, Subst, TCTerm))
tryMatchPat tc pat t = do
    fmap finish $ runErrorT $ runStateT (attemptMatch tc pat t) Map.empty
  where finish Left{} = Nothing
        finish (Right (t,args)) = Just (tc', V.fromList (Map.elems args), t)
          where tc' = extendPatContext tc pat

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
tryMatchPatList :: TermContext s
                -> [TCPat]
                -> [TCTerm]
                -> TC s (Maybe ( TermContext s
                               , Subst
                               , [TCTerm]))
tryMatchPatList tc pats terms =
    fmap finish $ runErrorT $ runStateT (go pats terms) Map.empty
  where go (pat:pl) (term:tl) =
          attemptMatch tc pat term >> go pl tl
        go [] tl = return tl
        go _ [] = fail "Insufficient number of terms"
        finish Left{} = Nothing
        finish (Right (tl,args)) = Just (tc', V.fromList (Map.elems args), tl)
          where bindings = runPatVarParser (mapM_ addPatBindings pats)
                tc' = foldr (uncurry consBoundVar) tc bindings

-- | Match untyped term against pattern, returning variables in reverse order.
-- so that last-bound variable is first.  Also returns the term after it was matched.
-- This may differ to the input term due to the use of reduction during matching.
matchPat :: forall s
          . TermContext s
         -> Pos -> TCPat -> TCTerm -> TC s (TermContext s, Vector TCTerm, TCTerm)
matchPat tc p pat t = do
  mr <- tryMatchPat tc pat t
  case mr of
    Nothing -> tcFail p $ "Pattern match failed."
    Just r -> return r

-- | Attempt to reduce a term to a  pi expression, returning the pattern, type
-- of the pattern and the right-hand side.
-- Reports error if htis fails.
reduceToPiExpr :: TermContext s -> Pos -> TCTerm -> TC s (TCPat, TCTerm, TCTerm)
reduceToPiExpr tc p tp = do
  rtp <- reduce tc tp
  case rtp of
    TCPi pat l r -> return (pat,l,r)
    _ -> tctFail p $ text "Unexpected argument to term with type:" $$
                         nest 2 (ppTCTerm tc rtp)

reduceToRecordType :: TermContext s -> Pos -> TCTerm -> TC s (Map FieldName TCTerm)
reduceToRecordType tc p tp = do
  rtp <- reduce tc tp
  case rtp of
    TCF (URecordType m) -> return m
    _ -> tctFail p $ text "Attempt to dereference field of term with type:" $$ 
                       nest 2 (ppTCTerm tc rtp)

{-
      (tc',dl) <- consLocalDecls tc udl
      rhs <- inferTerm tc' urhs
      return $ ULet dl rhs
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

data CompletionContext
  = CCGlobal Module
  | CCBinding CompletionContext Term

ccModule :: CompletionContext -> Module
ccModule (CCGlobal m) = m
ccModule (CCBinding cc _) = ccModule cc

addPatTypes :: CompletionContext -> [(String,TCTerm)] -> (CompletionContext, [Term])
addPatTypes cc0 vars = mapAccumL ins cc0 vars
  where ins cc (_,tp) = (CCBinding cc tp', tp')
          where tp' = completeTerm cc tp

ccVarType :: CompletionContext -> DeBruijnIndex -> Term
ccVarType cc0 i = go i cc0
  where go i (CCBinding cc t)
          | i == 0 = incVars 0 (i+1) t
          | otherwise = go (i-1) cc
        go _ CCGlobal{} = error "Could not find var with index in context."

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
completeDefEqn cc (DefEqnGen pats rhs) = eqn
  where m = ccModule cc
        bindings = runPatVarParser (mapM_ addPatBindings pats)
        (cc', v) = second V.fromList $ addPatTypes cc bindings
        eqn = DefEqn (completePat' m v <$> pats) (completeTerm cc' rhs)

completePat :: CompletionContext -> TCPat -> (Pat Term, CompletionContext)
completePat cc0 pat = (completePat' (ccModule cc0) v pat, cc')
  where (cc', v) = second V.fromList $ addPatTypes cc0 (patBoundVars pat)

completePat' :: Module -> Vector Term -> TCPat -> Pat Term
completePat' m v = go
  where go (TCPVar nm i _) = PVar nm i (v V.! i)
        go TCPUnused = PUnused
        go (TCPatF pf) =
          case pf of
            UPTuple l -> PTuple (go <$> l)
            UPRecord m -> PRecord (go <$> m)
            UPCtor i l -> PCtor c (go <$> l)
              where Just c = findCtor m i

addBoundVars :: [(String,TCTerm)] -> CompletionContext -> CompletionContext
addBoundVars _ _ = unimpl "addBoundVars"

localBoundVars :: TCLocalDef -> (String, TCTerm)
localBoundVars (LocalFnDefGen nm tp _) = (nm,tp)

completePatBoundVars :: TCPat -> CompletionContext -> CompletionContext
completePatBoundVars _ _ = unimpl "completePatBoundVars"

completeLocalVars :: [(String, TCTerm)] -> CompletionContext -> CompletionContext
completeLocalVars _ _ = unimpl "completeLocalVars"

-- | Returns the type of a unification term in the current context.
completeTerm :: CompletionContext -> TCTerm -> Term
completeTerm cc (TCF tf) =
  case tf of
    UGlobal i -> Term (GlobalDef d)
      where Just d = findDef m i
    UApp l r -> Term $ App (go l) (go r)
    UTupleValue l -> Term $ TupleValue (go <$> l)
    UTupleType l -> Term $ TupleType (go <$> l)
    URecordValue m      -> Term $ RecordValue (go <$> m)
    URecordSelector t f -> Term $ RecordSelector (go t) f
    URecordType m       -> Term $ RecordType (go <$> m)
    UCtorApp i l        -> Term $ CtorValue c (go <$> l)
      where Just c = findCtor m i
    UDataType i l       -> Term $ CtorType dt (go <$> l)
      where Just dt = findDataType m i
    USort s             -> Term $ Sort s
    UNatLit i           -> Term $ IntLit i
    UArray tp v         -> Term $ ArrayValue (go tp) (go <$> v)
 where m = ccModule cc
       go = completeTerm cc
completeTerm cc (TCLambda pat tp r) = Term $
    Lambda pat' (completeTerm cc tp) (completeTerm cc' r)
  where (pat', cc') = completePat cc pat
completeTerm cc (TCPi pat tp r) = Term $
    Pi pat' (completeTerm cc tp) (completeTerm cc' r)
  where (pat', cc') = completePat cc pat
completeTerm cc (TCLet lcls t) = Term $ Let lcls' (completeTerm cc' t)
  where (cc',tps) = addPatTypes cc (localBoundVars <$> lcls)
        completeLocal (LocalFnDefGen nm _ eqns) tp =
          LocalFnDef nm tp (completeDefEqn cc' <$> eqns)
        lcls' = zipWith completeLocal lcls tps
completeTerm cc (TCVar i) = Term $ LocalVar i (ccVarType cc i)
completeTerm cc (TCLocalDef i) = Term $ LocalVar i (ccVarType cc i)

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
          where cc = CCGlobal m
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
          tcEqns tc ueqs tp
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