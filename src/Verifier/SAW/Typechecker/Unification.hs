{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Typechecker.Unification
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Typechecker.Unification
  ( hasDups
  , typecheckPat
  , typecheckPats
  , typecheckPiPats
  , checkTypesEqual
  , checkTypesEqual'
  , instPats
  ) where

import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Lens
import Control.Monad (ap, unless, zipWithM, zipWithM_)
import Control.Monad.Trans.Except (ExceptT(..), runExceptT, throwE)
import Control.Monad.State (StateT(..), MonadState(..), evalStateT, gets)
import Control.Monad.Trans
import Control.Monad.ST
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.STRef
import Data.Vector (Vector)
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Position
import Verifier.SAW.Typechecker.Context
import Verifier.SAW.Typechecker.Monad
import Verifier.SAW.Typechecker.Simplification
import Verifier.SAW.TypedAST (ppParens, zipWithFlatTermF, ppFlatTermF, defaultPPOpts, Prec(..))
import Verifier.SAW.Prelude.Constants
import qualified Verifier.SAW.UntypedAST as Un

-- | Return true if set has duplicates.
hasDups :: Ord a => [a] -> Bool
hasDups l = Set.size (Set.fromList l) < length l

lift2 :: (a -> b) -> (b -> b -> c) -> a -> a -> c
lift2 f h x y = h (f x) (f y)

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

data VarIndex s = VarIndex { viIndex :: !Int
                           , viName :: String
                           , viRef :: STRef s (UVarState s)
                           }

instance Eq (VarIndex s) where
  (==) = lift2 viIndex (==)

instance Ord (VarIndex s) where
  compare = lift2 viIndex compare

data UVarState s
    -- | Indicates this var is equivalent to another.
  = UVar (VarIndex s)
  | URigidVar (RigidVarRef s) -- ^ Rigid variable that cannot be instantiated.
    -- | A unused pattern variable, and it's type.
  | UUnused String (VarIndex s)
    -- | A free type variable with the name of the variable it is type for.
  | UFreeType String
    -- | A higher order term that is not parsed during unification, possibly with
    -- some of the free variables substituted by indices.
    -- The term may be assumed to be a type expression, and the variables are arguments
    -- to instantiate it.
  | UHolTerm (TermContext s, TCTerm) -- Type with free variables.
             [VarIndex s] -- Variables bound to type.
  | UTF (FlatTermF (VarIndex s))
    -- A variable bound outside the context of the unification problem with name and type
    -- relative to when before unification began.
  | UApp (VarIndex s) (VarIndex s)
  | UOuterVar String Int

ppUTerm :: UVarState s -> TC s Doc
ppUTerm vs0 = evalStateT (go PrecNone vs0) Set.empty
  where goVar :: Prec -> VarIndex s -> StateT (Set (VarIndex s)) (TC s) Doc
        goVar pr v = do
          s <- get
          if Set.member v s then
            return $ text (viName v)
          else do
            put (Set.insert v s)
            go pr =<< lift (liftST (readSTRef (viRef v)))
        go :: Prec -> UVarState s -> StateT (Set (VarIndex s)) (TC s) Doc
        go pr (UVar v) = goVar pr v
        go _ (URigidVar r) = pure $ text $ 'r' : rvrName r
        go _ (UUnused nm _) = pure $ text $ "un" ++ nm
        go _ (UFreeType nm) = pure (text $ "typeOf(" ++ nm ++ ")")
        go pr (UHolTerm (tc,t) []) = pure $ ppTCTerm tc pr t
        go pr (UHolTerm (tc,t) bindings) = ppParens (pr > PrecApp) .
          hsep . (ppTCTerm tc PrecApp t :) <$> traverse (goVar PrecArg) bindings
        go pr (UTF tf) = ppFlatTermF defaultPPOpts goVar pr tf
        go pr (UApp l r) = ppParens (pr > PrecApp) <$> liftA2 (<+>) (goVar PrecApp l) (goVar PrecArg r)
        go _ (UOuterVar nm _) = pure $ text $ "outerv" ++ nm

data UPat s
  = UPVar (VarIndex s)
  | UPUnused (VarIndex s) String (VarIndex s)
  | UPatF Un.Pos (PatF (UPat s))

data UnifierState s =
  US { usGlobalContext :: TermContext s
       -- Position where unification began.
     , usPos :: Pos
     , _usVarCount :: Int
     , _usRigidCount :: Int
     }

usVarCount :: Simple Lens (UnifierState s) Int
usVarCount = lens _usVarCount (\s c -> s { _usVarCount = c })

usRigidCount :: Simple Lens (UnifierState s) Int
usRigidCount = lens _usRigidCount (\s c -> s { _usRigidCount = c })

type Unifier s = StateT (UnifierState s) (TC s)

runUnifier :: TermContext s -> Pos -> Unifier s v -> TC s v
runUnifier uc p m = evalStateT m s0
  where s0 = US { usGlobalContext = uc
                , usPos = p
                , _usVarCount = 0
                , _usRigidCount = 0
                }


mkVar :: String -> UVarState s -> Unifier s (VarIndex s)
mkVar nm vs = do
  vr <- lift $ liftST $ newSTRef vs
  vidx <- use usVarCount
  usVarCount += 1
  return VarIndex { viIndex  = vidx
                  , viName = nm
                  , viRef = vr
                  }

mkFreeTypeVar :: String -> Unifier s (VarIndex s)
mkFreeTypeVar nm = mkVar ("type of " ++ show nm) (UFreeType nm)

newRigidVar :: Un.Pos -> String -> Unifier s (RigidVarRef s, VarIndex s)
newRigidVar p nm = do
  tp <- mkFreeTypeVar nm
  idx <- use usRigidCount
  usRigidCount += 1
  let rv = RigidVarRef { rvrIndex = idx
                       , rvrPos = p
                       , rvrName = nm
                       , rvrType = tp
                       }
  return (rv,tp)

unFail :: Pos -> Doc -> Unifier s a
unFail p msg = lift (tcFail p (show msg))

usetEqual :: VarIndex s -> VarIndex s -> Unifier s ()
usetEqual vx vy | viRef vx == viRef vy = pure ()
usetEqual vx vy = do
  p <- gets usPos
  x <- lift $ liftST $ readSTRef (viRef vx)
  y <- lift $ liftST $ readSTRef (viRef vy)
  case (x,y) of
    (UVar vz,_) -> usetEqual vz vy
    (_,UVar vz) -> usetEqual vx vz
    (URigidVar rx, URigidVar ry)
      | rx == ry -> pure ()
      | otherwise -> unFail p (text "Ununifiable rigid vars")
    (UTF ufx, UTF ufy)
      | Just ufz <- zipWithFlatTermF usetEqual ufx ufy -> sequenceOf_ folded ufz
    (UApp ufx1 ufx2, UApp ufy1 ufy2) -> do
      usetEqual ufx1 ufy1
      usetEqual ufx2 ufy2
    (UFreeType{}, _) -> lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    (_, UFreeType{}) -> lift $ liftST $ writeSTRef (viRef vy) (UVar vx)
    -- We only merge unused with counterparts that are not free types.
    (UUnused{}, _) -> lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    (_, UUnused{}) -> lift $ liftST $ writeSTRef (viRef vy) (UVar vx)

    -- We have very limited support for dealing with higher-order types.
    -- They must match exactly.
    (UHolTerm (tc1,t1) c1, UHolTerm (tc2,t2) c2) | length c1 == length c2 -> do
      -- Check that txf and tyf are equivalent
      tc <- gets usGlobalContext
      let t1' = boundFreeVarsWithPi (tc1,t1) tc
          t2' = boundFreeVarsWithPi (tc2,t2) tc
      lift $ checkTypesEqual p [] tc t1' t2'
      -- Unify corresponding entries in cx and cy.
      zipWithM_ usetEqual c1 c2
      -- Set vx to point to vy.
      lift $ liftST $ writeSTRef (viRef vx) (UVar vy)
    (UOuterVar _ xi, UOuterVar _ yi) | xi == yi -> pure ()
    _ -> do
      xd <- lift $ ppUTerm x
      yd <- lift $ ppUTerm y
      unFail p $ vcat [ text "Do not support unifying types:"
                      , text "Type 1"
                      , nest 2 xd
                      , text "Type 2"
                      , nest 2 yd
                      ]

upatToTerm :: UPat s -> Unifier s (VarIndex s)
upatToTerm (UPVar v) = pure v -- mkVar (rvrName r) (URigidVar r)
upatToTerm (UPUnused v _ _) = pure v
upatToTerm (UPatF _ pf) =
  mkVar "patf" . UTF . termFromPatF =<< traverse upatToTerm pf

-- | Create a upat from a untyped pat, and return its type.
indexUnPat :: Un.Pat -> Unifier s (UPat s, VarIndex s)
indexUnPat upat =
  case upat of
    Un.PSimple (Un.PVar (PosPair p nm)) -> do
      (rvr,tpv) <- newRigidVar p nm
      v <- mkVar nm (URigidVar rvr)
      return (UPVar v,tpv)
    Un.PSimple (Un.PUnused (PosPair _ nm)) -> do
      tpv <- mkVar ("type of " ++ nm) (UFreeType nm)
      (\v -> (UPUnused v nm tpv, tpv)) <$> mkVar nm (UUnused nm tpv)
    Un.PUnit p -> do
        tpv <- mkVar (show (Un.ppPat PrecNone upat)) (UTF UnitType)
        return (UPatF p UPUnit, tpv)
    Un.PPair p x y -> do
        (xp, xtp) <- indexUnPat x
        (yp, ytp) <- indexUnPat y
        tpv <- mkVar (show (Un.ppPat PrecNone upat)) (UTF (PairType xtp ytp))
        return (UPatF p (UPPair xp yp), tpv)
    Un.PEmpty p -> do
        tpv <- mkVar (show (Un.ppPat PrecNone upat)) (UTF EmptyType)
        return (UPatF p UPEmpty, tpv)
    Un.PField (x, y) z -> do
        (xp, xtp) <- indexUnPat x
        (yp, ytp) <- indexUnPat y
        (zp, ztp) <- indexUnPat z
        tpv <- mkVar (show (Un.ppPat PrecNone upat)) (UTF (FieldType xtp ytp ztp))
        return (UPatF (pos z) (UPField xp yp zp), tpv)
{-
    Un.PRecord p fpl
        | hasDups (val . fst <$> fpl) ->
           unFail p $ text "Duplicate field names in pattern."
        | otherwise -> do
           rm <- traverse indexUnPat (Map.fromList (first val <$> fpl))
           tpv <- mkVar (show (Un.ppPat PrecNone upat))
                        (UTF $ RecordType (fmap snd rm))
           return (UPatF p (UPRecord (fmap fst rm)), tpv)
-}
    Un.PCtor pnm pl -> do
      tc <- gets usGlobalContext
      (c,tp) <- lift $ resolveCtor (globalContext tc) pnm (length pl)
      let vfn upl = UPatF (pos pnm) (UPCtor c upl)
      first vfn <$> indexPiPats pl tp
    Un.PString p s -> do
      tpv <- mkVar (show (Un.ppPat PrecNone upat)) (UTF preludeStringType)
      return (UPatF p (UPString s), tpv)

-- | Variable, the type, and name, and type.
type LocalCtxBinding s = (VarIndex s, VarIndex s, String, TCTerm)

-- | Context during unification.
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

extendLocalCtx1 :: LocalCtxBinding s -> UnifyLocalCtx s -> Unifier s (UnifyLocalCtx s)
extendLocalCtx1 b@(_,vtp,nm,tp) ulc = do
  usetEqual vtp =<< mkUnifyTerm ulc tp
  return UnifyLocalCtx { ulcTC = consBoundVar nm tp (ulcTC ulc)
                       , ulcBindings = b : ulcBindings ulc
                       }

extendLocalCtx :: [LocalCtxBinding s] -> UnifyLocalCtx s -> Unifier s (UnifyLocalCtx s)
extendLocalCtx l ulc = foldlMOf folded (flip extendLocalCtx1) ulc l

-- | Create a unify term from a term.
mkUnifyTerm :: UnifyLocalCtx s
            -> TCTerm
            -> Unifier s (VarIndex s)
mkUnifyTerm l t =
    case t of
      TCF tf -> mkTermVar . UTF =<< traverse (mkUnifyTerm l) tf
      TCApp x y -> mkTermVar =<< (UApp <$> mkUnifyTerm l x <*> mkUnifyTerm l y)
      TCLambda{} -> holTerm
      TCPi{} -> holTerm
      TCVar i -> do
          case lookupLocalCtxVar l i of
            Just v -> return v
            Nothing -> mkTermVar (UOuterVar nm (i - localCtxSize l))
        where BoundVar nm = resolveBoundInfo i (ulcTC l)
  where holTerm = mkTermVar (mkHolTerm l t)
        mkTermVar = mkVar "intermediate term"

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
        go (TCPVar nm (i, tp)) unpat = StateT $ \m -> do
             (up,utp) <- indexUnPat unpat
             u <- upatToTerm up
             return (up, Map.insert i (u,utp,nm,tp) m)
        go TCPUnused{} unpat = StateT $ \m ->
           second (const m) <$> indexUnPat unpat
        go (TCPatF pf) unpat =
          case (pf, unpat) of
            (UPUnit, Un.PUnit p) -> return $ UPatF p UPUnit
            (UPPair px py, Un.PPair p upx upy) ->
                 UPatF p <$> (UPPair <$> go px upx <*> go py upy)
            (UPEmpty, Un.PEmpty p) -> return $ UPatF p UPEmpty
            (UPField f px py, Un.PField (f', upx) upy) ->
                 UPatF (pos f') <$> (UPField <$> go f f' <*> go px upx <*> go py upy)
            (UPCtor c pl, Un.PCtor pnm upl) -> do
              tc <- lift $ gets usGlobalContext
              (c',_) <- lift $ lift $ resolveCtor (globalContext tc) pnm (length upl)
              unless (c == c') (err (pos pnm))
              UPatF (pos pnm) . UPCtor c <$> zipWithM go pl upl
            _ -> err (pos unpat)

indexPiPats :: [Un.Pat] -> TCTerm -> Unifier s ([UPat s], VarIndex s)
indexPiPats unpats0 tp0 = do
    tc <- gets usGlobalContext
    go [] unpats0 (emptyLocalCtx tc, tp0)
  where go :: -- Previous patterns
              [UPat s]
              -- Terms for substution.
           -> [Un.Pat]
           -> (UnifyLocalCtx s, TCTerm) -> Unifier s ([UPat s], VarIndex s)
        go ppats [] (lctx, tp) =
          (reverse ppats,) <$> mkUnifyTerm lctx tp
        go ppats (unpat:upl) (lctx,tp) = do
          (p,_,r) <- lift $ reduceToPiExpr (ulcTC lctx) (pos unpat) tp
          (up,lctx') <- matchUnPat lctx p unpat
          go (up:ppats) upl (lctx', r)

data URRes v = URSeen v
             | URActive

type UResolverCache k v = Map k (URRes v)

data UnifyResult s
   = UR { -- | Context when unification began
          urOuterContext :: TermContext s
          -- Current context
        , _urContext  :: TermContext s
        , _urBoundMap :: UResolverCache (VarIndex s) (TermContext s, TCTerm)
        -- | Cache that maps variables to their typechecked value at the
        -- given deBruijnIndex.
        , _urVarMap   :: UResolverCache (VarIndex s) (TermContext s, TCTerm)
        }

urContext :: Simple Lens (UnifyResult s) (TermContext s)
urContext = lens _urContext (\s c -> s { _urContext = c })

urBoundMap :: Simple Lens (UnifyResult s) (UResolverCache (VarIndex s) (TermContext s, TCTerm))
urBoundMap = lens _urBoundMap (\s v -> s { _urBoundMap = v })

urVarMap :: Simple Lens (UnifyResult s) (UResolverCache (VarIndex s) (TermContext s, TCTerm))
urVarMap = lens _urVarMap (\s v -> s { _urVarMap = v })

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

-- | Get results of unification or message indicating why unification failed."
resolve :: UResolver s a -> Unifier s (Either String (a, TermContext s))
resolve (URR m) = do
  us <- get
  lift $ do
    let ur0 = UR { urOuterContext = usGlobalContext us
                 , _urContext  = usGlobalContext us
                 , _urBoundMap = Map.empty
                 , _urVarMap   = Map.empty
                 }
    right (second _urContext) <$> liftST (m ur0)

urST :: ST s v -> UResolver s v
urST m = URR $ \r -> Right . (,r) <$> m

readVarState :: VarIndex s -> UResolver s (UVarState s)
readVarState v = urST $ readSTRef (viRef v)

occursCheckFailure :: Monad m => String -> m a
occursCheckFailure nm = fail msg
  where msg = "Cyclic dependency detected during unification of " ++ nm

-- | Function for getting value from cache once.
uresolveCache :: (Ord k, MonadState s m)
              => Simple Lens s (UResolverCache k v) -- ^ Lens for accessing cache in state.
              -> (k -> m v) -- ^ Evaluation function for getting value if key is empty.
              -> String -- ^ Name if occurs check failure occurs.
              -> k -- ^ Value to lookup.
              -> m v
uresolveCache clens evalFn nm k = do
  m0 <- use clens
  case Map.lookup k m0 of
    Just (URSeen r) -> return r
    Just URActive -> occursCheckFailure nm
    Nothing -> do
      clens . at k ?= URActive
      r <- evalFn k
      clens . at k ?= URSeen r
      return r

-- | Resolve variable that should be bound to a new pattern variable.
-- Returns context just before variable was added, and type of variable (which is relative
-- to the returned context.)
uresolveBoundVar :: String -- ^ Name of variable.
                 -> VarIndex s -- ^ Variable for value.
                 -> VarIndex s -- ^ Variable for type.
                 -> UResolver s (TermContext s, TCTerm)
uresolveBoundVar nm v vtp = do
  uresolveCache urBoundMap (uresolveBoundVar' nm vtp) nm v

-- | Resolve bound var name and type, and add bound var to current context.
uresolveBoundVar' :: String -> VarIndex s -> VarIndex s -> UResolver s (TermContext s, TCTerm)
uresolveBoundVar' nm vtp _ = do
  tpp <- resolveUTerm vtp
  tc <- use urContext
  let tp = applyExt tc tpp
  urContext .= consBoundVar nm tp tc
  return (tc,tp)

-- | Convert a TCTerm at a given level to be valid at the current level.
resolveCurrent :: (TermContext s, TCTerm) -> UResolver s TCTerm
resolveCurrent p = mk <$> use urContext
  where mk tc = applyExt tc p

-- | Resolve a unifier pat to a tcpat.
resolvePat :: UPat s -> UResolver s TCPat
resolvePat (UPVar v) = do
  s <- readVarState v
  case s of
    URigidVar rvr -> do
      tc0 <- gets urOuterContext
      (tc,tp) <- uresolveBoundVar (rvrName rvr) v (rvrType rvr)
      let Just d = tc `boundVarDiff` tc0
      return $ TCPVar (rvrName rvr) (d, tp)
    _ -> error "Rigid var ref has been replaced."
resolvePat (UPUnused v nm vtp) = do
  s <- readVarState v
  case s of
    UUnused _ _ -> do
      (tc,tp) <- uresolveBoundVar nm v vtp
      tc0 <- gets urOuterContext
      let Just d = tc `boundVarDiff` tc0
      return $ TCPVar nm (d,tp)
    _ -> do
      (tc,tp) <- resolveUTerm vtp
      tc0 <- gets urOuterContext
      let Just d = tc `boundVarDiff` tc0
      return $ TCPUnused nm (d,tp)

resolvePat (UPatF _ pf) = TCPatF <$> traverse resolvePat pf

traverseResolveUTerm :: Traversable t
                     => t (VarIndex s)
                     -> UResolver s (TermContext s, t TCTerm)
traverseResolveUTerm tv = do
  ttf <- traverse resolveUTerm tv
  tc <- use urContext
  let Just r = traverse (applyExtSafe tc) ttf
  return (tc, r)

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm :: VarIndex s -> UResolver s (TermContext s, TCTerm)
resolveUTerm v = uresolveCache urVarMap resolveUTerm' (viName v) v

-- | Returns the TCTerm for the given var with vars relative to returned deBruijn level.
resolveUTerm' :: forall s . VarIndex s -> UResolver s (TermContext s, TCTerm)
resolveUTerm' v = do
  -- Returns a refernce to a pattern variable with the given name, index, and type.
  let mkPatVarRef :: String -> VarIndex s -> VarIndex s -> UResolver s (TermContext s, TCTerm)
      mkPatVarRef nm ivar tpv = fn <$> uresolveBoundVar nm ivar tpv
        where fn (tc,tp) = (consBoundVar nm tp tc, TCVar 0)
  uvs <- urST $ readSTRef (viRef v)
  case uvs of
    URigidVar r -> mkPatVarRef (rvrName r) v (rvrType r)
    UVar v' -> resolveUTerm v'
    UUnused nm tpv -> mkPatVarRef nm v tpv
    UFreeType _ -> fail "Free type variable unbound during unification"
    UHolTerm f c -> do
      baseTC <- gets urOuterContext
      let finish p@(tc,_) = (tc, tcApply baseTC f p)
      finish <$> traverseResolveUTerm (V.fromList c)
    UTF utf -> second TCF <$> traverseResolveUTerm utf
    UApp l r -> do
      x <- resolveUTerm l
      y <- resolveUTerm r
      tc <- use urContext
      let Just a = applyExtSafe tc x
      let Just b = applyExtSafe tc y
      return (tc, TCApp a b)
    UOuterVar _ i -> do
      tc <- gets urOuterContext
      return (tc, TCVar i)

-- | Typecheck pat against given expected type.
typecheckPat :: TermContext s
             -> Un.Pat
             -> TCTerm
             -> TC s (TCPat, TermContext s)
typecheckPat tc up tp = do
  rtp <- reduce tc tp
  r <- runUnifier tc (pos up) $ do
    utp <- mkUnifyTerm (emptyLocalCtx tc) rtp
    (p,uptp) <- indexUnPat up
    usetEqual utp uptp
    resolve $ resolvePat p
  case r of
    Left msg -> tcFail (pos up) msg
    Right rv -> return rv


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
    traverseOf_ folded (usetEqual utp) utpl
    resolve $ traverse resolvePat pl
  case r of
    Left msg -> tcFail (pos up) msg
    Right rv -> return rv

-- | Typecheck pats against the given pi type.
typecheckPiPats :: TermContext s
                -> Pos
                -> [Un.Pat]
                -> TCTerm
                -> TC s (([TCPat], TCTerm), TermContext s)
typecheckPiPats tc p pats tp = do
  tp' <- reduce tc tp
  r <- runUnifier tc p $ do
      (pl,utp') <- indexPiPats pats tp'
      resolve $ do
        pl' <- traverse resolvePat pl
        unless (isJust (checkTCPatOf (termBoundCount tc) traverse pl')) $
          fail "typecheckPiPats failed"
        fmap (pl',) $ resolveCurrent =<< resolveUTerm utp'
  case r of
    Left msg -> tcFail p msg
    Right rv -> return rv

-- | Pattern where each variable is annotated with var for value and type.
type UnifyPat s = AnnPat (VarIndex s,VarIndex s)

-- | Convert a typechecked pat into something usable in unification.
convertPat :: TCPat -> Unifier s (UnifyPat s)
convertPat p0 = do
  let vterms = patBoundVars p0
  let fn :: (String,TCTerm)
         -> StateT (UnifyLocalCtx s) (Unifier s) (UnifyLocalCtx s, (VarIndex s, VarIndex s))
      fn (nm,tp) = do
        ulc <- get
        tpv <- lift $ mkUnifyTerm ulc tp
        v <- lift $ mkVar nm (UUnused nm tpv)
        ulc' <- lift $ extendLocalCtx1 (v, tpv, nm, tp) ulc
        put ulc'
        return (ulc', (v,tpv))
  tc0 <- gets usGlobalContext
  (resv,ulc') <- runStateT (traverse fn vterms) (emptyLocalCtx tc0)
  let ulcv = fmap fst resv `V.snoc` ulc'
  let vars = fmap snd resv
  -- Remap vars in pat to new vars.
  let remapPat (TCPVar nm (i,_)) = pure $ TCPVar nm (i, vars V.! i)
      remapPat (TCPUnused nm (i,tp)) = do
        let Just ulc = ulcv V.!? i
        tpv <- mkUnifyTerm ulc tp
        v <- mkVar nm (UUnused nm tpv)
        pure $ TCPUnused nm (i, (v,tpv))
      remapPat (TCPatF pf) = TCPatF <$> traverse remapPat pf
  remapPat p0

-- | Return term representing pat and storing vars in map.
instUnifyPat :: UnifyPat s -> Unifier s (VarIndex s)
instUnifyPat (TCPVar    _ (_, (v,_))) = pure v
instUnifyPat (TCPUnused _ (_, (v,_))) = pure v
instUnifyPat (TCPatF pf) =
  mkVar "patf" . UTF . termFromPatF =<< traverse instUnifyPat pf

-- | Attempt to unify two pats, updating state to map variables to term they are bound to.
mergeUnifyPats :: UnifyPat s
               -> UnifyPat s
               -> ExceptT String (Unifier s) ()
mergeUnifyPats (TCPVar _ (_, (v,_))) p2 = do
  lift $ usetEqual v =<< instUnifyPat p2
mergeUnifyPats p1 (TCPVar _ (_, (v,_))) = do
  lift $ flip usetEqual v =<< instUnifyPat p1
mergeUnifyPats (TCPUnused _ (_, (v,_))) p2 = do
  lift $ usetEqual v =<< instUnifyPat p2
mergeUnifyPats p1 (TCPUnused _ (_, (v,_))) = do
  lift $ flip usetEqual v =<< instUnifyPat p1
mergeUnifyPats (TCPatF pf1) (TCPatF pf2) = do
  case zipWithPatF mergeUnifyPats pf1 pf2 of
    Just pf -> sequenceOf_ folded pf
    Nothing -> throwE "Pattern merging failed"

instPats :: Pos
          -> TermContext s
          -> TCTerm
          -> (TCPat,TCTerm)
          -> (TCPat,TCTerm)
          -> TC s (Maybe (TermContext s, TCTerm, TCTerm))
instPats p tc _tp (xp,xr) (yp,yr) = do
  runUnifier tc p $ do
    xp' <- convertPat xp
    yp' <- convertPat yp
    mr <- runExceptT $ mergeUnifyPats xp' yp'
    case mr of
      Left{} -> return Nothing
      Right{} -> do
        let mkSub :: UnifyPat s -> UResolver s (Vector (TermContext s, TCTerm))
            mkSub = traverse (resolveUTerm . typeOfBoundVar) . patBoundVars
              where typeOfBoundVar = fst . snd
        mr' <- resolve $ both mkSub (xp',yp')
        case mr' of
          Left{} -> return Nothing
          Right ((xs,ys),tc') -> do
            let getRes pat r sub = tcApply tc (extendPatContext tc pat, r) (tc', sub')
                  where Just sub' = traverse (applyExtSafe tc') sub
            return $ Just ( tc'
                          , getRes xp xr xs
                          , getRes yp yr ys
                          )

type CheckTypesCtx s = [(TermContext s, TCTerm, TCTerm)]

-- | Check types in two terms are equal.
checkTypesEqual :: forall s . Pos -> CheckTypesCtx s
                -> TermContext s -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual p ctx tc x y = do
  xr <- reduce tc x
  yr <- reduce tc y
  checkTypesEqual' p ctx tc xr yr

-- | Check types applied to reduced terms.
checkTypesEqual' :: forall s . Pos -> CheckTypesCtx s
                 -> TermContext s -> TCTerm -> TCTerm -> TC s ()
checkTypesEqual' p ctx tc x y = do
  let check' = checkTypesEqual p ((tc,x,y):ctx)
      checkAll :: Foldable t => t (TCTerm, TCTerm) -> TC s ()
      checkAll = traverseOf_ folded (uncurry (check' tc))
  case (tcAsApp x, tcAsApp y) of
    ( (TCF (GlobalDef xg), xa), (TCF (GlobalDef yg), ya))
      | xg == yg && length xa == length ya -> do
        checkAll (zip xa ya)

    ( (TCF UnitValue, []), (TCF UnitValue, [])) ->
        checkAll []
    ( (TCF (PairValue x1 x2), []), (TCF (PairValue y1 y2), [])) ->
        checkAll [(x1, y1), (x2, y2)]
    ( (TCF UnitType, []), (TCF UnitType, [])) ->
        checkAll []
    ( (TCF (PairType x1 x2), []), (TCF (PairType y1 y2), [])) ->
        checkAll [(x1, y1), (x2, y2)]

    ( (TCF EmptyValue, []), (TCF EmptyValue, [])) ->
        checkAll []
    ( (TCF (FieldValue x1 x2 x3), []), (TCF (FieldValue y1 y2 y3), [])) ->
        checkAll [(x1, y1), (x2, y2), (x3, y3)]
    ( (TCF EmptyType, []), (TCF EmptyType, [])) ->
        checkAll []
    ( (TCF (FieldType x1 x2 x3), []), (TCF (FieldType y1 y2 y3), [])) ->
        checkAll [(x1, y1), (x2, y2), (x3, y3)]
    ( (TCF (RecordSelector xr xf), []), (TCF (RecordSelector yr yf), [])) ->
        checkAll [(xr, yr), (xf, yf)]

    ( (TCF (CtorApp xc xa), []), (TCF (CtorApp yc ya), []))
      | xc == yc ->
        checkAll (zip xa ya)
    ( (TCF (DataTypeApp xdt xa), []), (TCF (DataTypeApp ydt ya), []))
      | xdt == ydt ->
        checkAll (zip xa ya)

    ( (TCF (Sort xs), []), (TCF (Sort ys), [])) | xs == ys -> return ()

    ( (TCF (NatLit xi), []), (TCF (NatLit yi), [])) | xi == yi -> return ()
    ( (TCF (StringLit xs), []), (TCF (StringLit ys), [])) | xs == ys -> return ()
    ( (TCF (ArrayValue xtp xv), []), (TCF (ArrayValue ytp yv), []))
      | V.length xv == V.length yv ->
         check' tc xtp ytp *> checkAll (V.zip xv yv)
    ( (TCLambda xp xtp xr, []), (TCLambda yp ytp yr, []) ) -> do
       check' tc xtp ytp
       mr <- instPats p tc xtp (xp,xr) (yp,yr)
       case mr of
         Nothing -> return ()
         Just (tc', xr', yr') -> do
           --let xr' = tcApply tc (extendPatContext tc xp, xr) (tc', xsub)
           --let yr' = tcApply tc (extendPatContext tc yp, yr) (tc', ysub)
           check' tc' xr' yr'

    ( (TCPi xp xtp xr, []), (TCPi yp ytp yr, []) ) -> do
       check' tc xtp ytp
       mr <- instPats p tc xtp (xp,xr) (yp,yr)
       case mr of
         Nothing -> return ()
         Just (tc', xr', yr') ->
           check' tc' xr' yr'

    ( (TCVar xi, xa), (TCVar yi, ya))
      | xi == yi && length xa == length ya ->
        checkAll (zip xa ya)

    ( (TCF (NatLit 0), []), (TCF (CtorApp c []), []))
      | c == preludeZeroIdent -> pure ()
    ( (TCF (CtorApp c []), []), (TCF (NatLit 0), []))
      | c == preludeZeroIdent -> pure ()

    ( (TCF (NatLit n), []), (TCF (CtorApp c [b]), []))
      | c == preludeSuccIdent && n > 0 ->
      check' tc (TCF (NatLit (n-1))) b
    ( (TCF (CtorApp c [b]), []), (TCF (NatLit n), []))
      | c == preludeSuccIdent && n > 0 ->
      check' tc b (TCF (NatLit (n-1)))
    _ -> do
       tcFail p $ show $ text "Equivalence check failed during typechecking:"  <$$>
          nest 2 (ppTCTerm tc PrecNone x) <$$> text "and\n" <$$>
          nest 2 (ppTCTerm tc PrecNone y) <$$> text "in context\n" <$$>
          nest 4 (ppTermContext tc) <$$>
          nest 2 (vcat (ppScope <$> ctx))
      where ppScope (tc',x',y') =
             text "while typechecking" <$$>
             nest 2 (ppTCTerm tc PrecNone x') <$$> text "and\n" <$$>
             nest 2 (ppTCTerm tc PrecNone y') <$$> text "in context\n" <$$>
             nest 4 (ppTermContext tc')
