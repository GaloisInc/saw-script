{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module SAWScript.Heapster.Permissions where

import Data.Maybe
import Data.Bits
import Data.List
import Data.String
import Data.Proxy
import Data.Functor.Constant
import Data.Reflection
import Data.Binding.Hobbits
import GHC.TypeLits
import Data.Kind
import Control.Applicative hiding (empty)
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Lens hiding ((:>), Index, Empty)

import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, zipWith)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core
import Verifier.SAW.Term.Functor (Ident)
import Verifier.SAW.OpenTerm

import SAWScript.Heapster.CruUtil

import Debug.Trace


----------------------------------------------------------------------
-- * Monads that Support Name-Binding
----------------------------------------------------------------------

-- FIXME HERE: move all of the below to Hobbits!

type RNil = 'RNil
type (:>) = '(:>)

class Monad m => MonadBind m where
  mbM :: NuMatching a => Mb ctx (m a) -> m (Mb ctx a)

nuM :: (MonadBind m, NuMatching b) => (Name a -> m b) -> m (Binding a b)
nuM = mbM . nu

instance MonadBind Identity where
  mbM = Identity . fmap runIdentity

instance MonadBind Maybe where
  mbM [nuP| Just x |] = return x
  mbM [nuP| Nothing |] = Nothing

instance MonadBind m => MonadBind (ReaderT r m) where
  mbM mb = ReaderT $ \r -> mbM $ fmap (flip runReaderT r) mb

-- | A version of 'MonadBind' that does not require a 'NuMatching' instance on
-- the element type of the multi-binding in the monad
class MonadBind m => MonadStrongBind m where
  strongMbM :: Mb ctx (m a) -> m (Mb ctx a)

instance MonadStrongBind Identity where
  strongMbM = Identity . fmap runIdentity

instance MonadStrongBind m => MonadStrongBind (ReaderT r m) where
  strongMbM mb = ReaderT $ \r -> strongMbM $ fmap (flip runReaderT r) mb

-- | State types that can incorporate name-bindings
class NuMatching s => BindState s where
  bindState :: Mb ctx s -> s

instance BindState (Closed s) where
  bindState = mbLift

instance (MonadBind m, BindState s) => MonadBind (StateT s m) where
  mbM mb_m = StateT $ \s ->
    mbM (fmap (\m -> runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

instance (MonadStrongBind m, BindState s) => MonadStrongBind (StateT s m) where
  strongMbM mb_m = StateT $ \s ->
    strongMbM (fmap (\m -> runStateT m s) mb_m) >>= \mb_as ->
    return (fmap fst mb_as, bindState (fmap snd mb_as))

-- | A monad whose effects are closed
class Monad m => MonadClosed m where
  closedM :: Closed (m a) -> m (Closed a)

instance MonadClosed Identity where
  closedM = Identity . clApply $(mkClosed [| runIdentity |])

instance (MonadClosed m, Closable s) => MonadClosed (StateT s m) where
  closedM clm =
    do s <- get
       cl_a_s <- lift $ closedM ($(mkClosed [| runStateT |]) `clApply` clm
                                 `clApply` toClosed s)
       put (snd $ unClosed cl_a_s)
       return ($(mkClosed [| fst |]) `clApply` cl_a_s)


----------------------------------------------------------------------
-- * Pretty-printing
----------------------------------------------------------------------

newtype StringF a = StringF { unStringF :: String }

data PPInfo =
  PPInfo { ppExprNames :: NameMap (StringF :: CrucibleType -> Type),
           ppPermNames :: NameMap (StringF :: Type -> Type),
           ppVarIndex :: Int }

emptyPPInfo :: PPInfo
emptyPPInfo = PPInfo NameMap.empty NameMap.empty 1

-- | Record an expression variable in a 'PPInfo' with the given base name
ppInfoAddExprName :: String -> ExprVar a -> PPInfo -> PPInfo
ppInfoAddExprName base x info =
  info { ppExprNames =
           NameMap.insert x (StringF (base ++ show (ppVarIndex info)))
           (ppExprNames info),
           ppVarIndex = ppVarIndex info + 1 }

ppInfoAddExprNames :: String -> MapRList Name (tps :: RList CrucibleType) ->
                      PPInfo -> PPInfo
ppInfoAddExprNames _ MNil info = info
ppInfoAddExprNames base (ns :>: n) info =
  ppInfoAddExprNames base ns $ ppInfoAddExprName base n info

-- | Record a permission variable in a 'PPInfo' with the given base name
ppInfoAddPermName :: String -> Name (a :: Type) -> PPInfo -> PPInfo
ppInfoAddPermName base x info =
  info { ppPermNames =
           NameMap.insert x (StringF (base ++ show (ppVarIndex info)))
           (ppPermNames info),
           ppVarIndex = ppVarIndex info + 1 }

ppInfoAddPermNames :: String -> MapRList Name (tps :: RList Type) ->
                      PPInfo -> PPInfo
ppInfoAddPermNames _ MNil info = info
ppInfoAddPermNames base (ns :>: n) info =
  ppInfoAddPermNames base ns $ ppInfoAddPermName base n info


type PermPPM = Reader PPInfo

instance NuMatching Doc where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable Doc where
  toClosed = unsafeClose

instance Liftable Doc where
  mbLift = unClosed . mbLift . fmap toClosed


class PermPretty a where
  permPrettyM :: a -> PermPPM Doc

permPretty :: PermPretty a => PPInfo -> a -> Doc
permPretty info a = runReader (permPrettyM a) info

permPrettyString :: PermPretty a => PPInfo -> a -> String
permPrettyString info a =
  flip displayS "" $ renderPretty 0.8 80 $ permPretty info a

tracePretty :: Doc -> a -> a
tracePretty doc = trace (flip displayS "" $ renderPretty 0.8 80 doc)

instance PermPretty (ExprVar a) where
  permPrettyM x =
    do maybe_str <- NameMap.lookup x <$> ppExprNames <$> ask
       case maybe_str of
         Just (StringF str) -> return $ string str
         Nothing -> return $ string (show x)

instance PermPretty (Name (a :: Type)) where
  permPrettyM x =
    do maybe_str <- NameMap.lookup x <$> ppPermNames <$> ask
       case maybe_str of
         Just (StringF str) -> return $ string str
         Nothing -> return $ string (show x)

instance PermPretty (MapRList Name (ctx :: RList CrucibleType)) where
  permPrettyM MNil = return PP.empty
  permPrettyM (MNil :>: n) = permPrettyM n
  permPrettyM (ns :>: n) =
    do pp_ns <- permPrettyM ns
       pp_n <- permPrettyM n
       return (pp_ns <> comma <+> pp_n)

-- FIXME: move to Hobbits...?
{-
instance TraversableFC MapRList where
  traverseFC _ MNil = pure MNil
  traverseFC f (xs :>: x) = (:>:) <$> traverseFC f xs <*> f x
-}

-- FIXME: this is just TraversableFC without having an orphan instance...
traverseMapRList :: Applicative m => (forall a. f a -> m (g a)) ->
                    MapRList f as -> m (MapRList g as)
traverseMapRList _ MNil = pure MNil
traverseMapRList f (xs :>: x) = (:>:) <$> traverseMapRList f xs <*> f x

permPrettyExprMb :: PermPretty a =>
                    (MapRList (Constant Doc) ctx -> PermPPM Doc -> PermPPM Doc) ->
                    Mb (ctx :: RList CrucibleType) a -> PermPPM Doc
permPrettyExprMb f mb =
  fmap mbLift $ strongMbM $ flip nuMultiWithElim1 mb $ \ns a ->
  local (ppInfoAddExprNames "z" ns) $
  do docs <- traverseMapRList (\n -> Constant <$> permPrettyM n) ns
     f docs $ permPrettyM a

permPrettyPermMb :: PermPretty a =>
                    (MapRList (Constant Doc) ctx -> PermPPM Doc -> PermPPM Doc) ->
                    Mb (ctx :: RList Type) a -> PermPPM Doc
permPrettyPermMb f mb =
  fmap mbLift $ strongMbM $ flip nuMultiWithElim1 mb $ \ns a ->
  local (ppInfoAddPermNames "z" ns) $
  do docs <- traverseMapRList (\n -> Constant <$> permPrettyM n) ns
     f docs $ permPrettyM a

instance PermPretty a => PermPretty (Mb (ctx :: RList CrucibleType) a) where
  permPrettyM =
    permPrettyExprMb $ \docs ppm ->
    (\pp -> hang 2 (tupled (mapRListToList docs) <> dot </> pp)) <$> ppm

instance PermPretty a => PermPretty (Mb (ctx :: RList Type) a) where
  permPrettyM =
    permPrettyPermMb $ \docs ppm ->
    (\pp -> hang 2 (tupled (mapRListToList docs) <> dot </> pp)) <$> ppm


----------------------------------------------------------------------
-- * Expressions for Permissions
----------------------------------------------------------------------

-- | The Haskell type of expression variables
type ExprVar (a :: CrucibleType) = Name a

-- | Crucible type for lifetimes; we give them a Crucible type so they can be
-- existentially bound in the same way as other Crucible objects
type LifetimeType = IntrinsicType "Lifetime" EmptyCtx

-- | The object-level representation of 'LifetimeType'
lifetimeTypeRepr :: TypeRepr LifetimeType
lifetimeTypeRepr = knownRepr

-- | Pattern for building/destructing lifetime types
pattern LifetimeRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "Lifetime") ->
                 Just Refl)
  Empty
  where LifetimeRepr = IntrinsicRepr knownSymbol Empty

-- | A lifetime is an expression of type 'LifetimeType'
type Lifetime = PermExpr LifetimeType

-- | Crucible type for read/write modalities; we give them a Crucible type so
-- they can be used as variables in recursive permission definitions
type RWModalityType = IntrinsicType "RWModality" EmptyCtx

-- | The object-level representation of 'RWModalityType'
rwModalityTypeRepr :: TypeRepr RWModalityType
rwModalityTypeRepr = knownRepr

-- | Pattern for building/destructing RWModality types
pattern RWModalityRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "RWModality") ->
                 Just Refl)
  Empty
  where RWModalityRepr = IntrinsicRepr knownSymbol Empty

-- | Crucible type for lists of expressions and permissions on them
type PermListType = IntrinsicType "PermList" EmptyCtx

-- | Pattern for building/desctructing permission list types
pattern PermListRepr :: () => ty ~ PermListType => TypeRepr ty
pattern PermListRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "PermList") ->
                 Just Refl) Empty
  where
    PermListRepr = IntrinsicRepr knownSymbol Empty

-- | Crucible type for LLVM stack frame objects
type LLVMFrameType w = IntrinsicType "LLVM_frame" (EmptyCtx ::> BVType w)

-- | Pattern for building/desctructing LLVM frame types
pattern LLVMFrameRepr :: () => (1 <= w, ty ~ LLVMFrameType w) =>
                         NatRepr w -> TypeRepr ty
pattern LLVMFrameRepr w <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_frame") ->
                 Just Refl)
  (viewAssign -> AssignExtend Empty (BVRepr w))
  where
    LLVMFrameRepr w = IntrinsicRepr knownSymbol (extend Empty (BVRepr w))


-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (a :: CrucibleType) where
  PExpr_Var :: ExprVar a -> PermExpr a
  -- ^ A variable of any type

  PExpr_Unit :: PermExpr UnitType
  -- ^ A unit literal

  PExpr_Bool :: Bool -> PermExpr BoolType
  -- ^ A literal Boolean number

  PExpr_Nat :: Integer -> PermExpr NatType
  -- ^ A literal natural number

  PExpr_BV :: (1 <= w, KnownNat w) =>
              [BVFactor w] -> Integer -> PermExpr (BVType w)
  -- ^ A bitvector expression is a linear expression in @N@ variables, i.e., sum
  -- of constant times variable factors plus a constant
  --
  -- FIXME: make the offset a 'Natural'

  PExpr_Struct :: PermExprs (CtxToRList args) -> PermExpr (StructType args)
  -- ^ A struct expression is an expression for each argument of the struct type

  PExpr_Always :: PermExpr LifetimeType
  -- ^ The @always@ lifetime that is always current

  PExpr_LLVMWord :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermExpr (LLVMPointerType w)
  -- ^ An LLVM value that represents a word, i.e., whose region identifier is 0

  PExpr_LLVMOffset :: (1 <= w, KnownNat w) =>
                      ExprVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      PermExpr (LLVMPointerType w)
  -- ^ An LLVM value built by adding an offset to an LLVM variable

  PExpr_Fun :: FnHandle args ret -> PermExpr (FunctionHandleType args ret)
  -- ^ A literal function pointer

  PExpr_PermListNil :: PermExpr PermListType
  -- ^ An empty list of expressions plus permissions

  PExpr_PermListCons :: KnownRepr TypeRepr a => PermExpr a -> ValuePerm a ->
                        PermExpr PermListType -> PermExpr PermListType
  -- ^ A cons of an expression and permission for that expression onto a
  -- permission list
  --
  -- FIXME: turn the 'KnownRepr' constraint into a normal 'TypeRepr' argument

  PExpr_RWModality :: RWModality -> PermExpr RWModalityType
  -- ^ A read/write modality 


-- | A sequence of permission expressions
data PermExprs (as :: RList CrucibleType) where
  PExprs_Nil :: PermExprs RNil
  PExprs_Cons :: PermExprs as -> PermExpr a -> PermExprs (as :> a)

-- | A bitvector variable, possibly multiplied by a constant
data BVFactor w where
  BVFactor :: (1 <= w, KnownNat w) => Integer -> ExprVar (BVType w) ->
              BVFactor w
  -- ^ A variable of type @'BVType' w@ multiplied by a constant @i@, which
  -- should be in the range @0 <= i < 2^w@
  --
  -- FIXME: make the constant a 'Natural'

-- | Whether a permission allows reads or writes
data RWModality
  = Write
  | Read
  deriving Eq


instance Eq (PermExpr a) where
  (PExpr_Var x1) == (PExpr_Var x2) = x1 == x2
  (PExpr_Var _) == _ = False

  PExpr_Unit == PExpr_Unit = True
  PExpr_Unit == _ = False

  (PExpr_Nat n1) == (PExpr_Nat n2) = n1 == n2
  (PExpr_Nat _) == _ = False

  (PExpr_Bool b1) == (PExpr_Bool b2) = b1 == b2
  (PExpr_Bool _) == _ = False

  (PExpr_BV factors1 const1) == (PExpr_BV factors2 const2) =
    const1 == const2 && eqFactors factors1 factors2
    where
      eqFactors :: [BVFactor w] -> [BVFactor w] -> Bool
      eqFactors [] [] = True
      eqFactors (f : factors1) factors2
        | elem f factors2 = eqFactors factors1 (delete f factors2)
      eqFactors _ _ = False
  (PExpr_BV _ _) == _ = False

  (PExpr_Struct args1) == (PExpr_Struct args2) = args1 == args2 where
  (PExpr_Struct _) == _ = False

  PExpr_Always == PExpr_Always = True
  PExpr_Always == _ = False

  (PExpr_LLVMWord e1) == (PExpr_LLVMWord e2) = e1 == e2
  (PExpr_LLVMWord _) == _ = False

  (PExpr_LLVMOffset x1 e1) == (PExpr_LLVMOffset x2 e2) =
    x1 == x2 && e1 == e2
  (PExpr_LLVMOffset _ _) == _ = False

  (PExpr_Fun fh1) == (PExpr_Fun fh2) = fh1 == fh2
  (PExpr_Fun _) == _ = False

  PExpr_PermListNil == PExpr_PermListNil = True
  PExpr_PermListNil == _ = False

  (PExpr_PermListCons (e1 :: PermExpr a1) p1 l1)
    == (PExpr_PermListCons (e2 :: PermExpr a2) p2 l2)
    | Just Refl <-
        testEquality (knownRepr :: TypeRepr a1) (knownRepr :: TypeRepr a2)
    = e1 == e2 && p1 == p2 && l1 == l2
  (PExpr_PermListCons _ _ _) == _ = False

  (PExpr_RWModality rw1) == (PExpr_RWModality rw2) = rw1 == rw2
  (PExpr_RWModality _) == _ = False


instance Eq (PermExprs as) where
  PExprs_Nil == PExprs_Nil = True
  (PExprs_Cons es1 e1) == (PExprs_Cons es2 e2) = es1 == es2 && e1 == e2

instance Eq (BVFactor w) where
  (BVFactor i1 x1) == (BVFactor i2 x2) = i1 == i2 && x1 == x2


instance PermPretty (PermExpr a) where
  permPrettyM (PExpr_Var x) = permPrettyM x
  permPrettyM PExpr_Unit = return $ string "()"
  permPrettyM (PExpr_Nat n) = return $ integer n
  permPrettyM (PExpr_Bool b) = return $ bool b
  permPrettyM (PExpr_BV factors const) =
    do pps <- mapM permPrettyM factors
       return $ encloseSep lparen rparen (string "+") (pps ++ [integer const])
  permPrettyM (PExpr_Struct args) =
    (\pp -> string "struct" <+> parens pp) <$> permPrettyM args
  permPrettyM PExpr_Always = return $ string "always"
  permPrettyM (PExpr_LLVMWord e) = (string "LLVMword" <+>) <$> permPrettyM e
  permPrettyM (PExpr_LLVMOffset x e) =
    (\ppx ppe -> ppx <+> string "&+" <+> ppe)
    <$> permPrettyM x <*> permPrettyM e
  permPrettyM (PExpr_Fun fh) = return $ angles $ string ("fun" ++ show fh)
  permPrettyM PExpr_PermListNil = return $ string "[]"
  permPrettyM e@(PExpr_PermListCons _ _ _) = prettyPermListM e
  permPrettyM (PExpr_RWModality rw) = permPrettyM rw

prettyPermListH :: PermExpr PermListType -> PermPPM ([Doc], Maybe Doc)
prettyPermListH (PExpr_Var x) = (\pp -> ([], Just pp)) <$> permPrettyM x
prettyPermListH PExpr_PermListNil = return ([], Nothing)
prettyPermListH (PExpr_PermListCons e p l) =
  (\ppe ppp (pps, maybe_doc) -> (ppe <> colon <> ppp : pps, maybe_doc))
  <$> permPrettyM e <*> permPrettyM p <*> prettyPermListH l

prettyPermListM :: PermExpr PermListType -> PermPPM Doc
prettyPermListM e = prettyPermListH e >>= \(pps, maybe_doc) ->
  case maybe_doc of
    Just pp_x -> return $ encloseSep lparen rparen (string "::") (pps ++ [pp_x])
    Nothing -> return $ list pps

instance PermPretty (PermExprs as) where
  permPrettyM es = tupled <$> helper es where
    helper :: PermExprs as' -> PermPPM [Doc]
    helper PExprs_Nil = return []
    helper (PExprs_Cons es e) =
      (\pps pp -> pps ++ [pp]) <$> helper es <*> permPrettyM e

instance PermPretty (BVFactor w) where
  permPrettyM (BVFactor i x) = ((integer i <> string "*") <>) <$> permPrettyM x

instance PermPretty RWModality where
  permPrettyM Read = return $ string "R"
  permPrettyM Write = return $ string "W"

-- | The 'Write' modality as an expression
pattern PExpr_Write :: PermExpr RWModalityType
pattern PExpr_Write = PExpr_RWModality Write

-- | The 'Read' modality as an expression
pattern PExpr_Read :: PermExpr RWModalityType
pattern PExpr_Read = PExpr_RWModality Read

-- | Build a "default" expression for a given type
zeroOfType :: TypeRepr tp -> PermExpr tp
zeroOfType (BVRepr w) = withKnownNat w $ PExpr_BV [] 0
zeroOfType LifetimeRepr = PExpr_Always
zeroOfType _ = error "zeroOfType"


----------------------------------------------------------------------
-- * Operations on Bitvector and LLVM Pointer Expressions
----------------------------------------------------------------------

-- | Normalize a factor so that its coefficient is between @0@ and @(2^w)-1@
normalizeFactor :: BVFactor w -> BVFactor w
normalizeFactor f@(BVFactor i x) =
  BVFactor (i `mod` (shiftL 1 $ fromInteger $ natVal f)) x

-- | Smart constructor for 'BVFactor'
bvFactor :: (1 <= w, KnownNat w) => Integer -> ExprVar (BVType w) ->
            BVFactor w
bvFactor i x = normalizeFactor $ BVFactor i x

-- | Build a 'BVFactor' for a variable
varFactor :: (1 <= w, KnownNat w) => ExprVar (BVType w) -> BVFactor w
varFactor = BVFactor 1

-- | Normalize a bitvector expression, so that every variable has at most one
-- factor and the factors are sorted by variable name. NOTE: we shouldn't
-- actually have to call this if we always construct our expressions with the
-- combinators below.
bvNormalize :: PermExpr (BVType w) -> PermExpr (BVType w)
bvNormalize e@(PExpr_Var _) = e
bvNormalize (PExpr_BV factors off) =
  PExpr_BV
  (norm (sortBy (\(BVFactor _ x) (BVFactor _ y) -> compare x y) factors))
  off
  where
    norm [] = []
    norm ((BVFactor 0 _) : factors') = norm factors'
    norm ((BVFactor i1 x1) : (BVFactor i2 x2) : factors')
      | x1 == x2 = norm ((bvFactor (i1+i2) x1) : factors')
    norm (f : factors') = normalizeFactor f : norm factors'

-- | Merge two normalized / sorted lists of 'BVFactor's
bvMergeFactors :: [BVFactor w] -> [BVFactor w] -> [BVFactor w]
bvMergeFactors fs1 fs2 =
  filter (\(BVFactor i _) -> i /= 0) $
  helper fs1 fs2
  where
    helper factors1 [] = factors1
    helper [] factors2 = factors2
    helper ((BVFactor i1 x1):factors1) ((BVFactor i2 x2):factors2)
      | x1 == x2
      = bvFactor (i1+i2) x1 : helper factors1 factors2
    helper (f1@(BVFactor _ x1):factors1) (f2@(BVFactor _ x2):factors2)
      | x1 < x2 = f1 : helper factors1 (f2 : factors2)
    helper (f1@(BVFactor _ _):factors1) (f2@(BVFactor _ _):factors2) =
      f2 : helper (f1 : factors1) factors2

-- | Convert a bitvector expression to a sum of factors plus a constant
bvMatch :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
           ([BVFactor w], Integer)
bvMatch (PExpr_Var x) = ([varFactor x], 0)
bvMatch (PExpr_BV factors const) = (factors, const)

-- | Test if a bitvector expression is a constant value
bvMatchConst :: PermExpr (BVType w) -> Maybe Integer
bvMatchConst (PExpr_BV [] const) = Just const
bvMatchConst _ = Nothing

-- | Normalize a bitvector expression to a canonical form. Currently this just
-- means converting @1*x+0@ to @x@.
normalizeBVExpr :: PermExpr (BVType w) -> PermExpr (BVType w)
normalizeBVExpr (PExpr_BV [BVFactor 1 x] 0) = PExpr_Var x
normalizeBVExpr e = e

-- | Test whether two bitvector expressions are semantically equal, assuming
-- they are both in normal form
bvEq :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvEq e1 e2 = normalizeBVExpr e1 == normalizeBVExpr e2

-- | Test whether a bitvector expression is less than another for all
-- substitutions to the free variables. This is an underapproximation, meaning
-- that it could return 'False' in cases where it is actually 'True'. The
-- current algorithm only returns 'True' for constant expressions @k1 < k2@.
bvLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvLt (PExpr_BV [] k1) (PExpr_BV [] k2) = k1 < k2
bvLt _ _ = False

-- | Test whether a bitvector expression is in a 'BVRange' for all substitutions
-- to the free variables. This is an underapproximation, meaning that it could
-- return 'False' in cases where it is actually 'True'.
bvInRange :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w -> Bool
bvInRange e (BVRange off len) =
  (bvEq off e || bvLt off e) && bvLt e (bvAdd off len)


-- | Test whether a bitvector @e@ could equal @0@, i.e., whether the equation
-- @e=0@ has any solutions.
--
-- NOTE: this is an overapproximation, meaning that it may return 'True' for
-- complex expressions that technically cannot unify with @0@.
bvZeroable :: PermExpr (BVType w) -> Bool
bvZeroable (PExpr_Var _) = True
bvZeroable (PExpr_BV _ 0) = True
bvZeroable (PExpr_BV [] _) = False
bvZeroable (PExpr_BV _ _) =
  -- NOTE: there are cases that match this pattern but are still not solvable,
  -- like 8*x + 3 = 0.
  True

-- | Test whether two bitvector expressions are potentially unifiable, i.e.,
-- whether some substitution to the variables could make them equal. This is an
-- overapproximation, meaning that some expressions are marked as "could" equal
-- when they actually cannot.
bvCouldEqual :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldEqual e1@(PExpr_BV _ _) e2 =
  -- NOTE: we can only call bvSub when at least one side matches PExpr_BV
  bvZeroable (bvSub e1 e2)
bvCouldEqual e1 e2@(PExpr_BV _ _) = bvZeroable (bvSub e1 e2)
bvCouldEqual _ _ = True

-- | Test whether a bitvector expression could potentially be less than another,
-- for some substitution to the free variables. This is an overapproximation,
-- meaning that some expressions are marked as "could" be less than when they
-- actually cannot. The current algorithm returns 'True' in all cases except
-- constant expressions @k1 >= k2@.
bvCouldBeLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldBeLt (PExpr_BV [] k1) (PExpr_BV [] k2) = k1 < k2
bvCouldBeLt _ _ = True

-- | Test whether a bitvector expression is in a 'BVRange' for all substitutions
-- to the free variables. This is an overapproximation, meaning that some
-- expressions are marked as "could" be in the range when they actually cannot.
bvCouldBeInRange :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w -> Bool
bvCouldBeInRange e (BVRange off len) =
  (bvCouldEqual off e || bvCouldBeLt off e) && bvCouldBeLt e (bvAdd off len)

-- | Test whether a 'BVProp' "could" hold for all substitutions of the free
-- variables. This is an overapproximation, meaning that some propositions are
-- marked as "could" hold when they actually cannot.
bvPropCouldHold :: (1 <= w, KnownNat w) => BVProp w -> Bool
bvPropCouldHold (BVProp_Eq e1 e2) = bvCouldEqual e1 e2
bvPropCouldHold (BVProp_Neq e1 e2) = not (bvEq e1 e2)
bvPropCouldHold (BVProp_InRange e rng) = bvCouldBeInRange e rng
bvPropCouldHold (BVProp_NotInRange e rng) = not (bvInRange e rng)
bvPropCouldHold (BVProp_RangeSubset rng1 rng2) =
  bvCouldBeInRange (bvRangeOffset rng1) rng2 &&
  bvCouldBeInRange (bvSub
                    (bvAdd (bvRangeOffset rng1) (bvRangeLength rng1))
                    (bvInt 1)) rng2
bvPropCouldHold (BVProp_RangesDisjoint rng1 rng2) =
  -- NOTE: if two ranges are not disjoint then either one fully contains the
  -- other or they overlap. In either case, one range will contain the first
  -- value of the other.
  not (bvInRange (bvRangeOffset rng1) rng2) &&
  not (bvInRange (bvRangeOffset rng2) rng1)


-- | Build a bitvector expression from an integer
bvInt :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w)
bvInt i = PExpr_BV [] i

-- | Add two bitvector expressions
bvAdd :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvAdd (bvMatch -> (factors1, const1)) (bvMatch -> (factors2, const2)) =
  PExpr_BV (bvMergeFactors factors1 factors2) (const1 + const2)

-- | Multiply a bitvector expression by a constant
bvMult :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w) ->
          PermExpr (BVType w)
bvMult i (PExpr_Var x) = PExpr_BV [bvFactor i x] 0
bvMult i (PExpr_BV factors off) =
  PExpr_BV (map (\(BVFactor j x) -> bvFactor (i*j) x) factors) (i*off)

-- | Negate a bitvector expression
bvNegate :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w)
bvNegate = bvMult (-1)

-- | Subtract one bitvector expression from another
--
-- FIXME: this would be more efficient if we did not use 'bvNegate', which could
-- make very large 'Integer's for negative numbers wrapped around to be positive
bvSub :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvSub e1 e2 = bvAdd e1 (bvNegate e2)

-- | Integer division on bitvector expressions, truncating any factors @i*x@
-- where @i@ is not a multiple of the divisor to zero
bvDiv :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvDiv (bvMatch -> (factors, off)) n =
  PExpr_BV (mapMaybe (\(BVFactor i x) ->
                       if mod i n == 0 then
                         -- NOTE: if i is in range then so is i/n, so we do not
                         -- need to normalize the resulting BVFactor
                         Just (BVFactor (div i n) x)
                       else Nothing) factors)
  (div off n)

-- | Integer Modulus on bitvector expressions, where any factors @i*x@ with @i@
-- not a multiple of the divisor are included in the modulus
bvMod :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvMod (bvMatch -> (factors, off)) n =
  PExpr_BV (mapMaybe (\f@(BVFactor i _) ->
                       if mod i n /= 0 then Just f else Nothing) factors)
  (mod off n)

-- | Given a constant factor @a@, test if a bitvector expression can be written
-- as @a*x+y@ for some constant @y@
bvMatchFactorPlusConst :: (1 <= w, KnownNat w) =>
                          Integer -> PermExpr (BVType w) ->
                          Maybe (PermExpr (BVType w), Integer)
bvMatchFactorPlusConst a e =
  bvMatchConst (bvMod e a) >>= \y -> Just (bvDiv e a, y)

-- | Convert an LLVM pointer expression to a variable + optional offset, if this
-- is possible
asLLVMOffset :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                Maybe (ExprVar (LLVMPointerType w), PermExpr (BVType w))
asLLVMOffset (PExpr_Var x) = Just (x, bvInt 0)
asLLVMOffset (PExpr_LLVMOffset x off) = Just (x, off)
asLLVMOffset _ = Nothing

-- | Add a word expression to an LLVM pointer expression
addLLVMOffset :: (1 <= w, KnownNat w) =>
                 PermExpr (LLVMPointerType w) -> PermExpr (BVType w) ->
                 PermExpr (LLVMPointerType w)
addLLVMOffset (PExpr_Var x) off = PExpr_LLVMOffset x off
addLLVMOffset (PExpr_LLVMWord e) off = PExpr_LLVMWord $ bvAdd e off
addLLVMOffset (PExpr_LLVMOffset x e) off =
  PExpr_LLVMOffset x $ bvAdd e off

-- | Build a range that contains exactly one index
bvRangeOfIndex :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w
bvRangeOfIndex e = BVRange e (bvInt 1)


----------------------------------------------------------------------
-- * Permissions
----------------------------------------------------------------------

-- | Ranges of bitvector values
data BVRange w = BVRange { bvRangeOffset :: PermExpr (BVType w),
                           bvRangeLength :: PermExpr (BVType w) }
               deriving Eq

-- | Propositions about bitvectors
data BVProp w
  = BVProp_Eq (PermExpr (BVType w)) (PermExpr (BVType w))
    -- ^ True iff the two expressions are equal
  | BVProp_Neq (PermExpr (BVType w)) (PermExpr (BVType w))
    -- ^ True iff the two expressions are not equal
  | BVProp_InRange (PermExpr (BVType w)) (BVRange w)
    -- ^ True iff the first expression is greater than or equal to the second
    -- and less than the third, i.e., in the half-closed interval @[e2,e3)@
  | BVProp_NotInRange (PermExpr (BVType w)) (BVRange w)
    -- ^ True iff the first expression is *not* in the given range
  | BVProp_RangeSubset (BVRange w) (BVRange w)
    -- ^ True iff the first and second expressions form an interval that is
    -- contained in that formed by the third and fourth, i.e., iff @[e1,e2)@ is
    -- a subset of @[e3,e4)@
  | BVProp_RangesDisjoint (BVRange w) (BVRange w)
    -- ^ True iff the first and second expressions form an interval that is
    -- disjoint from that formed by the third and fourth, i.e., iff @[e1,e2)@
    -- and @[e3,e4)@ do not overlap
  deriving Eq

-- | An atomic permission is a value permission that is not one of the compound
-- constructs in the 'ValuePerm' type; i.e., not a disjunction, existential,
-- recursive, or equals permission. These are the permissions that we can put
-- together with separating conjuctions.
data AtomicPerm (a :: CrucibleType) where
  -- | Gives permissions to a single field pointed to by an LLVM pointer
  Perm_LLVMField :: (1 <= w, KnownNat w) => LLVMFieldPerm w ->
                    AtomicPerm (LLVMPointerType w)

  -- | Gives permissions to an array pointer to by an LLVM pointer
  Perm_LLVMArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                    AtomicPerm (LLVMPointerType w)

  -- | Says that we have permission to free the memory pointed at by this
  -- pointer if we have write permission to @e@ words of size @w@
  Perm_LLVMFree :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                   AtomicPerm (LLVMPointerType w)

  -- | Says that we known an LLVM value is a function pointer whose function has
  -- the given function permissions
  Perm_LLVMFunPtr :: (1 <= w, KnownNat w) => FunPerm ghosts args ret ->
                     AtomicPerm (LLVMPointerType w)

  -- | Says we know an LLVM value is a pointer value, meaning that its block
  -- value is non-zero. Note that this does not say the pointer is allocated.
  Perm_IsLLVMPtr :: (1 <= w, KnownNat w) =>
                    AtomicPerm (LLVMPointerType w)

  -- | Permission to allocate (via @alloca@) on an LLVM stack frame, and
  -- permission to delete that stack frame if we have exclusive permissions to
  -- all the given LLVM pointer objects
  Perm_LLVMFrame :: (1 <= w, KnownNat w) => LLVMFramePerm w ->
                    AtomicPerm (LLVMFrameType w)

  -- | Ownership permission for a lifetime, including an assertion that it is
  -- still current and permission to end that lifetime and get back the given
  -- permissions that are being held by the lifetime
  Perm_LOwned :: PermExpr PermListType -> AtomicPerm LifetimeType

  -- | Assertion that a lifetime is current during another lifetime
  Perm_LCurrent :: PermExpr LifetimeType -> AtomicPerm LifetimeType

  -- | A function permission
  Perm_Fun :: FunPerm ghosts (CtxToRList cargs) ret ->
              AtomicPerm (FunctionHandleType cargs ret)

  -- | An LLVM permission that asserts a proposition about bitvectors
  Perm_BVProp :: (1 <= w, KnownNat w) => BVProp w ->
                 AtomicPerm (LLVMPointerType w)


-- | A value permission is a permission to do something with a value, such as
-- use it as a pointer. This also includes a limited set of predicates on values
-- (you can think about this as "permission to assume the value satisfies this
-- predicate" if you like).
data ValuePerm (a :: CrucibleType) where

  -- | Says that a value is equal to a known static expression
  ValPerm_Eq :: PermExpr a -> ValuePerm a

  -- | The disjunction of two value permissions
  ValPerm_Or :: ValuePerm a -> ValuePerm a -> ValuePerm a

  -- | An existential binding of a value in a value permission
  --
  -- FIXME: turn the 'KnownRepr' constraint into a normal 'TypeRepr' argument
  ValPerm_Exists :: KnownRepr TypeRepr a =>
                    Binding a (ValuePerm b) ->
                    ValuePerm b

  -- | A named recursive permission
  ValPerm_Rec :: RecPermName args a -> RecPermArgs args -> ValuePerm a

  -- | A separating conjuction of 0 or more atomic permissions, where 0
  -- permissions is the trivially true permission
  ValPerm_Conj :: [AtomicPerm a] -> ValuePerm a


-- | The vacuously true permission is the conjunction of 0 atomic permissions
pattern ValPerm_True :: ValuePerm a
pattern ValPerm_True = ValPerm_Conj []

-- | The conjunction of exactly 1 atomic permission
pattern ValPerm_Conj1 :: AtomicPerm a -> ValuePerm a
pattern ValPerm_Conj1 p = ValPerm_Conj [p]

-- | A sequence of value permissions
data ValuePerms as where
  ValPerms_Nil :: ValuePerms RNil
  ValPerms_Cons :: ValuePerms as -> ValuePerm a -> ValuePerms (as :> a)

-- | A binding of 0 or more variables, each with permissions
type MbValuePerms ctx = Mb ctx (ValuePerms ctx)

-- | A frame permission is a list of the pointers that have been allocated in
-- the frame and their corresponding allocation sizes in words of size
-- @w@. Write permissions of the given sizes are required to these pointers in
-- order to delete the frame.
type LLVMFramePerm w = [(PermExpr (LLVMPointerType w), Integer)]

-- | An LLVM pointer permission is an 'AtomicPerm' of type 'LLVMPointerType'
type LLVMPtrPerm w = AtomicPerm (LLVMPointerType w)

-- | A permission for a pointer to a specific field
data LLVMFieldPerm w =
  LLVMFieldPerm { llvmFieldRW :: PermExpr RWModalityType,
                  -- ^ Whether this is a read or write permission
                  llvmFieldLifetime :: PermExpr LifetimeType,
                  -- ^ The lifetime during with this field permission is active
                  llvmFieldOffset :: PermExpr (BVType w),
                  -- ^ The offset from the pointer in bytes of this field
                  llvmFieldContents :: ValuePerm (LLVMPointerType w)
                  -- ^ The permissions we get for the value read from this field
                }
  deriving Eq

-- | Helper type to represent byte offsets
--
-- > 'machineWordBytes' * (stride * ix + fld_num)
--
-- from the beginning of an array permission. Such an expression refers to the
-- array field @fld_num@, which must be a statically-known constant, in array
-- cell @ix@.
data LLVMArrayIndex w =
  LLVMArrayIndex { llvmArrayIndexCell :: PermExpr (BVType w),
                   llvmArrayIndexFieldNum :: Int }

-- NOTE: we need a custom instance of Eq so we can use bvEq on the cell
instance Eq (LLVMArrayIndex w) where
  LLVMArrayIndex e1 i1 == LLVMArrayIndex e2 i2 =
    bvEq e1 e2 && i1 == i2

-- | A permission to an array of repeated field permissions. An array permission
-- is structured as zero or more cells, each of which are composed of one or
-- more individual fields. The number of cells can be a dynamic expression, but
-- the size in memory of each cell, called the /stride/ of the array, must be
-- statically known and no less than the total number of fields times the
-- machine word size.
data LLVMArrayPerm w =
  LLVMArrayPerm { llvmArrayOffset :: PermExpr (BVType w),
                  -- ^ The offset from the pointer in bytes of this array
                  llvmArrayLen :: PermExpr (BVType w),
                  -- ^ The number of array blocks
                  llvmArrayStride :: Integer,
                  -- ^ The array stride in words of length @w@
                  llvmArrayFields :: [LLVMFieldPerm w],
                  -- ^ The fields in each element of this array; should have
                  -- length <= the stride
                  llvmArrayBorrows :: [LLVMArrayBorrow w]
                  -- ^ Indices or index ranges that are missing from this array
                }
  deriving Eq

-- | An index or range of indices that are missing from an array perm
--
-- FIXME: think about calling the just @LLVMArrayIndexSet@
data LLVMArrayBorrow w
  = FieldBorrow (LLVMArrayIndex w)
    -- ^ Borrow a specific field in a specific cell of an array permission
  | RangeBorrow (BVRange w)
    -- ^ Borrow a range of array cells
  deriving Eq


-- | A function permission is a set of input and output permissions inside a
-- context of ghost variables, including a lifetime ghost variable. The input
-- and output permissions are only over the "real" arguments (including the
-- return value in the latter case); ghost arguments do not get permissions.
data FunPerm ghosts args ret where
  FunPerm :: CruCtx ghosts -> CruCtx args -> TypeRepr ret ->
             Mb (ghosts :> LifetimeType) (MbValuePerms args) ->
             Mb (ghosts :> LifetimeType) (MbValuePerms (args :> ret)) ->
             FunPerm ghosts args ret

-- | Extract the @args@ context from a function permission
funPermArgs :: FunPerm ghosts args ret -> CruCtx args
funPermArgs (FunPerm _ args _ _ _) = args

-- | Extract the @ghosts@ context from a function permission
funPermGhosts :: FunPerm ghosts args ret -> CruCtx ghosts
funPermGhosts (FunPerm ghosts _ _ _ _) = ghosts

-- | Extract the return type from a function permission
funPermRet :: FunPerm ghosts args ret -> TypeRepr ret
funPermRet (FunPerm _ _ ret _ _) = ret

-- | Extract the input permissions of a function permission
funPermIns :: FunPerm ghosts args ret ->
              Mb (ghosts :> LifetimeType) (MbValuePerms args)
funPermIns (FunPerm _ _ _ perms_in _) = perms_in

-- | Extract the output permissions of a function permission
funPermOuts :: FunPerm ghosts args ret ->
               Mb (ghosts :> LifetimeType) (MbValuePerms (args :> ret))
funPermOuts (FunPerm _ _ _ _ perms_out) = perms_out


-- | A name for a recursive permission
data RecPermName args a = RecPermName {
  recPermNameName :: String,
  recPermNameType :: TypeRepr a,
  recPermNameArgs :: CruCtx args
  }

-- | Test if two 'RecPermName's of possibly different types are equal
testRecPermNameEq :: RecPermName args1 a1 -> RecPermName args2 a2 ->
                     Maybe (args1 :~: args2, a1 :~: a2)
testRecPermNameEq (RecPermName str1 tp1 ctx1) (RecPermName str2 tp2 ctx2)
  | Just Refl <- testEquality tp1 tp2
  , Just Refl <- testEquality ctx1 ctx2
  , str1 == str2 = Just (Refl, Refl)
testRecPermNameEq _ _ = Nothing

instance Eq (RecPermName args a) where
  n1 == n2 | Just (Refl, Refl) <- testRecPermNameEq n1 n2 = True
  _ == _ = False

-- | An existentially quantified 'RecPermName'
data SomeRecPermName where
  SomeRecPermName :: RecPermName args a -> SomeRecPermName

-- | An argument for a recursive permission
data RecPermArg a where
  RecPermArg_Lifetime :: PermExpr LifetimeType -> RecPermArg LifetimeType
  RecPermArg_RWModality :: PermExpr RWModalityType ->
                           RecPermArg RWModalityType

instance TestEquality RecPermArg where
  testEquality (RecPermArg_Lifetime l1) (RecPermArg_Lifetime l2)
    | l1 == l2 = Just Refl
  testEquality (RecPermArg_RWModality rw1) (RecPermArg_RWModality rw2)
    | rw1 == rw2 = Just Refl
  testEquality _ _ = Nothing

instance Eq (RecPermArg a) where
  arg1 == arg2 | Just Refl <- testEquality arg1 arg2 = True
  _ == _ = False

-- | A sequence of 'RecPermArg's
data RecPermArgs (args :: RList CrucibleType) where
  RecPermArgs_Nil :: RecPermArgs RNil
  RecPermArgs_Cons :: RecPermArgs as -> RecPermArg a -> RecPermArgs (as :> a)

-- | Convert a 'RecPermArg' to an expression
permArgToExpr :: RecPermArg a -> PermExpr a
permArgToExpr (RecPermArg_Lifetime l) = l
permArgToExpr (RecPermArg_RWModality rw) = rw

-- | Convert a sequence of 'RecPermArg's to expressions
permArgsToExprs :: RecPermArgs args -> PermExprs args
permArgsToExprs RecPermArgs_Nil = PExprs_Nil
permArgsToExprs (RecPermArgs_Cons args arg) =
  PExprs_Cons (permArgsToExprs args) (permArgToExpr arg)

-- | Get the @n@th argument in a 'RecPermArgs' list
getRecPermArg :: RecPermArgs args -> Member args a -> RecPermArg a
getRecPermArg (RecPermArgs_Cons _ arg) Member_Base = arg
getRecPermArg (RecPermArgs_Cons args _) (Member_Step memb) =
  getRecPermArg args memb

-- | Set the @n@th argument in a 'RecPermArgs' list
setRecPermArg :: RecPermArgs args -> Member args a -> RecPermArg a ->
                 RecPermArgs args
setRecPermArg (RecPermArgs_Cons args _) Member_Base a = RecPermArgs_Cons args a
setRecPermArg (RecPermArgs_Cons args arg) (Member_Step memb) a =
  RecPermArgs_Cons (setRecPermArg args memb a) arg

-- | Get a list of 'Member' proofs for each arg in a 'RecPermArgs' sequence
getRecPermsMembers :: RecPermArgs args ->
                      [Some (Member args :: CrucibleType -> Type)]
getRecPermsMembers RecPermArgs_Nil = []
getRecPermsMembers (RecPermArgs_Cons args _) =
  map (\case Some memb -> Some (Member_Step memb)) (getRecPermsMembers args)
  ++ [Some Member_Base]

instance TestEquality RecPermArgs where
  testEquality (RecPermArgs_Cons args1 arg1) (RecPermArgs_Cons args2 arg2)
    | Just Refl <- testEquality args1 args2
    , Just Refl <- testEquality arg1 arg2
    = Just Refl
  testEquality RecPermArgs_Nil RecPermArgs_Nil = Just Refl
  testEquality _ _ = Nothing

instance Eq (RecPermArgs args) where
  args1 == args2 | Just Refl <- testEquality args1 args2 = True
  _ == _ = False

-- | A recursive permission is a disjunction of 1 or more permissions, each of
-- which can contain the recursive permission itself. NOTE: it is an error to
-- have an empty list of cases. A recursive permission is also associated with a
-- SAW datatype, given by a SAW 'Ident', and each disjunctive permission case is
-- associated with a constructor of that datatype.
data RecPerm args a = RecPerm {
  recPermName :: RecPermName args a,
  recPermDataType :: Ident,
  recPermFoldFun :: Ident,
  recPermUnfoldFun :: Ident,
  recPermCases :: [(Mb args (ValuePerm a), Ident)]
  }

-- | A list of "distinguished" permissions to named variables
-- FIXME: just call these VarsAndPerms or something like that...
data DistPerms ps where
  DistPermsNil :: DistPerms RNil
  DistPermsCons :: DistPerms ps -> ExprVar a -> ValuePerm a ->
                   DistPerms (ps :> a)

type MbDistPerms ps = Mb ps (DistPerms ps)

-- | A special-purpose 'DistPerms' that specifies a list of permissions needed
-- to prove that a lifetime is current
data LifetimeCurrentPerms ps_l where
  -- | The @always@ lifetime needs no proof that it is current
  AlwaysCurrentPerms :: LifetimeCurrentPerms RNil
  -- | A variable @l@ that is @lowned@ is current, requiring perms
  --
  -- > l:lowned(ps)
  LOwnedCurrentPerms :: ExprVar LifetimeType -> PermExpr PermListType ->
                        LifetimeCurrentPerms (RNil :> LifetimeType)

  -- | A variable @l@ that is @lcurrent@ during another lifetime @l'@ is
  -- current, i.e., if @ps@ ensure @l'@ is current then we need perms
  --
  -- > ps, l:lcurrent(l')
  CurrentTransPerms :: LifetimeCurrentPerms ps_l -> ExprVar LifetimeType ->
                       LifetimeCurrentPerms (ps_l :> LifetimeType)

-- | Get the lifetime that a 'LifetimeCurrentPerms' is about
lifetimeCurrentPermsLifetime :: LifetimeCurrentPerms ps_l ->
                                PermExpr LifetimeType
lifetimeCurrentPermsLifetime AlwaysCurrentPerms = PExpr_Always
lifetimeCurrentPermsLifetime (LOwnedCurrentPerms l _) = PExpr_Var l
lifetimeCurrentPermsLifetime (CurrentTransPerms _ l) = PExpr_Var l

-- | Convert a 'LifetimeCurrentPerms' to the 'DistPerms' it represent
lifetimeCurrentPermsPerms :: LifetimeCurrentPerms ps_l -> DistPerms ps_l
lifetimeCurrentPermsPerms AlwaysCurrentPerms = DistPermsNil
lifetimeCurrentPermsPerms (LOwnedCurrentPerms l ps) =
  DistPermsCons DistPermsNil l $ ValPerm_Conj1 $ Perm_LOwned ps
lifetimeCurrentPermsPerms (CurrentTransPerms cur_ps l) =
  DistPermsCons (lifetimeCurrentPermsPerms cur_ps) l $
  ValPerm_Conj1 $ Perm_LCurrent $ lifetimeCurrentPermsLifetime cur_ps

-- | Build a lift of proxies for a 'LifetimeCurrentPerms'
mbLifetimeCurrentPermsProxies :: Mb ctx (LifetimeCurrentPerms ps_l) ->
                                 MapRList Proxy ps_l
mbLifetimeCurrentPermsProxies [nuP| AlwaysCurrentPerms |] = MNil
mbLifetimeCurrentPermsProxies [nuP| LOwnedCurrentPerms _ _ |] = MNil :>: Proxy
mbLifetimeCurrentPermsProxies [nuP| CurrentTransPerms cur_ps _ |] =
  mbLifetimeCurrentPermsProxies cur_ps :>: Proxy

instance TestEquality DistPerms where
  testEquality DistPermsNil DistPermsNil = Just Refl
  testEquality (DistPermsCons ps1 x1 p1) (DistPermsCons ps2 x2 p2)
    | Just Refl <- testEquality ps1 ps2
    , Just Refl <- testEquality x1 x2
    , p1 == p2
    = Just Refl
  testEquality _ _ = Nothing

instance Eq (DistPerms ps) where
  perms1 == perms2 =
    case testEquality perms1 perms2 of
      Just _ -> True
      Nothing -> False

-- FIXME: move to Hobbits!
instance Eq a => Eq (Mb ctx a) where
  mb1 == mb2 =
    mbLift $ nuMultiWithElim (\_ (_ :>: a1 :>: a2) ->
                               a1 == a2) (MNil :>: mb1 :>: mb2)

instance Eq (ValuePerm a) where
  (ValPerm_Eq e1) == (ValPerm_Eq e2) = e1 == e2
  (ValPerm_Eq _) == _ = False
  (ValPerm_Or p1 p1') == (ValPerm_Or p2 p2') = p1 == p2 && p1' == p2'
  (ValPerm_Or _ _) == _ = False
  (ValPerm_Exists (p1 :: Binding a1 _)) == (ValPerm_Exists (p2 :: Binding a2 _))
    | Just Refl <-
        testEquality (knownRepr :: TypeRepr a1) (knownRepr :: TypeRepr a2)
    = p1 == p2
  (ValPerm_Exists _) == _ = False
  (ValPerm_Rec n1 args1) == (ValPerm_Rec n2 args2)
    | Just (Refl, Refl) <- testRecPermNameEq n1 n2 = args1 == args2
  (ValPerm_Rec _ _) == _ = False
  (ValPerm_Conj aps1) == (ValPerm_Conj aps2) = aps1 == aps2
  (ValPerm_Conj _) == _ = False

instance Eq (AtomicPerm a) where
  (Perm_LLVMField fp1) == (Perm_LLVMField fp2) = fp1 == fp2
  (Perm_LLVMField _) == _ = False
  (Perm_LLVMArray ap1) == (Perm_LLVMArray ap2) = ap1 == ap2
  (Perm_LLVMArray _) == _ = False
  (Perm_LLVMFree e1) == (Perm_LLVMFree e2) = e1 == e2
  (Perm_LLVMFree _) == _ = False
  (Perm_LLVMFunPtr fperm1) == (Perm_LLVMFunPtr fperm2)
    | Just Refl <- testEquality (funPermArgs fperm1) (funPermArgs fperm2)
    , Just Refl <- testEquality (funPermRet fperm1) (funPermRet fperm2)
    , Just Refl <- funPermEq fperm1 fperm2 = True
  (Perm_LLVMFunPtr _) == _ = False
  Perm_IsLLVMPtr == Perm_IsLLVMPtr = True
  Perm_IsLLVMPtr == _ = False
  (Perm_LLVMFrame frame1) == (Perm_LLVMFrame frame2) = frame1 == frame2
  (Perm_LLVMFrame _) == _ = False
  (Perm_LOwned e1) == (Perm_LOwned e2) = e1 == e2
  (Perm_LOwned _) == _ = False
  (Perm_LCurrent e1) == (Perm_LCurrent e2) = e1 == e2
  (Perm_LCurrent _) == _ = False
  (Perm_Fun fperm1) == (Perm_Fun fperm2)
    | Just Refl <- funPermEq fperm1 fperm2 = True
  (Perm_Fun _) == _ = False
  (Perm_BVProp p1) == (Perm_BVProp p2) = p1 == p2
  (Perm_BVProp _) == _ = False

instance Eq (ValuePerms as) where
  ValPerms_Nil == ValPerms_Nil = True
  (ValPerms_Cons ps1 p1) == (ValPerms_Cons ps2 p2) =
    ps1 == ps2 && p1 == p2

-- | Test if function permissions with different ghost argument lists are equal
funPermEq :: FunPerm ghosts1 args ret -> FunPerm ghosts2 args ret ->
             Maybe (ghosts1 :~: ghosts2)
funPermEq (FunPerm ghosts1 _ _ perms_in1 perms_out1)
  (FunPerm ghosts2 _ _ perms_in2 perms_out2)
  | Just Refl <- testEquality ghosts1 ghosts2
  , perms_in1 == perms_in2 && perms_out1 == perms_out2
  = Just Refl
funPermEq _ _ = Nothing

-- | Test if function permissions with all 3 type args different are equal
funPermEq3 :: FunPerm ghosts1 args1 ret1 -> FunPerm ghosts2 args2 ret2 ->
              Maybe (ghosts1 :~: ghosts2, args1 :~: args2, ret1 :~: ret2)
funPermEq3 (FunPerm ghosts1 args1 ret1 perms_in1 perms_out1)
  (FunPerm ghosts2 args2 ret2 perms_in2 perms_out2)
  | Just Refl <- testEquality ghosts1 ghosts2
  , Just Refl <- testEquality args1 args2
  , Just Refl <- testEquality ret1 ret2
  , perms_in1 == perms_in2 && perms_out1 == perms_out2
  = Just (Refl, Refl, Refl)
funPermEq3 _ _ = Nothing

instance Eq (FunPerm ghosts args ret) where
  fperm1 == fperm2 = isJust (funPermEq fperm1 fperm2)

instance PermPretty (RecPermName args a) where
  permPrettyM (RecPermName str _ _) = return $ string str

instance PermPretty (ValuePerm a) where
  permPrettyM (ValPerm_Eq e) = ((string "eq" <>) . parens) <$> permPrettyM e
  permPrettyM (ValPerm_Or p1 p2) =
    -- FIXME: If we ever fix the SAW lexer to handle "\/"...
    -- (\pp1 pp2 -> hang 2 (pp1 </> string "\\/" <> pp2))
    (\pp1 pp2 -> hang 2 (pp1 </> string "or" <+> pp2))
    <$> permPrettyM p1 <*> permPrettyM p2
  permPrettyM (ValPerm_Exists mb_p) =
    flip permPrettyExprMb mb_p $ \(_ :>: Constant pp_n) ppm ->
    (\pp -> hang 2 (string "exists" <+> pp_n <> dot <+> pp)) <$> ppm
  permPrettyM (ValPerm_Rec n args) =
    do n_pp <- permPrettyM n
       args_pp <- permPrettyM args
       return (n_pp <> char '<' <> args_pp <> char '>')
  permPrettyM ValPerm_True = return $ string "true"
  permPrettyM (ValPerm_Conj ps) =
    (hang 2 . encloseSep PP.empty PP.empty (string "*")) <$> mapM permPrettyM ps

-- | Pretty-print an 'LLVMFieldPerm', either by itself as the form
-- @[l]ptr((rw,off) |-> p)@ if the 'Bool' flag is 'False' or as part of an array
-- permission as the form @[l](rw,off) |-> p@ if the 'Bool' flag is 'True'
permPrettyLLVMField :: Bool -> LLVMFieldPerm w -> PermPPM Doc
permPrettyLLVMField in_array (LLVMFieldPerm {..}) =
  do pp_l <-
       if llvmFieldLifetime == PExpr_Always then return (string "")
       else brackets <$> permPrettyM llvmFieldLifetime
     pp_off <- permPrettyM llvmFieldOffset
     pp_rw <- permPrettyM llvmFieldRW
     pp_contents <- permPrettyM llvmFieldContents
     return (pp_l <>
             (if in_array then id else (string "ptr" <>) . parens)
             (parens (pp_rw <> comma <> pp_off) </>
              string "|->" </> pp_contents))

instance PermPretty (AtomicPerm a) where
  permPrettyM (Perm_LLVMField fp) = permPrettyLLVMField False fp
  permPrettyM (Perm_LLVMArray (LLVMArrayPerm {..})) =
    do pp_off <- permPrettyM llvmArrayOffset
       pp_len <- permPrettyM llvmArrayLen
       let pp_stride = string (show llvmArrayStride)
       pp_flds <- mapM (permPrettyLLVMField True) llvmArrayFields
       pp_bs <- mapM permPrettyM llvmArrayBorrows
       return (string "array" <>
               parens (sep [pp_off, string "<" <> pp_len,
                            string "*" <> pp_stride,
                            list pp_flds, list pp_bs]))
  permPrettyM (Perm_LLVMFree e) = (string "free" <+>) <$> permPrettyM e
  permPrettyM (Perm_LLVMFunPtr fp) =
    (string "llvm_funptr" <+>) <$> permPrettyM fp
  permPrettyM Perm_IsLLVMPtr = return (string "is_llvmptr")
  permPrettyM (Perm_LLVMFrame fperm) =
    do pps <- mapM (\(e,i) -> (<> (colon <> integer i)) <$> permPrettyM e) fperm
       return (string "LLVMframe" <+> list pps)
  permPrettyM (Perm_LOwned ps) = (string "lowned" <+>) <$> permPrettyM ps
  permPrettyM (Perm_LCurrent l) = (string "lcurrent" <+>) <$> permPrettyM l
  permPrettyM (Perm_Fun fun_perm) = permPrettyM fun_perm
  permPrettyM (Perm_BVProp prop) = permPrettyM prop

instance PermPretty (FunPerm ghosts args ret) where
  permPrettyM fun_perm =
    return $ string "<FunPerm (FIXME)>" -- FIXME HERE: implement

instance PermPretty (RecPermArgs args) where
  permPrettyM RecPermArgs_Nil = return $ string ""
  permPrettyM (RecPermArgs_Cons RecPermArgs_Nil arg) = permPrettyM arg
  permPrettyM (RecPermArgs_Cons args arg) =
    (\pp1 pp2 -> pp1 <> comma <> pp2) <$> permPrettyM args <*> permPrettyM arg

instance PermPretty (RecPermArg a) where
  permPrettyM (RecPermArg_Lifetime l) = permPrettyM l
  permPrettyM (RecPermArg_RWModality rw) = permPrettyM rw

instance PermPretty (BVRange w) where
  permPrettyM (BVRange e1 e2) =
    (\pp1 pp2 -> braces (pp1 <> comma <+> pp2))
    <$> permPrettyM e1 <*> permPrettyM e2

instance PermPretty (BVProp w) where
  permPrettyM (BVProp_Eq e1 e2) =
    (\pp1 pp2 -> pp1 <+> equals <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_Neq e1 e2) =
    (\pp1 pp2 -> pp1 <+> string "/=" <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_InRange e rng) =
    (\pp1 pp2 -> pp1 <+> string "in" <+> pp2)
    <$> permPrettyM e <*> permPrettyM rng
  permPrettyM (BVProp_RangeSubset rng1 rng2) =
    (\pp1 pp2 -> pp1 <+> string "subset" <+> pp2)
    <$> permPrettyM rng1 <*> permPrettyM rng2
  permPrettyM (BVProp_RangesDisjoint rng1 rng2) =
    (\pp1 pp2 -> pp1 <+> string "disjoint" <+> pp2)
    <$> permPrettyM rng1 <*> permPrettyM rng2

instance PermPretty (LLVMArrayBorrow w) where
  permPrettyM (FieldBorrow (LLVMArrayIndex ix fld_num)) =
    do pp_ix <- permPrettyM ix
       let pp_fld_num = string (show fld_num)
       return (parens pp_ix <> string "." <> pp_fld_num)
  permPrettyM (RangeBorrow rng) = permPrettyM rng

instance PermPretty (DistPerms ps) where
  permPrettyM ps = encloseSep PP.empty PP.empty comma <$> helper ps where
    helper :: DistPerms ps' -> PermPPM [Doc]
    helper DistPermsNil = return []
    helper (DistPermsCons ps x p) =
      do x_pp <- permPrettyM x
         p_pp <- permPrettyM p
         (++ [x_pp <> colon <> p_pp]) <$> helper ps


$(mkNuMatching [t| forall a . PermExpr a |])
$(mkNuMatching [t| forall a . BVFactor a |])
$(mkNuMatching [t| forall as . PermExprs as |])
$(mkNuMatching [t| forall w. BVRange w |])
$(mkNuMatching [t| forall w. BVProp w |])
$(mkNuMatching [t| forall a . AtomicPerm a |])
$(mkNuMatching [t| forall a . ValuePerm a |])
$(mkNuMatching [t| forall as. ValuePerms as |])
$(mkNuMatching [t| forall w . LLVMFieldPerm w |])
$(mkNuMatching [t| forall w . LLVMArrayPerm w |])
$(mkNuMatching [t| RWModality |])
$(mkNuMatching [t| forall w . LLVMArrayIndex w |])
$(mkNuMatching [t| forall w . LLVMArrayBorrow w |])
$(mkNuMatching [t| forall ghosts args ret. FunPerm ghosts args ret |])
$(mkNuMatching [t| forall args a. RecPermName args a |])
$(mkNuMatching [t| SomeRecPermName |])
$(mkNuMatching [t| forall a. RecPermArg a |])
$(mkNuMatching [t| forall args. RecPermArgs args |])
$(mkNuMatching [t| forall args a. RecPerm args a |])
$(mkNuMatching [t| forall ps. DistPerms ps |])
$(mkNuMatching [t| forall ps. LifetimeCurrentPerms ps |])

instance NuMatchingAny1 DistPerms where
  nuMatchingAny1Proof = nuMatchingProof

instance Liftable RWModality where
  mbLift [nuP| Write |] = Write
  mbLift [nuP| Read |] = Read

instance Closable RWModality where
  toClosed Write = $(mkClosed [| Write |])
  toClosed Read = $(mkClosed [| Read |])

instance Liftable (RecPermName args a) where
  mbLift [nuP| RecPermName n tp args |] =
    RecPermName (mbLift n) (mbLift tp) (mbLift args)

instance Liftable SomeRecPermName where
  mbLift [nuP| SomeRecPermName rpn |] = SomeRecPermName $ mbLift rpn

-- | Extract @p1@ from a permission of the form @p1 \/ p2@
orPermLeft :: ValuePerm a -> ValuePerm a
orPermLeft (ValPerm_Or p _) = p
orPermLeft _ = error "orPermLeft"

-- | Extract @p2@ from a permission of the form @p1 \/ p2@
orPermRight :: ValuePerm a -> ValuePerm a
orPermRight (ValPerm_Or _ p) = p
orPermRight _ = error "orPermRight"

-- | Extract the body @p@ from a permission of the form @exists (x:tp).p@
exPermBody :: TypeRepr tp -> ValuePerm a -> Binding tp (ValuePerm a)
exPermBody tp (ValPerm_Exists (p :: Binding tp' (ValuePerm a)))
  | Just Refl <- testEquality tp (knownRepr :: TypeRepr tp') = p
exPermBody _ _ = error "exPermBody"

-- | Test if an 'AtomicPerm' is a field permission
isLLVMFieldPerm :: AtomicPerm (LLVMPointerType w) -> Bool
isLLVMFieldPerm (Perm_LLVMField _) = True
isLLVMFieldPerm _ = False

-- | Test if an 'AtomicPerm' is an array permission
isLLVMArrayPerm :: AtomicPerm (LLVMPointerType w) -> Bool
isLLVMArrayPerm (Perm_LLVMArray _) = True
isLLVMArrayPerm _ = False

-- | Existential permission @x:eq(word(e))@ for some @e@
llvmExEqWord :: (1 <= w, KnownNat w) =>
                Binding (BVType w) (ValuePerm (LLVMPointerType w))
llvmExEqWord = nu $ \e -> ValPerm_Eq (PExpr_LLVMWord $ PExpr_Var e)

{-
-- | Create a field pointer permission with offset 0 and @eq(e)@ permissions
-- with the given read-write modality
llvmFieldContents0Eq :: (1 <= w, KnownNat w) =>
                    RWModality -> PermExpr (LLVMPointerType w) ->
                    LLVMPtrPerm w
llvmFieldContents0Eq rw e =
  Perm_LLVMField $ LLVMFieldPerm { llvmFieldRW = rw,
                                   llvmFieldOffset = bvInt 0,
                                   llvmFieldContents = ValPerm_Eq e }
-}

-- | Create a permission to read a known value from offset 0 of an LLVM pointer
-- in the given lifetime, i.e., return @exists y.[l]ptr ((0,R) |-> eq(e))@
llvmRead0EqPerm :: (1 <= w, KnownNat w) => PermExpr LifetimeType ->
                    PermExpr (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w)
llvmRead0EqPerm l e =
  ValPerm_Conj [Perm_LLVMField $
                LLVMFieldPerm { llvmFieldRW = PExpr_Read,
                                llvmFieldLifetime = l,
                                llvmFieldOffset = bvInt 0,
                                llvmFieldContents = ValPerm_Eq e }]

-- | Create a field write permission with offset 0 and @true@ permissions
llvmFieldWrite0True :: (1 <= w, KnownNat w) => LLVMFieldPerm w
llvmFieldWrite0True =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = PExpr_Always,
                  llvmFieldOffset = bvInt 0,
                  llvmFieldContents = ValPerm_True }

-- | Create a field write permission with offset 0 and @true@ permissions
llvmWrite0TruePerm :: (1 <= w, KnownNat w) => ValuePerm (LLVMPointerType w)
llvmWrite0TruePerm = ValPerm_Conj [Perm_LLVMField llvmFieldWrite0True]

-- | Create a field write permission with offset 0 and an @eq(e)@ permission
llvmFieldWrite0Eq :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                     LLVMFieldPerm w
llvmFieldWrite0Eq e =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = PExpr_Always,
                  llvmFieldOffset = bvInt 0,
                  llvmFieldContents = ValPerm_Eq e }

-- | Create a field write permission with offset 0 and an @eq(e)@ permission
llvmWrite0EqPerm :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w)
llvmWrite0EqPerm e = ValPerm_Conj [Perm_LLVMField $ llvmFieldWrite0Eq e]

-- | Create a field write permission with offset @e@ and lifetime @l@
llvmFieldWriteTrueL :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                      PermExpr LifetimeType -> LLVMFieldPerm w
llvmFieldWriteTrueL off l =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = l,
                  llvmFieldOffset = off,
                  llvmFieldContents = ValPerm_True }

-- | Create a field write permission with offset @e@ and an existential lifetime
llvmWriteTrueExLPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                        Binding LifetimeType (ValuePerm (LLVMPointerType w))
llvmWriteTrueExLPerm off =
  nu $ \l ->
  ValPerm_Conj1 $ Perm_LLVMField $ llvmFieldWriteTrueL off (PExpr_Var l)

-- | Create a field permission with offset @e@ and existential lifetime and rw
llvmReadExRWExLPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                       Mb (RNil :> RWModalityType :> LifetimeType)
                       (ValuePerm (LLVMPointerType w))
llvmReadExRWExLPerm off =
  nuMulti (MNil :>: Proxy :>: Proxy) $ \(_ :>: rw :>: l) ->
  ValPerm_Conj1 $ Perm_LLVMField $
  LLVMFieldPerm { llvmFieldRW = PExpr_Var rw,
                  llvmFieldLifetime = PExpr_Var l,
                  llvmFieldOffset = off,
                  llvmFieldContents = ValPerm_True }

-- | Return the clopen range @[0,len)@ of the indices of an array permission
llvmArrayIndexRange :: (1 <= w, KnownNat w) => LLVMArrayPerm w -> BVRange w
llvmArrayIndexRange ap = BVRange (bvInt 0) (llvmArrayLen ap)

-- | Return the range of the byte offsets of an array permission
{-
llvmArrayRangeBytes :: (1 <= w, KnownNat w) => LLVMArrayPerm w -> BVRange w
llvmArrayRangeBytes ap = BVRange (llvmArrayOffset ap) (arrayLengthBytes ap)
-}

-- | Return the number of bytes per machine word; @w@ is the number of bits
machineWordBytes :: KnownNat w => f w -> Integer
machineWordBytes w
  | natVal w `mod` 8 /= 0 =
    error "machineWordBytes: word size is not a multiple of 8!"
machineWordBytes w = natVal w `div` 8

-- | Convert bytes to machine words, rounded up, i.e., return @ceil(n/W)@,
-- where @W@ is the number of bytes per machine word
bytesToMachineWords :: KnownNat w => f w -> Integer -> Integer
bytesToMachineWords w n = (n + machineWordBytes w - 1) `div` machineWordBytes w

{-
-- | Return an array stride in bytes, instead of words of size @w@
arrayStrideBytes :: KnownNat w => LLVMArrayPerm w -> Integer
arrayStrideBytes ap@(LLVMArrayPerm {..}) =
  llvmArrayStride * machineWordBytes ap

-- | Return the length of an array in bytes
arrayLengthBytes :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                    PermExpr (BVType w)
arrayLengthBytes ap = bvMult (arrayStrideBytes ap) (llvmArrayLen ap)
-}

-- | Add a borrow to an 'LLVMArrayPerm'
llvmArrayAddBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayAddBorrow b ap = ap { llvmArrayBorrows = b : llvmArrayBorrows ap }

-- | Find the position in the list of borrows of an 'LLVMArrayPerm' of a
-- specific borrow
llvmArrayFindBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> Int
llvmArrayFindBorrow b ap =
  case findIndex (== b) (llvmArrayBorrows ap) of
    Just i -> i
    Nothing -> error "llvmArrayFindBorrow: borrow not found"

-- | Remove a borrow from an 'LLVMArrayPerm'
llvmArrayRemBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayRemBorrow b ap =
  ap { llvmArrayBorrows =
         deleteNth (llvmArrayFindBorrow b ap) (llvmArrayBorrows ap) }

-- | Test if a byte offset @o@ statically aligns with a field in an array, i.e.,
-- whether
--
-- > o - off = wordBytes * (stride*ix + fld_num)
--
-- for some @ix@ and @fld_num@, where @off@ is the array offset and @stride@ is
-- the array stride. Return @ix@ and @fld_num@ on success.
matchLLVMArrayField :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                       PermExpr (BVType w) -> Maybe (LLVMArrayIndex w)
matchLLVMArrayField ap o
  | w <- machineWordBytes ap
  , rel_off <- bvSub o (llvmArrayOffset ap)
  , bvEq (bvMod rel_off w) (bvInt 0) =
    fmap (\(ix, fld_num) -> LLVMArrayIndex ix $ fromInteger fld_num) $
    bvMatchFactorPlusConst (llvmArrayStride ap) (bvDiv rel_off w)
matchLLVMArrayField _ _ = Nothing

-- | Return a 'BVProp' stating that the field(s) represented by an array borrow
-- are in the "base" set of fields in an array, before the borrows are
-- considered. We assume that the borrow is statically well-formed for that
-- array, meaning that the static field number of a 'FieldBorrow' refers to a
-- valid field in the array perm.
llvmArrayBorrowInArrayBase :: (1 <= w, KnownNat w) =>
                              LLVMArrayPerm w -> LLVMArrayBorrow w ->
                              BVProp w
llvmArrayBorrowInArrayBase ap (FieldBorrow ix)
  | llvmArrayIndexFieldNum ix >= length (llvmArrayFields ap) =
    error "llvmArrayBorrowInArrayBase: invalid index"
llvmArrayBorrowInArrayBase ap (FieldBorrow ix) =
  BVProp_InRange (llvmArrayIndexCell ix) (llvmArrayIndexRange ap)
llvmArrayBorrowInArrayBase ap (RangeBorrow rng) =
  BVProp_RangeSubset rng (llvmArrayIndexRange ap)

-- | Return a 'BVProp' stating that two array borrows are disjoint, or 'Nothing'
-- if they are trivially disjoint because they refer to statically distinct
-- field numbers
llvmArrayBorrowsDisjoint :: LLVMArrayBorrow w -> LLVMArrayBorrow w ->
                            Maybe (BVProp w)
llvmArrayBorrowsDisjoint (FieldBorrow ix1) (FieldBorrow ix2)
  | llvmArrayIndexFieldNum ix1 == llvmArrayIndexFieldNum ix2
  = Just (BVProp_Neq (llvmArrayIndexCell ix1) (llvmArrayIndexCell ix2))
llvmArrayBorrowsDisjoint (FieldBorrow _) (FieldBorrow _) = Nothing
llvmArrayBorrowsDisjoint (FieldBorrow ix) (RangeBorrow rng) =
  Just $ BVProp_NotInRange (llvmArrayIndexCell ix) rng
llvmArrayBorrowsDisjoint (RangeBorrow rng) (FieldBorrow ix) =
  Just $ BVProp_NotInRange (llvmArrayIndexCell ix) rng
llvmArrayBorrowsDisjoint (RangeBorrow rng1) (RangeBorrow rng2) =
  Just $ BVProp_RangesDisjoint rng1 rng2

-- | Return a list of propositions stating that the field(s) represented by an
-- array borrow are in the set of fields of an array permission. This takes into
-- account the current borrows on the array permission, which are fields that
-- are /not/ currently in that array permission.
llvmArrayBorrowInArray :: (1 <= w, KnownNat w) =>
                          LLVMArrayPerm w -> LLVMArrayBorrow w -> [BVProp w]
llvmArrayBorrowInArray ap b =
  llvmArrayBorrowInArrayBase ap b :
  mapMaybe (llvmArrayBorrowsDisjoint b) (llvmArrayBorrows ap)

-- | Shorthand for 'llvmArrayBorrowInArray' with a single index
llvmArrayIndexInArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                         LLVMArrayIndex w -> [BVProp w]
llvmArrayIndexInArray ap ix = llvmArrayBorrowInArray ap (FieldBorrow ix)

-- | Test if an atomic LLVM permission potentially allows a read or write of a
-- given offset. If so, return a list of the propositions required for the read
-- to be allowed. For LLVM field permissions, the offset of the field must
-- statically match the supplied offset, so the list of propositions will be
-- empty, while for arrays, the offset must only /not/ match any outstanding
-- borrows, and the propositions returned codify that as well as the requirement
-- that the offset is in the array range.
llvmPermContainsOffset :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                          AtomicPerm (LLVMPointerType w) -> Maybe [BVProp w]
llvmPermContainsOffset off (Perm_LLVMField fp)
  | bvEq (llvmFieldOffset fp) off = Just []
llvmPermContainsOffset off (Perm_LLVMArray ap)
  | Just ix <- matchLLVMArrayField ap off
  , props <- llvmArrayIndexInArray ap ix
  , all bvPropCouldHold props =
    Just props
llvmPermContainsOffset _ _ = Nothing

-- | Return the byte offset @'machineWordBytes' * (stride * cell + field_num)@
-- of an array index from the beginning of the array
llvmArrayIndexByteOffset :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayIndex w -> PermExpr (BVType w)
llvmArrayIndexByteOffset ap ix =
  bvMult (machineWordBytes ap) $
  bvAdd (bvMult (llvmArrayStride ap) (llvmArrayIndexCell ix))
  (bvInt (toInteger $ llvmArrayIndexFieldNum ix))

-- | Return the field permission corresponding to the given index an array
-- permission, offset by the array offset plus the byte offset of the field
llvmArrayFieldWithOffset :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayIndex w -> LLVMFieldPerm w
llvmArrayFieldWithOffset ap ix =
  offsetLLVMFieldPerm
  (bvAdd (llvmArrayOffset ap) (llvmArrayIndexByteOffset ap ix))
  (llvmArrayFields ap !! llvmArrayIndexFieldNum ix)


{- FIXME HERE: remove these...?

-- | Compute the byte index @wordSize*(i*stride + j)@ of the @j@th field in the
-- @i@th array element from the beginning of an array
llvmArrayIndex :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                  LLVMArrayIndex w -> Int -> PermExpr (BVType w)
llvmArrayIndex ap (LLVMArrayIndex i) j =
  bvAdd (bvMult (llvmArrayStride ap) i) (bvInt $ toInteger j)

-- | Convert the output of 'llvmArrayIndex' to a single-element 'BVRange'
llvmArrayIndexToRange :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                         PermExpr (BVType w) -> Int -> BVRange w
llvmArrayIndexToRange ap ix fld_num =
  bvRangeOfIndex $ llvmArrayIndex ap ix fld_num

-- | Get the range of byte offsets represented by an array borrow
llvmArrayBorrowRange :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                        LLVMArrayBorrow w -> BVRange w
llvmArrayBorrowRange ap (FieldBorrow ix fld_num) =
  llvmArrayIndexToRange ap ix fld_num
llvmArrayBorrowRange _ (RangeBorrow r) = r

-- | Test if a specific range of byte offsets from the beginning of an array
-- corresponds to a borrow already on an array
llvmArrayRangeIsBorrowed :: (1 <= w, KnownNat w) =>
                            LLVMArrayPerm w -> BVRange w -> Bool
llvmArrayRangeIsBorrowed ap rng =
  elem rng (map (llvmArrayBorrowRange ap) $ llvmArrayBorrows ap)

-- | Test if a specific array index and field number correspond to a borrow
-- already on an array
llvmArrayIndexIsBorrowed :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            PermExpr (BVType w) -> Int -> Bool
llvmArrayIndexIsBorrowed ap ix fld_num =
  llvmArrayRangeIsBorrowed ap $ llvmArrayIndexToRange ap ix fld_num

-- | Build 'BVProp's stating that each borrow in an array permission is disjoint
-- from an index or range
llvmArrayBorrowsDisjoint :: (1 <= w, KnownNat w) =>
                            LLVMArrayPerm w -> BVRange w -> [BVProp w]
llvmArrayBorrowsDisjoint ap range =
  map (BVProp_RangesDisjoint range . llvmArrayBorrowRange ap) $
  llvmArrayBorrows ap

-- | Search through a list of atomic permissions to see if one of them is an
-- LLVM array permission where the given field has been borrowed. If so, return
-- the index of the array permission in the list, the array permission itself,
-- and the index and field number of the field in the array
findLLVMArrayWithFieldBorrow :: (1 <= w, KnownNat w) => LLVMFieldPerm w ->
                                [AtomicPerm (LLVMPointerType w)] ->
                                Maybe (Int, LLVMArrayPerm w,
                                       PermExpr (BVType w), Int)
findLLVMArrayWithFieldBorrow _ [] = Nothing
findLLVMArrayWithFieldBorrow fp (Perm_LLVMArray ap : _)
  | Just (ix, fromInteger -> fld_num) <-
      bvMatchFactorPlusConst (llvmArrayStride ap)
      (bvSub (llvmFieldOffset fp) (llvmArrayOffset ap))
  , llvmArrayIndexIsBorrowed ap ix fld_num =
    Just (0, ap, ix, fld_num)
findLLVMArrayWithFieldBorrow fp (_ : ps) =
  fmap (\(i, ap, ix, fld_num) -> (i+1, ap, ix, fld_num)) $
  findLLVMArrayWithFieldBorrow fp ps
-}

-- | Create a list of field permissions the cover @N@ bytes:
--
-- > ptr((w,0) |-> true, (w,W) |-> true, ..., (w,W*(M-1)) |-> true)
--
-- where @W@ is the number of bytes per machine word and @M@ is the number of
-- machine words for @N@ bytes, rounded up
llvmFieldsOfSize :: (1 <= w, KnownNat w) => f w -> Integer -> [LLVMFieldPerm w]
llvmFieldsOfSize w n =
  map (\i -> llvmFieldWrite0True { llvmFieldOffset =
                                     bvInt (i * machineWordBytes w) })
  [0 .. bytesToMachineWords w n - 1]

-- | Return the permission built from the field permissions returned by
-- 'llvmFieldsOfSize'
llvmFieldsPermOfSize :: (1 <= w, KnownNat w) => f w -> Integer ->
                        ValuePerm (LLVMPointerType w)
llvmFieldsPermOfSize w n =
  ValPerm_Conj $ map Perm_LLVMField $ llvmFieldsOfSize w n

-- | Create the array ponter perm @array(0,<len,*1 |-> [ptr(0 |-> true)])@ of
-- size @len@ words of width @w@
llvmArrayPtrPermOfSize :: (1 <= w, KnownNat w) => Integer -> LLVMPtrPerm w
llvmArrayPtrPermOfSize len =
  Perm_LLVMArray $ LLVMArrayPerm { llvmArrayOffset = bvInt 0,
                                   llvmArrayLen = bvInt len,
                                   llvmArrayStride = 1,
                                   llvmArrayFields = [llvmFieldWrite0True],
                                   llvmArrayBorrows = [] }

-- | Like 'llvmArrayPtrPermOfSize', but return a 'ValuePerm' instead of a
-- pointer perm
llvmArrayPermOfSize :: (1 <= w, KnownNat w) => Integer ->
                       ValuePerm (LLVMPointerType w)
llvmArrayPermOfSize sz = ValPerm_Conj [llvmArrayPtrPermOfSize sz]

-- | Test if an LLVM pointer permission can be offset by the given offset; i.e.,
-- whether 'offsetLLVMAtomicPerm' returns a value
canOffsetLLVMAtomicPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                           LLVMPtrPerm w -> Bool
canOffsetLLVMAtomicPerm off p = isJust $ offsetLLVMAtomicPerm off p

-- | Add an offset to an LLVM pointer permission, returning 'Nothing' for
-- permissions like @free@ and @llvm_funptr@ that cannot be offset
offsetLLVMAtomicPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                        LLVMPtrPerm w -> Maybe (LLVMPtrPerm w)
offsetLLVMAtomicPerm (bvMatchConst -> Just 0) p = Just p
offsetLLVMAtomicPerm off (Perm_LLVMField fp) =
  Just $ Perm_LLVMField $ offsetLLVMFieldPerm off fp
offsetLLVMAtomicPerm off (Perm_LLVMArray ap) =
  Just $ Perm_LLVMArray $ offsetLLVMArrayPerm off ap
offsetLLVMAtomicPerm _ (Perm_LLVMFree _) = Nothing
offsetLLVMAtomicPerm _ (Perm_LLVMFunPtr _) = Nothing
offsetLLVMAtomicPerm _ p@Perm_IsLLVMPtr = Just p

-- | Add an offset to a field permission
offsetLLVMFieldPerm :: (1 <= w, KnownNat w) =>
                       PermExpr (BVType w) -> LLVMFieldPerm w -> LLVMFieldPerm w
offsetLLVMFieldPerm off (LLVMFieldPerm {..}) =
  LLVMFieldPerm { llvmFieldOffset = bvAdd llvmFieldOffset off, ..}

-- | Add an offset to an array permission
offsetLLVMArrayPerm :: (1 <= w, KnownNat w) =>
                       PermExpr (BVType w) -> LLVMArrayPerm w -> LLVMArrayPerm w
offsetLLVMArrayPerm off (LLVMArrayPerm {..}) =
  LLVMArrayPerm { llvmArrayOffset = bvAdd llvmArrayOffset off, ..}

-- | Lens for the atomic permissions in a 'ValPerm_Conj'; it is an error to use
-- this lens with a value permission not of this form
conjAtomicPerms :: Lens' (ValuePerm a) [AtomicPerm a]
conjAtomicPerms =
  lens
  (\p -> case p of
      ValPerm_Conj ps -> ps
      _ -> error "conjAtomicPerms: not a conjuction of atomic permissions")
  (\p ps ->
    case p of
      ValPerm_Conj _ -> ValPerm_Conj ps
      _ -> error "conjAtomicPerms: not a conjuction of atomic permissions")

-- | Lens for the @i@th atomic permission in a 'ValPerm_Conj'; it is an error to
-- use this lens with a value permission not of this form
conjAtomicPerm :: Int -> Lens' (ValuePerm a) (AtomicPerm a)
conjAtomicPerm i =
  lens
  (\p -> if i >= length (p ^. conjAtomicPerms) then
           error "conjAtomicPerm: index out of bounds"
         else (p ^. conjAtomicPerms) !! i)
  (\p pp ->
    -- FIXME: there has got to be a nicer, more lens-like way to do this
    let pps = p ^. conjAtomicPerms in
    if i >= length pps then
      error "conjAtomicPerm: index out of bounds"
    else set conjAtomicPerms (take i pps ++ (pp : drop (i+1) pps)) p)

-- | Add a new atomic permission to the end of the list of those contained in
-- the 'conjAtomicPerms' of a permission
addAtomicPerm :: AtomicPerm a -> ValuePerm a -> ValuePerm a
addAtomicPerm pp = over conjAtomicPerms (++ [pp])

-- | Delete the atomic permission at the given index from the list of those
-- contained in the 'conjAtomicPerms' of a permission
deleteAtomicPerm :: Int -> ValuePerm a -> ValuePerm a
deleteAtomicPerm i =
  over conjAtomicPerms (\pps ->
                         if i >= length pps then
                           error "deleteAtomicPerm: index out of bounds"
                         else take i pps ++ drop (i+1) pps)

-- | Lens for the LLVM pointer permissions in a 'ValPerm_Conj'; it is an error
-- to use this lens with a value permission not of this form
llvmPtrPerms :: Lens' (ValuePerm (LLVMPointerType w)) [LLVMPtrPerm w]
llvmPtrPerms = conjAtomicPerms

-- | Lens for the @i@th LLVM pointer permission of a 'ValPerm_Conj'
llvmPtrPerm :: Int -> Lens' (ValuePerm (LLVMPointerType w)) (LLVMPtrPerm w)
llvmPtrPerm = conjAtomicPerm

-- | Add a new 'LLVMPtrPerm' to the end of the list of those contained in the
-- 'llvmPtrPerms' of a permission
addLLVMPtrPerm :: LLVMPtrPerm w -> ValuePerm (LLVMPointerType w) ->
                  ValuePerm (LLVMPointerType w)
addLLVMPtrPerm pp = over llvmPtrPerms (++ [pp])

-- | Delete the 'LLVMPtrPerm' at the given index from the list of those
-- contained in the 'llvmPtrPerms' of a permission
deleteLLVMPtrPerm :: Int -> ValuePerm (LLVMPointerType w) ->
                     ValuePerm (LLVMPointerType w)
deleteLLVMPtrPerm i =
  over llvmPtrPerms (\pps ->
                      if i >= length pps then
                        error "deleteLLVMPtrPerm: index out of bounds"
                      else take i pps ++ drop (i+1) pps)

-- | Return the index of the last 'LLVMPtrPerm' of a permission
lastLLVMPtrPermIndex :: ValuePerm (LLVMPointerType w) -> Int
lastLLVMPtrPermIndex p =
  let len = length (p ^. llvmPtrPerms) in
  if len > 0 then len - 1 else error "lastLLVMPtrPerms: no pointer perms!"

-- | Create a list of pointer permissions needed in order to deallocate a frame
-- that has the given frame permissions. It is an error if any of the required
-- permissions are for LLVM words instead of pointers.
llvmFrameDeletionPerms :: (1 <= w, KnownNat w) => LLVMFramePerm w ->
                          Some DistPerms
llvmFrameDeletionPerms [] = Some DistPermsNil
llvmFrameDeletionPerms ((asLLVMOffset -> Just (x,off), sz):fperm')
  | Some del_perms <- llvmFrameDeletionPerms fperm' =
    Some $ DistPermsCons del_perms x $ ValPerm_Conj
    (map (Perm_LLVMField . offsetLLVMFieldPerm off) $
     llvmFieldsOfSize knownNat sz)
    -- [offsetLLVMAtomicPerm off $ llvmArrayPtrPermOfSize sz]
llvmFrameDeletionPerms _ =
  error "llvmFrameDeletionPerms: unexpected LLVM word allocated in frame"

-- | Build a 'DistPerms' with just one permission
distPerms1 :: ExprVar a -> ValuePerm a -> DistPerms (RNil :> a)
distPerms1 x p = DistPermsCons DistPermsNil x p

-- | Build a 'DistPerms' with two permissions
distPerms2 :: ExprVar a1 -> ValuePerm a1 ->
              ExprVar a2 -> ValuePerm a2 -> DistPerms (RNil :> a1 :> a2)
distPerms2 x1 p1 x2 p2 = DistPermsCons (distPerms1 x1 p1) x2 p2

-- | Get the first permission in a 'DistPerms'
distPermsHeadPerm :: DistPerms (ps :> a) -> ValuePerm a
distPermsHeadPerm (DistPermsCons _ _ p) = p

-- | Drop the last permission in a 'DistPerms'
distPermsSnoc :: DistPerms (ps :> a) -> DistPerms ps
distPermsSnoc (DistPermsCons ps _ _) = ps

-- | Map a function on permissions across a 'DistPerms'
mapDistPerms :: (forall a. ValuePerm a -> ValuePerm a) ->
                DistPerms ps -> DistPerms ps
mapDistPerms _ DistPermsNil = DistPermsNil
mapDistPerms f (DistPermsCons perms x p) =
  DistPermsCons (mapDistPerms f perms) x (f p)


-- | Create a sequence of @true@ permissions
trueValuePerms :: CruCtx ps -> ValuePerms ps
trueValuePerms CruCtxNil = ValPerms_Nil
trueValuePerms (CruCtxCons ctx _) =
  ValPerms_Cons (trueValuePerms ctx) ValPerm_True

-- | Append two lists of permissions
appendValuePerms :: ValuePerms ps1 -> ValuePerms ps2 -> ValuePerms (ps1 :++: ps2)
appendValuePerms ps1 ValPerms_Nil = ps1
appendValuePerms ps1 (ValPerms_Cons ps2 p) =
  ValPerms_Cons (appendValuePerms ps1 ps2) p

-- | Extract the non-variable portion of a permission list expression
permListToDistPerms :: PermExpr PermListType -> Some DistPerms
permListToDistPerms PExpr_PermListNil = Some DistPermsNil
permListToDistPerms (PExpr_Var _) = Some DistPermsNil
permListToDistPerms (PExpr_PermListCons (PExpr_Var x) p l) =
  case permListToDistPerms l of
    Some perms -> Some $ DistPermsCons perms x p
permListToDistPerms (PExpr_PermListCons _ _ l) = permListToDistPerms l

-- | Combine a list of variable names and a list of permissions into a list of
-- distinguished permissions
valuePermsToDistPerms :: MapRList Name ps -> ValuePerms ps -> DistPerms ps
valuePermsToDistPerms MNil _ = DistPermsNil
valuePermsToDistPerms (ns :>: n) (ValPerms_Cons ps p) =
  DistPermsCons (valuePermsToDistPerms ns ps) n p

-- | Convert a list of permissions inside bindings for variables into a list of
-- distinguished permissions for those variables
mbValuePermsToDistPerms :: MbValuePerms ps -> MbDistPerms ps
mbValuePermsToDistPerms = nuMultiWithElim1 valuePermsToDistPerms

distPermsToValuePerms :: DistPerms ps -> ValuePerms ps
distPermsToValuePerms DistPermsNil = ValPerms_Nil
distPermsToValuePerms (DistPermsCons dperms _ p) =
  ValPerms_Cons (distPermsToValuePerms dperms) p

mbDistPermsToValuePerms :: Mb ctx (DistPerms ps) -> Mb ctx (ValuePerms ps)
mbDistPermsToValuePerms = fmap distPermsToValuePerms

distPermsToProxies :: DistPerms ps -> MapRList Proxy ps
distPermsToProxies (DistPermsNil) = MNil
distPermsToProxies (DistPermsCons ps _ _) = distPermsToProxies ps :>: Proxy

mbDistPermsToProxies :: Mb ctx (DistPerms ps) -> MapRList Proxy ps
mbDistPermsToProxies [nuP| DistPermsNil |] = MNil
mbDistPermsToProxies [nuP| DistPermsCons ps _ _ |] =
  mbDistPermsToProxies ps :>: Proxy

-- | Extract the variables in a 'DistPerms'
distPermsVars :: DistPerms ps -> MapRList Name ps
distPermsVars DistPermsNil = MNil
distPermsVars (DistPermsCons ps x _) = distPermsVars ps :>: x

-- | Append two lists of distinguished permissions
appendDistPerms :: DistPerms ps1 -> DistPerms ps2 -> DistPerms (ps1 :++: ps2)
appendDistPerms ps1 DistPermsNil = ps1
appendDistPerms ps1 (DistPermsCons ps2 x p) =
  DistPermsCons (appendDistPerms ps1 ps2) x p

-- | Split a list of distinguished permissions into two
splitDistPerms :: f ps1 -> MapRList g ps2 -> DistPerms (ps1 :++: ps2) ->
                  (DistPerms ps1, DistPerms ps2)
splitDistPerms _ = helper where
  helper :: MapRList g ps2 -> DistPerms (ps1 :++: ps2) ->
            (DistPerms ps1, DistPerms ps2)
  helper MNil perms = (perms, DistPermsNil)
  helper (prxs :>: _) (DistPermsCons ps x p) =
    let (perms1, perms2) = helper prxs ps in
    (perms1, DistPermsCons perms2 x p)

-- | Lens for the top permission in a 'DistPerms' stack
distPermsHead :: ExprVar a -> Lens' (DistPerms (ps :> a)) (ValuePerm a)
distPermsHead x =
  lens (\(DistPermsCons _ y p) ->
         if x == y then p else error "distPermsHead: incorrect variable name!")
  (\(DistPermsCons pstk y _) p ->
    if x == y then DistPermsCons pstk y p else
      error "distPermsHead: incorrect variable name!")

-- | The lens for the tail of a 'DistPerms' stack
distPermsTail :: Lens' (DistPerms (ps :> a)) (DistPerms ps)
distPermsTail =
  lens (\(DistPermsCons pstk _ _) -> pstk)
  (\(DistPermsCons _ x p) pstk -> DistPermsCons pstk x p)

-- | The lens for the nth permission in a 'DistPerms' stack
nthVarPerm :: Member ps a -> ExprVar a -> Lens' (DistPerms ps) (ValuePerm a)
nthVarPerm Member_Base x = distPermsHead x
nthVarPerm (Member_Step memb') x = distPermsTail . nthVarPerm memb' x

-- | Test if a permission can be copied, i.e., whether @p -o p*p@. This is true
-- iff @p@ does not contain any 'Write' modalities, any frame permissions, or
-- any lifetime ownership permissions.
permIsCopyable :: ValuePerm a -> Bool
permIsCopyable (ValPerm_Eq _) = True
permIsCopyable (ValPerm_Or p1 p2) = permIsCopyable p1 && permIsCopyable p2
permIsCopyable (ValPerm_Exists mb_p) = mbLift $ fmap permIsCopyable mb_p
permIsCopyable (ValPerm_Rec _ args) = recPermArgsAreCopyable args
permIsCopyable (ValPerm_Conj ps) = all atomicPermIsCopyable ps

-- | The same as 'permIsCopyable' except for atomic permissions
atomicPermIsCopyable :: AtomicPerm a -> Bool
atomicPermIsCopyable (Perm_LLVMField
                      (LLVMFieldPerm { llvmFieldRW = PExpr_Read,
                                       llvmFieldContents = p })) =
  permIsCopyable p
atomicPermIsCopyable (Perm_LLVMField _) = False
atomicPermIsCopyable (Perm_LLVMArray
                      (LLVMArrayPerm { llvmArrayFields = fps })) =
  all (atomicPermIsCopyable . Perm_LLVMField) fps
atomicPermIsCopyable (Perm_LLVMFree _) = True
atomicPermIsCopyable (Perm_LLVMFunPtr _) = True
atomicPermIsCopyable Perm_IsLLVMPtr = True
atomicPermIsCopyable (Perm_LLVMFrame _) = False
atomicPermIsCopyable (Perm_LOwned _) = False
atomicPermIsCopyable (Perm_LCurrent _) = True
atomicPermIsCopyable (Perm_Fun _) = True
atomicPermIsCopyable (Perm_BVProp _) = True

-- | 'permIsCopyable' for the 'RecPermArg' type
recPermArgIsCopyable :: RecPermArg a -> Bool
recPermArgIsCopyable (RecPermArg_Lifetime _) = True
recPermArgIsCopyable (RecPermArg_RWModality PExpr_Read) = True
recPermArgIsCopyable (RecPermArg_RWModality _) = False

-- | 'permIsCopyable' for the 'RecPermArgs' type
recPermArgsAreCopyable :: RecPermArgs args -> Bool
recPermArgsAreCopyable RecPermArgs_Nil = True
recPermArgsAreCopyable (RecPermArgs_Cons args arg) =
  recPermArgsAreCopyable args && recPermArgIsCopyable arg

-- | Substitute arguments, a lifetime, and ghost values into a function
-- permission to get the input permissions needed on the arguments
funPermDistIns :: FunPerm ghosts args ret -> MapRList Name args ->
                  ExprVar LifetimeType -> PermExprs ghosts ->
                  DistPerms args
funPermDistIns fun_perm args l ghosts =
  varSubst (PermVarSubst args) $ mbValuePermsToDistPerms $
  subst (consSubst (substOfExprs ghosts) (PExpr_Var l)) $ funPermIns fun_perm

-- | Substitute arguments, a lifetime, and ghost values into a function
-- permission to get the output permissions returned by the function
funPermDistOuts :: FunPerm ghosts args ret -> MapRList Name (args :> ret) ->
                   ExprVar LifetimeType -> PermExprs ghosts ->
                   DistPerms (args :> ret)
funPermDistOuts fun_perm args l ghosts =
  varSubst (PermVarSubst args) $ mbValuePermsToDistPerms $
  subst (consSubst (substOfExprs ghosts) (PExpr_Var l)) $ funPermOuts fun_perm

-- | Unfold a recursive permission given a 'RecPerm' for it
unfoldRecPerm :: RecPerm args a -> RecPermArgs args -> ValuePerm a
unfoldRecPerm rp args =
  foldl1 ValPerm_Or $
  map (subst (substOfExprs $ permArgsToExprs args) . fst) $ recPermCases rp

-- | Generic function to test if a permission contains a lifetime
class ContainsLifetime a where
  containsLifetime :: PermExpr LifetimeType -> a -> Bool

instance ContainsLifetime (DistPerms ps) where
  containsLifetime _ DistPermsNil = False
  containsLifetime l (DistPermsCons ps _ p) =
    containsLifetime l ps || containsLifetime l p

instance ContainsLifetime (ValuePerm a) where
  containsLifetime _ (ValPerm_Eq _) = False
  containsLifetime l (ValPerm_Or p1 p2) =
    containsLifetime l p1 || containsLifetime l p2
  containsLifetime l (ValPerm_Exists mb_p) =
    mbLift $ fmap (containsLifetime l) mb_p
  containsLifetime l (ValPerm_Rec _ args) =
    containsLifetime l args
  containsLifetime l (ValPerm_Conj ps) = any (containsLifetime l) ps

instance ContainsLifetime (AtomicPerm a) where
  containsLifetime l (Perm_LLVMField fp) = containsLifetime l fp
  containsLifetime l (Perm_LLVMArray ap) = containsLifetime l ap
  containsLifetime _ (Perm_LLVMFree _) = False
  containsLifetime _ (Perm_LLVMFunPtr _) = False
  containsLifetime _ Perm_IsLLVMPtr = False
  containsLifetime _ (Perm_LLVMFrame _) = False
  containsLifetime l (Perm_LOwned _) =
    -- NOTE: we could check the permissions in the lowned perm, but we are only
    -- using containsLifetime to end lifetimes, and we should never have an
    -- lowned perm containing a different lifetime that we own; also, we would
    -- have to avoid the lowned perm for l itself, as that will not allow use to
    -- prove the l:lowned perm we need to end the lifetime...
    False
  containsLifetime l (Perm_LCurrent l') = l == l'
  containsLifetime _ (Perm_Fun _) = False
  containsLifetime _ (Perm_BVProp _) = False

instance ContainsLifetime (LLVMFieldPerm w) where
  containsLifetime l fp =
    l == llvmFieldLifetime fp || containsLifetime l (llvmFieldContents fp)

instance ContainsLifetime (LLVMArrayPerm w) where
  containsLifetime l ap = any (containsLifetime l) (llvmArrayFields ap)

instance ContainsLifetime (RecPermArgs args) where
  containsLifetime _ RecPermArgs_Nil = False
  containsLifetime l (RecPermArgs_Cons args arg) =
    containsLifetime l args || containsLifetime l arg

instance ContainsLifetime (RecPermArg a) where
  containsLifetime l (RecPermArg_Lifetime l') = l == l'
  containsLifetime l _ = False


-- | Generic function to put a permission inside a lifetime
class InLifetime a where
  inLifetime :: PermExpr LifetimeType -> a -> a

instance InLifetime (DistPerms ps) where
  inLifetime l = mapDistPerms (inLifetime l)

instance InLifetime (ValuePerm a) where
  inLifetime _ p@(ValPerm_Eq _) = p
  inLifetime l (ValPerm_Or p1 p2) =
    ValPerm_Or (inLifetime l p1) (inLifetime l p2)
  inLifetime l (ValPerm_Exists mb_p) =
    ValPerm_Exists $ fmap (inLifetime l) mb_p
  inLifetime l (ValPerm_Rec n args) =
    ValPerm_Rec n $ inLifetime l args
  inLifetime l (ValPerm_Conj ps) =
    ValPerm_Conj $ map (inLifetime l) ps

instance InLifetime (AtomicPerm a) where
  inLifetime l (Perm_LLVMField fp) =
    Perm_LLVMField $ inLifetime l fp
  inLifetime l (Perm_LLVMArray ap) =
    Perm_LLVMArray $ inLifetime l ap
  inLifetime _ p@(Perm_LLVMFree _) = p
  inLifetime _ p@(Perm_LLVMFunPtr _) = p
  inLifetime _ p@Perm_IsLLVMPtr = p
  inLifetime _ p@(Perm_LLVMFrame _) = p
  inLifetime l (Perm_LOwned _) = Perm_LCurrent l
  inLifetime _ p@(Perm_LCurrent _) = p
  inLifetime _ p@(Perm_Fun _) = p
  inLifetime _ p@(Perm_BVProp _) = p

instance InLifetime (LLVMFieldPerm w) where
  inLifetime l fp = fp { llvmFieldLifetime = l }

instance InLifetime (LLVMArrayPerm w) where
  inLifetime l ap =
    ap { llvmArrayFields = map (inLifetime l) (llvmArrayFields ap) }

instance InLifetime (RecPermArgs args) where
  inLifetime _ RecPermArgs_Nil = RecPermArgs_Nil
  inLifetime l (RecPermArgs_Cons args arg) =
    RecPermArgs_Cons (inLifetime l args) (inLifetime l arg)

instance InLifetime (RecPermArg a) where
  inLifetime l (RecPermArg_Lifetime _) = RecPermArg_Lifetime l
  inLifetime _ arg@(RecPermArg_RWModality _) = arg


-- | Compute the minimal permissions required to end a lifetime that contains
-- the given permissions in an @lowned@ permission. Right now, this just
-- replaces all writes with reads and adds the ending lifetime to the
-- permissions. An important property of this function is that the returned
-- permissions has the same translation as the input permissions, so the
-- translation of a mapping from @minLtEndPerms p@ to @p@ is just the identity.
class MinLtEndPerms a where
  minLtEndPerms :: PermExpr LifetimeType -> a -> a

instance MinLtEndPerms (DistPerms ps) where
  minLtEndPerms l = mapDistPerms (minLtEndPerms l)

instance MinLtEndPerms (ValuePerm a) where
  minLtEndPerms _ p@(ValPerm_Eq _) = p
  minLtEndPerms l (ValPerm_Or p1 p2) =
    ValPerm_Or (minLtEndPerms l p1) (minLtEndPerms l p2)
  minLtEndPerms l (ValPerm_Exists mb_p) =
    ValPerm_Exists $ fmap (minLtEndPerms l) mb_p
  minLtEndPerms l (ValPerm_Rec n args) =
    ValPerm_Rec n $ minLtEndPerms l args
  minLtEndPerms l (ValPerm_Conj ps) =
    ValPerm_Conj $ map (minLtEndPerms l) ps

instance MinLtEndPerms (AtomicPerm a) where
  minLtEndPerms l (Perm_LLVMField fp) =
    Perm_LLVMField $ minLtEndPerms l fp
  minLtEndPerms l (Perm_LLVMArray ap) =
    Perm_LLVMArray $ minLtEndPerms l ap
  minLtEndPerms _ p@(Perm_LLVMFree _) = p
  minLtEndPerms _ p@(Perm_LLVMFunPtr _) = p
  minLtEndPerms _ p@Perm_IsLLVMPtr = Perm_IsLLVMPtr
  minLtEndPerms _ p@(Perm_LLVMFrame _) = p
  minLtEndPerms l (Perm_LOwned _) = Perm_LCurrent l
  minLtEndPerms _ p@(Perm_LCurrent _) = p
  minLtEndPerms _ p@(Perm_Fun _) = p
  minLtEndPerms _ p@(Perm_BVProp _) = p

instance MinLtEndPerms (LLVMFieldPerm w) where
  minLtEndPerms l fp = fp { llvmFieldRW = PExpr_Read, llvmFieldLifetime = l }

instance MinLtEndPerms (LLVMArrayPerm w) where
  minLtEndPerms l ap =
    ap { llvmArrayFields = map (minLtEndPerms l) (llvmArrayFields ap) }

instance MinLtEndPerms (RecPermArgs args) where
  minLtEndPerms _ RecPermArgs_Nil = RecPermArgs_Nil
  minLtEndPerms l (RecPermArgs_Cons args arg) =
    RecPermArgs_Cons (minLtEndPerms l args) (minLtEndPerms l arg)

instance MinLtEndPerms (RecPermArg a) where
  minLtEndPerms l (RecPermArg_Lifetime _) = RecPermArg_Lifetime l
  minLtEndPerms _ (RecPermArg_RWModality _) = RecPermArg_RWModality PExpr_Read


----------------------------------------------------------------------
-- * Matching Functions for Inspecting Permissions
----------------------------------------------------------------------

-- FIXME: figure out a better place to put these functions

-- | Find all elements of list @l@ where @f@ returns a value and return that
-- value plus its index into @l@
findMaybeIndices :: (a -> Maybe b) -> [a] -> [(Int, b)]
findMaybeIndices f l = catMaybes $ zipWith (\i a -> (i,) <$> f a) [0 ..] l

-- | Combine all elements of a list like 'foldr1' unless the list is empty, in
-- which case return the default case
foldr1WithDefault :: (a -> a -> a) -> a -> [a] -> a
foldr1WithDefault _ def [] = def
foldr1WithDefault _ _ [a] = a
foldr1WithDefault f def (a:as) = f a $ foldr1WithDefault f def as

-- | Map a function across a list and then call 'foldr1WithDefault'. This is a
-- form of map-reduce where the default is returned as a special case for the
-- empty list.
foldMapWithDefault :: (b -> b -> b) -> b -> (a -> b) -> [a] -> b
foldMapWithDefault comb def f l = foldr1WithDefault comb def $ map f l


-- FIXME HERE: I think these are no longer used...

-- | The type of a matcher, that matches on an object of type @a@ and maybe
-- produces a @b@
type Matcher a b = a -> Maybe b

-- | Delete the nth element of a list
deleteNth :: Int -> [a] -> [a]
deleteNth i xs | i >= length xs = error "deleteNth"
deleteNth i xs = take i xs ++ drop (i+1) xs

-- | Replace the nth element of a list
replaceNth :: Int -> a -> [a] -> [a]
replaceNth i _ xs | i >= length xs = error "replaceNth"
replaceNth i x xs = take i xs ++ x : drop (i+1) xs

-- | Find all indices in a list for which the supplied
-- function @f@ returns @'Just' b@ for some @b@, also returning the @b@s
findMatches :: Matcher a b -> [a] -> [(Int, b)]
findMatches f = mapMaybe (\(i,a) -> (i,) <$> f a) . zip [0 ..]

-- | Find the first index in a list of an element for which the supplied
-- function @f@ returns @'Just' b@ for some @b@, also returning @b@
findMatch :: Matcher a b -> [a] -> Maybe (Int, b)
findMatch f = listToMaybe . findMatches f

-- | Test if a pointer permission is a free permission
matchFreePtrPerm :: Matcher (LLVMPtrPerm w) (PermExpr (BVType w))
matchFreePtrPerm (Perm_LLVMFree e) = Just e
matchFreePtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission
matchFieldPtrPerm :: Matcher (LLVMPtrPerm w) (LLVMFieldPerm w)
matchFieldPtrPerm (Perm_LLVMField fp) = Just fp
matchFieldPtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission with a specific offset
matchFieldPtrPermOff :: PermExpr (BVType w) ->
                        Matcher (LLVMPtrPerm w) (LLVMFieldPerm w)
matchFieldPtrPermOff off (Perm_LLVMField fp)
  | off == llvmFieldOffset fp = Just fp
matchFieldPtrPermOff _ _ = Nothing

-- | Test if a pointer permission is an array permission
matchArrayPtrPerm :: Matcher (LLVMPtrPerm w) (LLVMArrayPerm w)
matchArrayPtrPerm (Perm_LLVMArray ap) = Just ap
matchArrayPtrPerm _ = Nothing

-- | Find the first 'Perm_LLVMFree' in a list of pointer permissions, returning
-- its index in the list and the expression it contains if found
findFreePerm :: [LLVMPtrPerm w] -> Maybe (Int, PermExpr (BVType w))
findFreePerm = findMatch matchFreePtrPerm

-- | Find all fields in a list of pointer permissions, returning their contents
-- and their indices
findFieldPerms :: [LLVMPtrPerm w] -> [(Int, LLVMFieldPerm w)]
findFieldPerms = findMatches matchFieldPtrPerm

-- | Find a field in a list of pointer permissions with a specific offset
findFieldPerm :: PermExpr (BVType w) -> [LLVMPtrPerm w] ->
                 Maybe (Int, LLVMFieldPerm w)
findFieldPerm off = findMatch (matchFieldPtrPermOff off)

-- | Find all arrays in a list of pointer permissions, returning their contents
-- and their indices
findArrayPerms :: [LLVMPtrPerm w] -> [(Int, LLVMArrayPerm w)]
findArrayPerms = findMatches matchArrayPtrPerm


{- FIXME HERE: remove LLVMFieldMatch and friends

-- | A field match represents a pointer permission that could be used to prove a
-- field permission @ptr(off |-> p)@.
--
-- In order to be used, each match case (that is, each constructor here) has a
-- constraint on @off@ that must hold. The match case is a /definite/ match if
-- the constraint holds under all possible substitutions for the free variables
-- of the pointer permissions involved (i.e., the one being proved and the one
-- used to prove it), and otherwise is a /potential/ match. The first argument
-- to each constructor is a 'Bool' that is 'True' for a definite match and
-- 'False' for a potential one.
data LLVMFieldMatch w
  = FieldMatchField Bool Int (LLVMFieldPerm w)
    -- ^ Represents another field permission @ptr(off' |-> p')@ at the index
    -- given by the 'Int' argument. The constraint for a definite match is that
    -- @off'=off@.
  | FieldMatchArray Bool Int (LLVMArrayPerm w) (PermExpr (BVType w)) Int
    -- ^ Represents an array permission @(off',<len,*stride,S') |-> pps@ at the
    -- given index. The expression argument gives the index @ix@ into the array,
    -- which equals @(off - off')/stride@. The final 'Int' argument gives the
    -- index into the @pps@ list of the individual field in the @ix@ array cell
    -- whose offset equals @(off - off')%stride@, which must be a static
    -- constant. The constraint for a definite match is @ix < len@.

-- | Test if a field match is a definite match
fieldMatchDefinite :: LLVMFieldMatch w -> Bool
fieldMatchDefinite (FieldMatchField b _ _) = b
fieldMatchDefinite (FieldMatchArray b _ _ _ _) = b

-- | Find all field matches for a given offset @off@ in a list of pointer perms
findFieldMatches :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    [LLVMPtrPerm w] -> [LLVMFieldMatch w]
findFieldMatches off pps =
  flip mapMaybe (zip pps [0::Int ..]) $ \(pp, i) ->
  case pp of
    Perm_LLVMField fp
      | bvCouldEqual off (llvmFieldOffset fp) ->
        Just (FieldMatchField (bvEq off $ llvmFieldOffset fp) i fp)
    Perm_LLVMField _ -> Nothing
    Perm_LLVMArray ap@(LLVMArrayPerm {..}) ->
      -- In order to index into an array, off must be a multiple of the stride
      -- plus a known, constant offset into the array cell. That is, the value
      -- (off - off')%(stride*w/8) must be a constant.
      do let arr_off = bvSub off llvmArrayOffset -- offset from start of array
         k <- bvMatchConst (bvMod arr_off (arrayStrideBytes ap))
         fld_i <- findIndex (\fld ->
                              llvmFieldOffset fld == bvInt k) llvmArrayFields
         let arr_ix = bvDiv arr_off (arrayStrideBytes ap) -- index into array
         if bvCouldBeLt arr_ix llvmArrayLen then
           return $ FieldMatchArray (bvLt arr_ix llvmArrayLen) i ap arr_ix fld_i
           else Nothing
-}

-- FIXME HERE: remove, or at least reevaluate, these!
{-
-- | Build a matcher that ignores a value
matchIgnore :: Matcher a ()
matchIgnore = const $ return ()

-- | Build a matcher that tests equality
matchEq :: Eq a => a -> Matcher a a
matchEq a1 a2 | a1 == a2 = return a2
matchEq _ _ = Nothing

-- | Test if a permission is an equality permission
matchEqPerm :: Matcher (ValuePerm a) (PermExpr a)
matchEqPerm (ValPerm_Eq e) = Just e
matchEqPerm _ = Nothing

-- | Test is an expression is an LLVM word
matchLLVMWordExpr :: Matcher (PermExpr (LLVMPointerType w)) (PermExpr (BVType w))
matchLLVMWordExpr (PExpr_LLVMWord e) = Just e
matchLLVMWordExpr _ = Nothing

-- | Test if a permission is an equality permission to a @word(e)@ expression
matchEqLLVMWordPerm :: Matcher (ValuePerm (LLVMPointerType w))
                       (PermExpr (BVType w))
matchEqLLVMWordPerm = matchEqPerm >=> matchLLVMWordExpr

-- | Test if a permission satisfies a predicate inside 0 or more existentials or
-- disjunctions
matchInExsOrs :: Liftable r => Matcher (ValuePerm a) r ->
                 Matcher (ValuePerm a) r
matchInExsOrs f p | Just b <- f p = Just b
matchInExsOrs f (ValPerm_Or p1 p2) = matchInExsOrs f p1 <|> matchInExsOrs f p2
matchInExsOrs f (ValPerm_Exists p) = mbLift $ fmap (matchInExsOrs f) p
matchInExsOrs _ _ = Nothing

-- | Test if a permission is an @eq(e)@ inside 0 or more existentials or
-- disjunctions; does not return the contents of the @eq(e)@ perm, as it may be
-- under some number of name-bindings
matchNestedEqPerm :: Matcher (ValuePerm a) ()
matchNestedEqPerm = matchInExsOrs (matchEqPerm >=> matchIgnore)

-- | Test if a permission is an LLVM pointer permission satisfying the given
-- predicate
matchPtrPerm :: Matcher (LLVMPtrPerm w) r ->
                Matcher (ValuePerm (LLVMPointerType w)) r
matchPtrPerm f (ValPerm_LLVMPtr pp) = f pp
matchPtrPerm _ _ = Nothing

-- | Test if a pointer permission satisfies the given predicate inside 0 or more
-- stars
matchInPtrStars :: Matcher (LLVMPtrPerm w) r -> Matcher (LLVMPtrPerm w) r
matchInPtrStars f p | Just b <- f p = Just b
matchInPtrStars f (LLVMStarPerm p1 p2) =
  matchInPtrStars f p1 <|> matchInPtrStars f p2
matchInPtrStars _ _ = Nothing

-- | Test if a permission satisfies a predicate on 'LLVMPtrPerm's inside 0 or
-- more existentials, disjunctions, and stars; does not return the contents, as
-- these may be under name-bindings
matchInExsOrsStars :: Matcher (LLVMPtrPerm w) r ->
                      Matcher (ValuePerm (LLVMPointerType w)) ()
matchInExsOrsStars f =
  matchInExsOrs (matchPtrPerm (matchInPtrStars f) >=> matchIgnore)

-- | Test if a pointer permission is a free permission
matchFreePtrPerm :: Matcher (LLVMPtrPerm w) (PermExpr (BVType w))
matchFreePtrPerm (Perm_LLVMFree e) = Just e
matchFreePtrPerm _ = Nothing

-- | Test if a permission is an @x:ptr(free(e))@ inside 0 or more existentials,
-- disjunctions, or LLVM stars
matchNestedFreePerm :: Matcher (ValuePerm (LLVMPointerType w)) ()
matchNestedFreePerm = matchInExsOrsStars (matchFreePtrPerm >=> matchIgnore)

-- | Test if a pointer permission is a field permission
matchFieldPtrPerm :: Matcher (LLVMPtrPerm w)
                     (PermExpr (BVType w),
                      SplittingExpr, ValuePerm (LLVMPointerType w))
matchFieldPtrPerm (LLVMFieldPerm off spl p) = Just (off, spl, p)
matchFieldPtrPerm _ = Nothing

-- | Test if a pointer permission is a field permission with a specific offset
matchFieldPtrPermOff :: PermExpr (BVType w) ->
                        Matcher (LLVMPtrPerm w) (SplittingExpr,
                                                 ValuePerm (LLVMPointerType w))
matchFieldPtrPermOff off (LLVMFieldPerm off' spl p)
  | off == off' = Just (spl, p)
matchFieldPtrPermOff _ _ = Nothing
-}


----------------------------------------------------------------------
-- * Generalized Substitution
----------------------------------------------------------------------

-- | Defines a substitution type @s@ that supports substituting into expression
-- and permission variables in a given monad @m@
class MonadBind m => SubstVar s m | s -> m where
  extSubst :: s ctx -> ExprVar a -> s (ctx :> a)
  substExprVar :: s ctx -> Mb ctx (ExprVar a) -> m (PermExpr a)

-- | Generalized notion of substitution, which says that substitution type @s@
-- supports substituting into type @a@ in monad @m@
class SubstVar s m => Substable s a m where
  genSubst :: s ctx -> Mb ctx a -> m a

-- | A version of 'Substable' for type functors
class SubstVar s m => Substable1 s f m where
  genSubst1 :: s ctx -> Mb ctx (f a) -> m (f a)

instance SubstVar s m => Substable s Integer m where
  genSubst _ mb_i = return $ mbLift mb_i

instance (NuMatching a, Substable s a m) => Substable s [a] m where
  genSubst s as = mapM (genSubst s) (mbList as)

instance (Substable s a m, Substable s b m) => Substable s (a,b) m where
  genSubst s ab = (,) <$> genSubst s (fmap fst ab) <*> genSubst s (fmap snd ab)

instance (NuMatching a, Substable s a m) => Substable s (Maybe a) m where
  genSubst s [nuP| Just a |] = Just <$> genSubst s a
  genSubst _ [nuP| Nothing |] = return Nothing

instance (Substable s a m, NuMatching a) => Substable s (Mb ctx a) m where
  genSubst s mbmb = mbM $ fmap (genSubst s) (mbSwap mbmb)

instance SubstVar s m => Substable s (Member ctx a) m where
  genSubst _ mb_memb = return $ mbLift mb_memb

-- | Helper function to substitute into 'BVFactor's
substBVFactor :: SubstVar s m => s ctx -> Mb ctx (BVFactor w) ->
                 m (PermExpr (BVType w))
substBVFactor s [nuP| BVFactor i x |] =
  bvMult (mbLift i) <$> substExprVar s x

instance SubstVar s m =>
         Substable s (NatRepr n) m where
  genSubst _ = return . mbLift

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (ExprVar a) m where
  genSubst s mb_x = return $ varSubstVar s mb_x

instance SubstVar s m => Substable s (PermExpr a) m where
  genSubst s [nuP| PExpr_Var x |] = substExprVar s x
  genSubst _ [nuP| PExpr_Unit |] = return $ PExpr_Unit
  genSubst _ [nuP| PExpr_Nat n |] = return $ PExpr_Nat $ mbLift n
  genSubst _ [nuP| PExpr_Bool b |] = return $ PExpr_Bool $ mbLift b
  genSubst s [nuP| PExpr_BV factors off |] =
    foldr bvAdd (PExpr_BV [] (mbLift off)) <$>
    mapM (substBVFactor s) (mbList factors)
  genSubst s [nuP| PExpr_Struct args |] =
    PExpr_Struct <$> genSubst s args
  genSubst s [nuP| PExpr_Always |] = return PExpr_Always
  genSubst s [nuP| PExpr_LLVMWord e |] =
    PExpr_LLVMWord <$> genSubst s e
  genSubst s [nuP| PExpr_LLVMOffset x off |] =
    addLLVMOffset <$> substExprVar s x <*> genSubst s off
  genSubst _ [nuP| PExpr_Fun fh |] =
    return $ PExpr_Fun $ mbLift fh
  genSubst _ [nuP| PExpr_PermListNil |] =
    return $ PExpr_PermListNil
  genSubst s [nuP| PExpr_PermListCons e p l |] =
    PExpr_PermListCons <$> genSubst s e <*> genSubst s p <*> genSubst s l
  genSubst _ [nuP| PExpr_RWModality rw |] =
    return $ PExpr_RWModality $ mbLift rw

instance SubstVar s m => Substable s (PermExprs as) m where
  genSubst s [nuP| PExprs_Nil |] = return PExprs_Nil
  genSubst s [nuP| PExprs_Cons es e |] =
    PExprs_Cons <$> genSubst s es <*> genSubst s e

instance SubstVar s m => Substable s (BVRange w) m where
  genSubst s [nuP| BVRange e1 e2 |] =
    BVRange <$> genSubst s e1 <*> genSubst s e2

instance SubstVar s m => Substable s (BVProp w) m where
  genSubst s [nuP| BVProp_Eq e1 e2 |] =
    BVProp_Eq <$> genSubst s e1 <*> genSubst s e2
  genSubst s [nuP| BVProp_InRange e r |] =
    BVProp_InRange <$> genSubst s e <*> genSubst s r
  genSubst s [nuP| BVProp_RangeSubset r1 r2 |] =
    BVProp_RangeSubset <$> genSubst s r1 <*> genSubst s r2
  genSubst s [nuP| BVProp_RangesDisjoint r1 r2 |] =
    BVProp_RangesDisjoint <$> genSubst s r1 <*> genSubst s r2

instance SubstVar s m => Substable s (AtomicPerm a) m where
  genSubst s [nuP| Perm_LLVMField fp |] = Perm_LLVMField <$> genSubst s fp
  genSubst s [nuP| Perm_LLVMArray ap |] = Perm_LLVMArray <$> genSubst s ap
  genSubst s [nuP| Perm_LLVMFree e |] = Perm_LLVMFree <$> genSubst s e
  genSubst s [nuP| Perm_LLVMFunPtr fp |] = Perm_LLVMFunPtr <$> genSubst s fp
  genSubst _ [nuP| Perm_IsLLVMPtr |] = return Perm_IsLLVMPtr
  genSubst s [nuP| Perm_LLVMFrame fp |] =
    Perm_LLVMFrame <$> genSubst s fp
  genSubst s [nuP| Perm_LOwned e |] =
    Perm_LOwned <$> genSubst s e
  genSubst s [nuP| Perm_LCurrent e |] =
    Perm_LCurrent <$> genSubst s e
  genSubst s [nuP| Perm_Fun fperm |] =
    Perm_Fun <$> genSubst s fperm
  genSubst s [nuP| Perm_BVProp prop |] =
    Perm_BVProp <$> genSubst s prop

instance SubstVar s m => Substable s (RecPermName args a) m where
  genSubst _ mb_rpn = return $ mbLift mb_rpn

instance SubstVar s m => Substable s (RecPerm args a) m where
  genSubst s [nuP| RecPerm rpn dt_i f_i u_i cases |] =
    RecPerm (mbLift rpn) (mbLift dt_i) (mbLift f_i) (mbLift u_i) <$>
    mapM (\[nuP| (mb_p, i) |] -> genSubst s mb_p >>= \p -> return (p,mbLift i))
    (mbList cases)

instance SubstVar s m => Substable s (ValuePerm a) m where
  genSubst s [nuP| ValPerm_Eq e |] = ValPerm_Eq <$> genSubst s e
  genSubst s [nuP| ValPerm_Or p1 p2 |] =
    ValPerm_Or <$> genSubst s p1 <*> genSubst s p2
  genSubst s [nuP| ValPerm_Exists p |] =
    -- FIXME: maybe we don't need extSubst at all, but can just use the
    -- Substable instance for Mb ctx a from above
    ValPerm_Exists <$>
    nuM (\x -> genSubst (extSubst s x) $ mbCombine p)
  genSubst s [nuP| ValPerm_Rec n args |] =
    ValPerm_Rec (mbLift n) <$> genSubst s args
  genSubst s [nuP| ValPerm_Conj aps |] =
    ValPerm_Conj <$> mapM (genSubst s) (mbList aps)

instance SubstVar s m => Substable s (ValuePerms as) m where
  genSubst s [nuP| ValPerms_Nil |] = return ValPerms_Nil
  genSubst s [nuP| ValPerms_Cons ps p |] =
    ValPerms_Cons <$> genSubst s ps <*> genSubst s p

instance SubstVar s m => Substable s RWModality m where
  genSubst s [nuP| Write |] = return Write
  genSubst s [nuP| Read |] = return Read

instance SubstVar s m => Substable s (LLVMFieldPerm w) m where
  genSubst s [nuP| LLVMFieldPerm rw ls off p |] =
    LLVMFieldPerm <$> genSubst s rw <*> genSubst s ls <*>
    genSubst s off <*> genSubst s p

instance SubstVar s m => Substable s (LLVMArrayPerm w) m where
  genSubst s [nuP| LLVMArrayPerm off len stride pps bs |] =
    LLVMArrayPerm <$> genSubst s off <*> genSubst s len <*>
    return (mbLift stride) <*> mapM (genSubst s) (mbList pps)
    <*> mapM (genSubst s) (mbList bs)

instance SubstVar s m => Substable s (LLVMArrayIndex w) m where
  genSubst s [nuP| LLVMArrayIndex ix fld_num |] =
    LLVMArrayIndex <$> genSubst s ix <*> return (mbLift fld_num)

instance SubstVar s m => Substable s (LLVMArrayBorrow w) m where
  genSubst s [nuP| FieldBorrow ix |] = FieldBorrow <$> genSubst s ix
  genSubst s [nuP| RangeBorrow r |] = RangeBorrow <$> genSubst s r

instance SubstVar s m => Substable s (FunPerm ghosts args ret) m where
  genSubst s [nuP| FunPerm ghosts args ret perms_in perms_out |] =
    FunPerm (mbLift ghosts) (mbLift args) (mbLift ret)
    <$> genSubst s perms_in <*> genSubst s perms_out

instance SubstVar s m => Substable s (RecPermArgs args) m where
  genSubst s [nuP| RecPermArgs_Nil |] = return RecPermArgs_Nil
  genSubst s [nuP| RecPermArgs_Cons args arg |] =
    RecPermArgs_Cons <$> genSubst s args <*> genSubst s arg

instance SubstVar s m => Substable s (RecPermArg a) m where
  genSubst s [nuP| RecPermArg_Lifetime l |] =
    RecPermArg_Lifetime <$> genSubst s l
  genSubst s [nuP| RecPermArg_RWModality rw |] =
    RecPermArg_RWModality <$> genSubst s rw

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (LifetimeCurrentPerms ps) m where
  genSubst s [nuP| AlwaysCurrentPerms |] = return AlwaysCurrentPerms
  genSubst s [nuP| LOwnedCurrentPerms l ps |] =
    LOwnedCurrentPerms <$> genSubst s l <*> genSubst s ps
  genSubst s [nuP| CurrentTransPerms ps l |] =
    CurrentTransPerms <$> genSubst s ps <*> genSubst s l

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (DistPerms ps) m where
  genSubst s [nuP| DistPermsNil |] = return DistPermsNil
  genSubst s [nuP| DistPermsCons dperms' x p |] =
    DistPermsCons <$> genSubst s dperms' <*>
    return (varSubstVar s x) <*> genSubst s p


----------------------------------------------------------------------
-- * Expression Substitutions
----------------------------------------------------------------------

-- | A substitution assigns a permission expression to each bound name in a
-- name-binding context
newtype PermSubst ctx =
  PermSubst { unPermSubst :: MapRList PermExpr ctx }

emptySubst :: PermSubst RNil
emptySubst = PermSubst empty

consSubst :: PermSubst ctx -> PermExpr a -> PermSubst (ctx :> a)
consSubst (PermSubst elems) e = PermSubst (elems :>: e)

singletonSubst :: PermExpr a -> PermSubst (RNil :> a)
singletonSubst e = PermSubst (empty :>: e)

substOfExprs :: PermExprs ctx -> PermSubst ctx
substOfExprs PExprs_Nil = PermSubst MNil
substOfExprs (PExprs_Cons es e) = consSubst (substOfExprs es) e

-- FIXME: Maybe PermSubst should just be PermExprs?
exprsOfSubst :: PermSubst ctx -> PermExprs ctx
exprsOfSubst (PermSubst MNil) = PExprs_Nil
exprsOfSubst (PermSubst (es :>: e)) =
  PExprs_Cons (exprsOfSubst $ PermSubst es) e

substLookup :: PermSubst ctx -> Member ctx a -> PermExpr a
substLookup (PermSubst m) memb = mapRListLookup memb m

noPermsInCruCtx :: forall (ctx :: RList CrucibleType) (a :: CrucibleType) b.
                   Member ctx (ValuePerm a) -> b
noPermsInCruCtx (Member_Step ctx) = noPermsInCruCtx ctx
-- No case for Member_Base

instance SubstVar PermSubst Identity where
  extSubst (PermSubst elems) x = PermSubst $ elems :>: PExpr_Var x
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ substLookup s memb
      Right y -> return $ PExpr_Var y

-- | Wrapper function to apply a substitution to an expression type
subst :: Substable PermSubst a Identity => PermSubst ctx -> Mb ctx a -> a
subst s mb = runIdentity $ genSubst s mb


----------------------------------------------------------------------
-- * Variable Substitutions
----------------------------------------------------------------------

-- | Like a substitution but assigns variables instead of arbitrary expressions
-- to bound variables
newtype PermVarSubst (ctx :: RList CrucibleType) =
  PermVarSubst { unPermVarSubst :: MapRList Name ctx }

singletonVarSubst :: ExprVar a -> PermVarSubst (RNil :> a)
singletonVarSubst x = PermVarSubst (empty :>: x)

consVarSubst :: PermVarSubst ctx -> ExprVar a -> PermVarSubst (ctx :> a)
consVarSubst (PermVarSubst elems) n = PermVarSubst (elems :>: n)

varSubstLookup :: PermVarSubst ctx -> Member ctx a -> ExprVar a
varSubstLookup (PermVarSubst m) memb = mapRListLookup memb m

appendVarSubsts :: PermVarSubst ctx1 -> PermVarSubst ctx2 ->
                   PermVarSubst (ctx1 :++: ctx2)
appendVarSubsts (PermVarSubst es1) (PermVarSubst es2) =
  PermVarSubst (appendMapRList es1 es2)

varSubstVar :: PermVarSubst ctx -> Mb ctx (ExprVar a) -> ExprVar a
varSubstVar s mb_x =
  case mbNameBoundP mb_x of
    Left memb -> varSubstLookup s memb
    Right x -> x

instance SubstVar PermVarSubst Identity where
  extSubst (PermVarSubst elems) x = PermVarSubst $ elems :>: x
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ PExpr_Var $ varSubstLookup s memb
      Right y -> return $ PExpr_Var y

-- | Wrapper function to apply a renamionmg to an expression type
varSubst :: Substable PermVarSubst a Identity => PermVarSubst ctx ->
            Mb ctx a -> a
varSubst s mb = runIdentity $ genSubst s mb


----------------------------------------------------------------------
-- * Partial Substitutions
----------------------------------------------------------------------

-- | An element of a partial substitution = maybe an expression
newtype PSubstElem a = PSubstElem { unPSubstElem :: Maybe (PermExpr a) }

-- | Partial substitutions assign expressions to some of the bound names in a
-- context
newtype PartialSubst ctx =
  PartialSubst { unPartialSubst :: MapRList PSubstElem ctx }

-- | Build an empty partial substitution for a given set of variables, i.e., the
-- partial substitution that assigns no expressions to those variables
emptyPSubst :: CruCtx ctx -> PartialSubst ctx
emptyPSubst = PartialSubst . helper where
  helper :: CruCtx ctx -> MapRList PSubstElem ctx
  helper CruCtxNil = MNil
  helper (CruCtxCons ctx' _) = helper ctx' :>: PSubstElem Nothing

-- | Set the expression associated with a variable in a partial substitution. It
-- is an error if it is already set.
psubstSet :: Member ctx a -> PermExpr a -> PartialSubst ctx ->
             PartialSubst ctx
psubstSet memb e (PartialSubst elems) =
  PartialSubst $
  mapRListModify memb
  (\pse -> case pse of
      PSubstElem Nothing -> PSubstElem $ Just e
      PSubstElem (Just _) -> error "psubstSet: value already set for variable")
  elems

-- | Extend a partial substitution with an unassigned variable
extPSubst :: PartialSubst ctx -> PartialSubst (ctx :> a)
extPSubst (PartialSubst elems) = PartialSubst $ elems :>: PSubstElem Nothing

-- | Shorten a partial substitution
unextPSubst :: PartialSubst (ctx :> a) -> PartialSubst ctx
unextPSubst (PartialSubst (elems :>: _)) = PartialSubst elems

-- | Complete a partial substitution into a total substitution, filling in zero
-- values using 'zeroOfType' if necessary
completePSubst :: CruCtx vars -> PartialSubst vars -> PermSubst vars
completePSubst ctx (PartialSubst pselems) = PermSubst $ helper ctx pselems where
  helper :: CruCtx vars -> MapRList PSubstElem vars -> MapRList PermExpr vars
  helper _ MNil = MNil
  helper (CruCtxCons ctx' knownRepr) (pselems' :>: pse) =
    helper ctx' pselems' :>:
    (fromMaybe (zeroOfType knownRepr) (unPSubstElem pse))

-- | Look up an optional expression in a partial substitution
psubstLookup :: PartialSubst ctx -> Member ctx a -> Maybe (PermExpr a)
psubstLookup (PartialSubst m) memb = unPSubstElem $ mapRListLookup memb m

instance SubstVar PartialSubst Maybe where
  extSubst (PartialSubst elems) x =
    PartialSubst $ elems :>: PSubstElem (Just $ PExpr_Var x)
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> psubstLookup s memb
      Right y -> return $ PExpr_Var y

-- | Wrapper function to apply a partial substitution to an expression type
partialSubst :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                Mb ctx a -> Maybe a
partialSubst s mb = genSubst s mb

-- | Apply a partial substitution, raising an error (with the given string) if
-- this fails
partialSubstForce :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                     Mb ctx a -> String -> a
partialSubstForce s mb msg = fromMaybe (error msg) $ partialSubst s mb


----------------------------------------------------------------------
-- * Value Permission Substitutions
----------------------------------------------------------------------

noExprsInTypeCtx :: forall (ctx :: RList Type) (a :: CrucibleType) b.
                    Member ctx a -> b
noExprsInTypeCtx (Member_Step ctx) = noExprsInTypeCtx ctx
-- No case for Member_Base

-- | Typeclass to substitute a 'ValuePerm' for a 'PermVar'
class SubstValPerm a where
  substValPerm :: ValuePerm tp -> Binding (ValuePerm tp) a -> a

instance SubstValPerm Integer where
  substValPerm _ = mbLift

instance (NuMatching a, SubstValPerm a) => SubstValPerm [a] where
  substValPerm p as = map (substValPerm p) (mbList as)

instance (SubstValPerm a, SubstValPerm b) => SubstValPerm (a,b) where
  substValPerm p ab =
    (substValPerm p (fmap fst ab), substValPerm p (fmap snd ab))

instance (NuMatching a, SubstValPerm a) => SubstValPerm (Maybe a) where
  substValPerm p [nuP| Just a |] = Just $ substValPerm p a
  substValPerm _ [nuP| Nothing |] = Nothing

instance (NuMatching a, SubstValPerm a) => SubstValPerm (Mb ctx a) where
  substValPerm p mbmb = fmap (substValPerm p) (mbSwap mbmb)

instance SubstValPerm (Member ctx a) where
  substValPerm _ mb_memb = mbLift mb_memb

instance SubstValPerm (Name (a :: CrucibleType)) where
  substValPerm _ mb_x =
    case mbNameBoundP mb_x of
      Left memb -> noExprsInTypeCtx memb
      Right x -> x

instance SubstValPerm (BVFactor w) where
  substValPerm p [nuP| BVFactor i x |] =
    BVFactor (mbLift i) (substValPerm p x)

instance SubstValPerm (PermExpr a) where
  substValPerm p [nuP| PExpr_Var x |] = PExpr_Var (substValPerm p x)
  substValPerm _ [nuP| PExpr_Unit |] = PExpr_Unit
  substValPerm _ [nuP| PExpr_Nat n |] = PExpr_Nat $ mbLift n
  substValPerm _ [nuP| PExpr_Bool b |] = PExpr_Bool $ mbLift b
  substValPerm p [nuP| PExpr_BV factors off |] =
    PExpr_BV (substValPerm p factors) (substValPerm p off)
  substValPerm p [nuP| PExpr_Struct args |] =
    PExpr_Struct $ substValPerm p args
  substValPerm _ [nuP| PExpr_Always |] = PExpr_Always
  substValPerm p [nuP| PExpr_LLVMWord e |] =
    PExpr_LLVMWord $ substValPerm p e
  substValPerm p [nuP| PExpr_LLVMOffset x off |] =
    PExpr_LLVMOffset (substValPerm p x) (substValPerm p off)
  substValPerm _ [nuP| PExpr_Fun fh |] = PExpr_Fun $ mbLift fh
  substValPerm _ [nuP| PExpr_PermListNil |] = PExpr_PermListNil
  substValPerm s [nuP| PExpr_PermListCons e p l |] =
    PExpr_PermListCons (substValPerm s e) (substValPerm s p) (substValPerm s l)
  substValPerm _ [nuP| PExpr_RWModality rw |] = PExpr_RWModality $ mbLift rw

instance SubstValPerm (PermExprs as) where
  substValPerm _ [nuP| PExprs_Nil |] = PExprs_Nil
  substValPerm p [nuP| PExprs_Cons es e |] =
    PExprs_Cons (substValPerm p es) (substValPerm p e)

instance SubstValPerm (BVRange w) where
  substValPerm p [nuP| BVRange e1 e2 |] =
    BVRange (substValPerm p e1) (substValPerm p e2)

instance SubstValPerm (BVProp w) where
  substValPerm p [nuP| BVProp_Eq e1 e2 |] =
    BVProp_Eq (substValPerm p e1) (substValPerm p e2)
  substValPerm p [nuP| BVProp_InRange e r |] =
    BVProp_InRange (substValPerm p e) (substValPerm p r)
  substValPerm p [nuP| BVProp_RangeSubset r1 r2 |] =
    BVProp_RangeSubset (substValPerm p r1) (substValPerm p r2)
  substValPerm p [nuP| BVProp_RangesDisjoint r1 r2 |] =
    BVProp_RangesDisjoint (substValPerm p r1) (substValPerm p r2)

instance SubstValPerm (AtomicPerm a) where
  substValPerm p [nuP| Perm_LLVMField fp |] =
    Perm_LLVMField $ substValPerm p fp
  substValPerm p [nuP| Perm_LLVMArray ap |] =
    Perm_LLVMArray $ substValPerm p ap
  substValPerm p [nuP| Perm_LLVMFree e |] =
    Perm_LLVMFree $ substValPerm p e
  substValPerm p [nuP| Perm_LLVMFunPtr fp |] =
    Perm_LLVMFunPtr $ substValPerm p fp
  substValPerm _ [nuP| Perm_IsLLVMPtr |] = Perm_IsLLVMPtr
  substValPerm p [nuP| Perm_LLVMFrame fp |] =
    Perm_LLVMFrame $ substValPerm p fp
  substValPerm p [nuP| Perm_LOwned e |] =
    Perm_LOwned (substValPerm p e)
  substValPerm p [nuP| Perm_LCurrent e |] =
    Perm_LCurrent $ substValPerm p e
  substValPerm p [nuP| Perm_Fun fperm |] =
    Perm_Fun $ substValPerm p fperm
  substValPerm p [nuP| Perm_BVProp prop |] =
    Perm_BVProp $ substValPerm p prop

instance SubstValPerm (ValuePerm a) where
  substValPerm p [nuP| ValPerm_Eq e |] = ValPerm_Eq $ substValPerm p e
  substValPerm p [nuP| ValPerm_Or p1 p2 |] =
    ValPerm_Or (substValPerm p p1) (substValPerm p p2)
  substValPerm p [nuP| ValPerm_Exists p' |] =
    ValPerm_Exists $ substValPerm p p'
  substValPerm p [nuP| ValPerm_Rec n args |] =
    ValPerm_Rec (mbLift n) $ substValPerm p args
  substValPerm p [nuP| ValPerm_Conj aps |] =
    ValPerm_Conj $ substValPerm p aps

instance SubstValPerm (ValuePerms as) where
  substValPerm p [nuP| ValPerms_Nil |] = ValPerms_Nil
  substValPerm p [nuP| ValPerms_Cons ps p' |] =
    ValPerms_Cons (substValPerm p ps) (substValPerm p p')

instance SubstValPerm RWModality where
  substValPerm _ [nuP| Write |] = Write
  substValPerm _ [nuP| Read |] = Read

instance SubstValPerm (LLVMFieldPerm w) where
  substValPerm p [nuP| LLVMFieldPerm rw ls off p' |] =
    LLVMFieldPerm (substValPerm p rw) (substValPerm p ls) (substValPerm p off)
    (substValPerm p p')

instance SubstValPerm (LLVMArrayPerm w) where
  substValPerm p [nuP| LLVMArrayPerm off len stride pps bs |] =
    LLVMArrayPerm (substValPerm p off) (substValPerm p len)
    (mbLift stride) (substValPerm p pps) (substValPerm p bs)

instance SubstValPerm (LLVMArrayIndex w) where
  substValPerm p [nuP| LLVMArrayIndex ix fld_num |] =
    LLVMArrayIndex (substValPerm p ix) (mbLift fld_num)

instance SubstValPerm (LLVMArrayBorrow w) where
  substValPerm p [nuP| FieldBorrow ix |] =
    FieldBorrow (substValPerm p ix)
  substValPerm p [nuP| RangeBorrow r |] = RangeBorrow $ substValPerm p r

instance SubstValPerm (FunPerm ghosts args ret) where
  substValPerm p [nuP| FunPerm ghosts args ret perms_in perms_out |] =
    FunPerm (mbLift ghosts) (mbLift args) (mbLift ret)
    (substValPerm p perms_in) (substValPerm p perms_out)

instance SubstValPerm (RecPermArgs args) where
  substValPerm _ [nuP| RecPermArgs_Nil |] = RecPermArgs_Nil
  substValPerm p [nuP| RecPermArgs_Cons args arg |] =
    RecPermArgs_Cons (substValPerm p args) (substValPerm p arg)

instance SubstValPerm (RecPermArg a) where
  substValPerm p [nuP| RecPermArg_Lifetime l |] =
    RecPermArg_Lifetime $ substValPerm p l
  substValPerm p [nuP| RecPermArg_RWModality rw |] =
    RecPermArg_RWModality $ substValPerm p rw


----------------------------------------------------------------------
-- * Abstracting Out Variables
----------------------------------------------------------------------

mbMbApply :: Mb (ctx1 :: RList k1) (Mb (ctx2 :: RList k2) (a -> b)) ->
             Mb ctx1 (Mb ctx2 a) -> Mb ctx1 (Mb ctx2 b)
mbMbApply = mbApply . (fmap mbApply)

clMbMbApplyM :: Monad m =>
                m (Closed (Mb (ctx1 :: RList k1)
                           (Mb (ctx2 :: RList k2) (a -> b)))) ->
                m (Closed (Mb ctx1 (Mb ctx2 a))) ->
                m (Closed (Mb ctx1 (Mb ctx2 b)))
clMbMbApplyM fm am =
  (\f a -> $(mkClosed [| mbMbApply |]) `clApply` f `clApply` a) <$> fm <*> am

absVarsReturnH :: Monad m => MapRList f1 (ctx1 :: RList k1) ->
                  MapRList f2 (ctx2 :: RList k2) ->
                  Closed a -> m (Closed (Mb ctx1 (Mb ctx2 a)))
absVarsReturnH fs1 fs2 cl_a =
  return ( $(mkClosed [| \prxs1 prxs2 a ->
                        nuMulti prxs1 (const $ nuMulti prxs2 $ const a) |])
           `clApply` closedProxies fs1 `clApply` closedProxies fs2
           `clApply` cl_a)

closedProxies :: MapRList f args -> Closed (MapRList Proxy args)
closedProxies MNil = $(mkClosed [| MNil |])
closedProxies (args :>: _) =
  $(mkClosed [| (:>:) |]) `clApply` closedProxies args
  `clApply` $(mkClosed [| Proxy |])

nameMember :: forall (ctx :: RList k) (a :: k).
              MapRList Name ctx -> Name a -> Maybe (Member ctx a)
nameMember MNil _ = Nothing
nameMember (_ :>: n1) n2 | Just Refl <- cmpName n1 n2 = Just Member_Base
nameMember (ns :>: _) n = fmap Member_Step $ nameMember ns n

-- | Class for types that support abstracting out all permission and expression
-- variables. If the abstraction succeeds, we get a closed element of the type
-- inside a binding for those permission and expression variables that are free
-- in the original input.
class AbstractVars a where
  abstractPEVars :: MapRList Name (pctx :: RList Type) ->
                    MapRList Name (ectx :: RList CrucibleType) -> a ->
                    Maybe (Closed (Mb pctx (Mb ectx a)))

abstractVars :: AbstractVars a =>
                MapRList Name (ctx :: RList CrucibleType) -> a ->
                Maybe (Closed (Mb ctx a))
abstractVars ns a =
  fmap (clApply $(mkClosed [| elimEmptyMb |])) $ abstractPEVars MNil ns a

tryClose :: AbstractVars a => a -> Maybe (Closed a)
tryClose a =
  fmap (clApply $(mkClosed [| elimEmptyMb . elimEmptyMb |])) $
  abstractPEVars MNil MNil a

instance AbstractVars (Name (a :: CrucibleType)) where
  abstractPEVars ns1 ns2 (n :: Name a)
    | Just memb <- nameMember ns2 n
    = return ( $(mkClosed
                 [| \prxs1 prxs2 memb ->
                   nuMulti prxs1 (const $ nuMulti prxs2 (mapRListLookup memb)) |])
               `clApply` closedProxies ns1 `clApply` closedProxies ns2
               `clApply` toClosed memb)
  abstractPEVars _ _ _ = Nothing

instance AbstractVars (Name (a :: Type)) where
  abstractPEVars ns1 ns2 (n :: Name a)
    | Just memb <- nameMember ns1 n
    = return ( $(mkClosed
                 [| \prxs1 prxs2 memb ->
                   nuMulti prxs1 $ \ns ->
                   nuMulti prxs2 (const $ mapRListLookup memb ns) |])
               `clApply` closedProxies ns1 `clApply` closedProxies ns2
               `clApply` toClosed memb)
  abstractPEVars _ _ _ = Nothing

instance AbstractVars a => AbstractVars (Mb (ctx :: RList CrucibleType) a) where
  abstractPEVars ns1 ns2 mb =
    mbLift $
    nuMultiWithElim1
    (\ns a ->
      clApply ( $(mkClosed [| \prxs -> fmap (mbSeparate prxs) |])
                `clApply` closedProxies ns) <$>
      abstractPEVars ns1 (appendMapRList ns2 ns) a)
    mb

instance AbstractVars a => AbstractVars (Mb (ctx :: RList Type) a) where
  abstractPEVars ns1 ns2 mb =
    mbLift $
    nuMultiWithElim1
    (\ns a ->
      clApply ( $(mkClosed [| \prxs -> fmap mbSwap . mbSeparate prxs |])
                `clApply` closedProxies ns) <$>
      abstractPEVars (appendMapRList ns1 ns) ns2 a)
    mb

instance AbstractVars (MapRList Name (ctx :: RList CrucibleType)) where
  abstractPEVars ns1 ns2 MNil = absVarsReturnH ns1 ns2 $(mkClosed [| MNil |])
  abstractPEVars ns1 ns2 (ns :>: n) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (:>:) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ns
    `clMbMbApplyM` abstractPEVars ns1 ns2 n

instance AbstractVars Integer where
  abstractPEVars ns1 ns2 i = absVarsReturnH ns1 ns2 (toClosed i)

instance AbstractVars Char where
  abstractPEVars ns1 ns2 c = absVarsReturnH ns1 ns2 (toClosed c)

instance AbstractVars Bool where
  abstractPEVars ns1 ns2 b = absVarsReturnH ns1 ns2 (toClosed b)

instance AbstractVars (Member ctx a) where
  abstractPEVars ns1 ns2 memb = absVarsReturnH ns1 ns2 (toClosed memb)

instance AbstractVars a => AbstractVars (Maybe a) where
  abstractPEVars ns1 ns2 Nothing =
    absVarsReturnH ns1 ns2 $(mkClosed [| Nothing |])
  abstractPEVars ns1 ns2 (Just a) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Just |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a

instance AbstractVars a => AbstractVars [a] where
  abstractPEVars ns1 ns2 [] =
    absVarsReturnH ns1 ns2 $(mkClosed [| [] |])
  abstractPEVars ns1 ns2 (a:as) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (:) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a
    `clMbMbApplyM` abstractPEVars ns1 ns2 as

instance (AbstractVars a, AbstractVars b) => AbstractVars (a,b) where
  abstractPEVars ns1 ns2 (a,b) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (,) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a
    `clMbMbApplyM` abstractPEVars ns1 ns2 b

instance AbstractVars (PermExpr a) where
  abstractPEVars ns1 ns2 (PExpr_Var x) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Var |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 x
  abstractPEVars ns1 ns2 PExpr_Unit =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Unit |])
  abstractPEVars ns1 ns2 (PExpr_Bool b) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Bool |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 b
  abstractPEVars ns1 ns2 (PExpr_Nat i) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Nat |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 i
  abstractPEVars ns1 ns2 (PExpr_BV factors k) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_BV |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 factors
    `clMbMbApplyM` abstractPEVars ns1 ns2 k
  abstractPEVars ns1 ns2 (PExpr_Struct es) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Struct |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 es
  abstractPEVars ns1 ns2 PExpr_Always =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Always |])
  abstractPEVars ns1 ns2 (PExpr_LLVMWord e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_LLVMWord |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (PExpr_LLVMOffset x e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_LLVMOffset |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 x
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (PExpr_Fun fh) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_Fun |]) `clApply` toClosed fh)
  abstractPEVars ns1 ns2 PExpr_PermListNil =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_PermListNil |]))
  abstractPEVars ns1 ns2 (PExpr_PermListCons e p l) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_PermListCons |]))
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 p
    `clMbMbApplyM` abstractPEVars ns1 ns2 l
  abstractPEVars ns1 ns2 (PExpr_RWModality rw) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_RWModality |])
                            `clApply` toClosed rw)

instance AbstractVars (PermExprs as) where
  abstractPEVars ns1 ns2 PExprs_Nil =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExprs_Nil |])
  abstractPEVars ns1 ns2 (PExprs_Cons es e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExprs_Cons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 es
    `clMbMbApplyM` abstractPEVars ns1 ns2 e

instance AbstractVars (BVFactor w) where
  abstractPEVars ns1 ns2 (BVFactor i x) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVFactor |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 i
    `clMbMbApplyM` abstractPEVars ns1 ns2 x

instance AbstractVars (BVRange w) where
  abstractPEVars ns1 ns2 (BVRange e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVRange |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2

instance AbstractVars (BVProp w) where
  abstractPEVars ns1 ns2 (BVProp_Eq e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_Eq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
  abstractPEVars ns1 ns2 (BVProp_InRange e r) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_InRange |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 r
  abstractPEVars ns1 ns2 (BVProp_RangeSubset r1 r2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_RangeSubset |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 r1
    `clMbMbApplyM` abstractPEVars ns1 ns2 r2
  abstractPEVars ns1 ns2 (BVProp_RangesDisjoint r1 r2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_RangesDisjoint |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 r1
    `clMbMbApplyM` abstractPEVars ns1 ns2 r2

instance AbstractVars (AtomicPerm a) where
  abstractPEVars ns1 ns2 (Perm_LLVMField fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMField |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 (Perm_LLVMArray ap) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMArray |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ap
  abstractPEVars ns1 ns2 (Perm_LLVMFree e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMFree |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (Perm_LLVMFunPtr fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMFunPtr |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 Perm_IsLLVMPtr =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_IsLLVMPtr |])
  abstractPEVars ns1 ns2 (Perm_LLVMFrame fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMFrame |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 (Perm_LOwned eps) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LOwned |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 eps
  abstractPEVars ns1 ns2 (Perm_LCurrent e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LCurrent |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (Perm_Fun fperm) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_Fun |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fperm
  abstractPEVars ns1 ns2 (Perm_BVProp prop) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_BVProp |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 prop

instance AbstractVars (ValuePerm a) where
  abstractPEVars ns1 ns2 (ValPerm_Eq e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Eq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (ValPerm_Or p1 p2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Or |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 p1
    `clMbMbApplyM` abstractPEVars ns1 ns2 p2
  abstractPEVars ns1 ns2 (ValPerm_Exists p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Exists |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 p
  abstractPEVars ns1 ns2 (ValPerm_Rec n args) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Rec |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 n
    `clMbMbApplyM` abstractPEVars ns1 ns2 args
  abstractPEVars ns1 ns2 (ValPerm_Conj ps) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Conj |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps

instance AbstractVars (ValuePerms as) where
  abstractPEVars ns1 ns2 ValPerms_Nil =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerms_Nil |])
  abstractPEVars ns1 ns2 (ValPerms_Cons ps p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerms_Cons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars RWModality where
  abstractPEVars ns1 ns2 Write =
    absVarsReturnH ns1 ns2 $(mkClosed [| Write |])
  abstractPEVars ns1 ns2 Read =
    absVarsReturnH ns1 ns2 $(mkClosed [| Read |])

instance AbstractVars (LLVMFieldPerm w) where
  abstractPEVars ns1 ns2 (LLVMFieldPerm rw ls off p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMFieldPerm |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 rw
    `clMbMbApplyM` abstractPEVars ns1 ns2 ls
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (LLVMArrayPerm w) where
  abstractPEVars ns1 ns2 (LLVMArrayPerm off len str flds bs) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMArrayPerm |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
    `clMbMbApplyM` abstractPEVars ns1 ns2 len
    `clMbMbApplyM` abstractPEVars ns1 ns2 str
    `clMbMbApplyM` abstractPEVars ns1 ns2 flds
    `clMbMbApplyM` abstractPEVars ns1 ns2 bs

instance AbstractVars (LLVMArrayIndex w) where
  abstractPEVars ns1 ns2 (LLVMArrayIndex ix fld_num) =
    absVarsReturnH ns1 ns2 $(mkClosed
                             [| \ix' fld_num' ->
                               LLVMArrayIndex ix' $ fromInteger fld_num' |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ix
    `clMbMbApplyM` abstractPEVars ns1 ns2 (toInteger fld_num)

instance AbstractVars (LLVMArrayBorrow w) where
  abstractPEVars ns1 ns2 (FieldBorrow ix) =
    absVarsReturnH ns1 ns2 $(mkClosed [| FieldBorrow |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ix
  abstractPEVars ns1 ns2 (RangeBorrow r) =
    absVarsReturnH ns1 ns2 $(mkClosed [| RangeBorrow |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 r

instance AbstractVars (DistPerms ps) where
  abstractPEVars ns1 ns2 DistPermsNil =
    absVarsReturnH ns1 ns2 $(mkClosed [| DistPermsNil |])
  abstractPEVars ns1 ns2 (DistPermsCons perms x p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| DistPermsCons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms
    `clMbMbApplyM` abstractPEVars ns1 ns2 x `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (FunPerm ghosts args ret) where
  abstractPEVars ns1 ns2 (FunPerm ghosts args ret perms_in perms_out) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| FunPerm |])
     `clApply` toClosed ghosts `clApply` toClosed args `clApply` toClosed ret)
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms_in
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms_out

{- FIXME HERE NOW: do we need these instances?
instance AbstractVars FunTypeEnvEntry where
  abstractPEVars ns1 ns2 (FunTypeEnvEntry h fun_perm) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| FunTypeEnvEntry |]) `clApply` toClosed h)
    `clMbMbApplyM` abstractPEVars ns1 ns2 fun_perm

instance AbstractVars FunTypeEnv where
  abstractPEVars ns1 ns2 (FunTypeEnv entries) =
    absVarsReturnH ns1 ns2
    $(mkClosed [| FunTypeEnv |]) `clMbMbApplyM` abstractPEVars ns1 ns2 entries
-}

instance AbstractVars (RecPermName args a) where
  abstractPEVars ns1 ns2 (RecPermName n tp args) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| RecPermName |])
     `clApply` toClosed n `clApply` toClosed tp `clApply` toClosed args)

instance AbstractVars (RecPermArgs args) where
  abstractPEVars ns1 ns2 RecPermArgs_Nil =
    absVarsReturnH ns1 ns2 $(mkClosed [| RecPermArgs_Nil |])
  abstractPEVars ns1 ns2 (RecPermArgs_Cons args arg) =
    absVarsReturnH ns1 ns2 $(mkClosed [| RecPermArgs_Cons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 args
    `clMbMbApplyM` abstractPEVars ns1 ns2 arg

instance AbstractVars (RecPermArg a) where
  abstractPEVars ns1 ns2 (RecPermArg_Lifetime l) =
    absVarsReturnH ns1 ns2 $(mkClosed [| RecPermArg_Lifetime |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 l
  abstractPEVars ns1 ns2 (RecPermArg_RWModality rw) =
    absVarsReturnH ns1 ns2 $(mkClosed [| RecPermArg_RWModality |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 rw


----------------------------------------------------------------------
-- * Permission Environments
----------------------------------------------------------------------

-- | A function permission that existentially quantifies the @ghosts@ types
data SomeFunPerm args ret where
  SomeFunPerm :: FunPerm ghosts args ret -> SomeFunPerm args ret

-- | An entry in a permission environment that associates a permission and
-- corresponding SAW identifier with a Crucible function handle
data PermEnvFunEntry where
  PermEnvFunEntry :: args ~ CtxToRList cargs => FnHandle cargs ret ->
                     FunPerm ghosts args ret -> Ident ->
                     PermEnvFunEntry

-- | An existentially quantified 'RecPerm' (FIXME: is this needed?)
data SomeRecPerm where
  SomeRecPerm :: RecPerm args a -> SomeRecPerm

-- | An entry in a permission environment that associates a 'GlobalSymbol' with
-- a permission and a translation of that permission
data PermEnvGlobalEntry where
  PermEnvGlobalEntry :: (1 <= w, KnownNat w) => GlobalSymbol ->
                        ValuePerm (LLVMPointerType w) -> [OpenTerm] ->
                        PermEnvGlobalEntry

-- | A permission environment that maps function names, recursive permission
-- names, and 'GlobalSymbols' to their respective permission structures
data PermEnv = PermEnv {
  permEnvFunPerms :: [PermEnvFunEntry],
  permEnvRecPerms :: [SomeRecPerm],
  permEnvGlobalSyms :: [PermEnvGlobalEntry]
  }

$(mkNuMatching [t| forall args ret. SomeFunPerm args ret |])
$(mkNuMatching [t| PermEnvFunEntry |])
$(mkNuMatching [t| SomeRecPerm |])
$(mkNuMatching [t| PermEnvGlobalEntry |])
$(mkNuMatching [t| PermEnv |])

-- | Add some 'PermEnvGlobalEntry's to a 'PermEnv'
permEnvAddGlobalSyms :: PermEnv -> [PermEnvGlobalEntry] -> PermEnv
permEnvAddGlobalSyms env entries = env { permEnvGlobalSyms =
                                           permEnvGlobalSyms env ++ entries }

-- | Look up a 'FnHandle' by name in a 'PermEnv'
lookupFunHandle :: PermEnv -> String -> Maybe SomeHandle
lookupFunHandle env str =
  case find (\(PermEnvFunEntry h _ _) ->
              handleName h == fromString str) (permEnvFunPerms env) of
    Just (PermEnvFunEntry h _ _) -> Just (SomeHandle h)
    Nothing -> Nothing

-- | Look up the function permission and SAW translation for a 'FnHandle'
lookupFunPerm :: PermEnv -> FnHandle cargs ret ->
                 Maybe (SomeFunPerm (CtxToRList cargs) ret, Ident)
lookupFunPerm env = helper (permEnvFunPerms env) where
  helper :: [PermEnvFunEntry] -> FnHandle cargs ret ->
            Maybe (SomeFunPerm (CtxToRList cargs) ret, Ident)
  helper [] _ = Nothing
  helper ((PermEnvFunEntry h' fun_perm ident):_) h
    | Just Refl <- testEquality (handleType h') (handleType h)
    , h' == h
    = Just (SomeFunPerm fun_perm, ident)
  helper (_:entries) h = helper entries h

-- | Look up a 'RecPermName' by name in a 'PermEnv'
lookupRecPermName :: PermEnv -> String -> Maybe SomeRecPermName
lookupRecPermName env str =
  case find (\(SomeRecPerm rp) ->
              recPermNameName (recPermName rp) == str) (permEnvRecPerms env) of
    Just (SomeRecPerm rp) -> Just (SomeRecPermName (recPermName rp))
    Nothing -> Nothing

-- | Look up the 'RecPerm' for a 'RecPermName' in a 'RecPermEnv'
lookupRecPerm :: PermEnv -> RecPermName args a -> Maybe (RecPerm args a)
lookupRecPerm env = helper (permEnvRecPerms env) where
  helper :: [SomeRecPerm] -> RecPermName args a -> Maybe (RecPerm args a)
  helper [] _ = Nothing
  helper (SomeRecPerm rp:_) rpn
    | Just (Refl, Refl) <- testRecPermNameEq (recPermName rp) rpn
    = Just rp
  helper (_:rps) rpn = helper rps rpn

-- | Look up the permissions and translation for a 'GlobalSymbol' at a
-- particular machine word width
lookupGlobalSymbol :: PermEnv -> GlobalSymbol -> NatRepr w ->
                      Maybe (ValuePerm (LLVMPointerType w), [OpenTerm])
lookupGlobalSymbol env = helper (permEnvGlobalSyms env) where
  helper :: [PermEnvGlobalEntry] -> GlobalSymbol -> NatRepr w ->
            Maybe (ValuePerm (LLVMPointerType w), [OpenTerm])
  helper  (PermEnvGlobalEntry sym'
            (p :: ValuePerm (LLVMPointerType w')) t:_) sym w
    | sym' == sym
    , Just Refl <- testEquality w (knownNat :: NatRepr w') =
      Just (p, t)
  helper (_:entries) sym w = helper entries sym w
  helper [] _ _ = Nothing


----------------------------------------------------------------------
-- * Permission Sets
----------------------------------------------------------------------

-- FIXME: revisit all the operations in this section and remove those that we no
-- longer need

-- | A permission set associates permissions with expression variables, and also
-- has a stack of "distinguished permissions" that are used for intro rules
data PermSet ps = PermSet { _varPermMap :: NameMap ValuePerm,
                            _distPerms :: DistPerms ps }

makeLenses ''PermSet

-- | Build a 'PermSet' with only distinguished permissions
distPermSet :: DistPerms ps -> PermSet ps
distPermSet perms = PermSet NameMap.empty perms

-- NOTE: this instance would require a NuMatching instance for NameMap...
-- $(mkNuMatching [t| forall ps. PermSet ps |])

-- | The lens for the permissions associated with a given variable
varPerm :: ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
varPerm x =
  lens
  (\(PermSet nmap _) ->
    case NameMap.lookup x nmap of
      Just p -> p
      Nothing -> ValPerm_True)
  (\(PermSet nmap ps) p -> PermSet (NameMap.insert x p nmap) ps)

-- | Set the primary permission for a variable, assuming it is currently the
-- trivial permission @true@
setVarPerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet ps
setVarPerm x p =
  over (varPerm x) $ \p' ->
  case p' of
    ValPerm_True -> p
    _ -> error "setVarPerm: permission for variable already set!"

-- | Initialize the primary permission of a variable to @true@ if it is not set
initVarPerm :: ExprVar a -> PermSet ps -> PermSet ps
initVarPerm x =
  over varPermMap $ \nmap ->
  if NameMap.member x nmap then nmap else NameMap.insert x ValPerm_True nmap

-- | Set the primary permissions for a sequence of variables to @true@
initVarPerms :: MapRList Name (as :: RList CrucibleType) -> PermSet ps ->
                PermSet ps
initVarPerms MNil perms = perms
initVarPerms (ns :>: n) perms = initVarPerms ns $ initVarPerm n perms

-- | The lens for a particular distinguished perm, checking that it is indeed
-- associated with the given variable
distPerm :: Member ps a -> ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
distPerm memb x = distPerms . nthVarPerm memb x

-- | The lens for the distinguished perm at the top of the stack, checking that
-- it has the given variable
topDistPerm :: ExprVar a -> Lens' (PermSet (ps :> a)) (ValuePerm a)
topDistPerm x = distPerms . distPermsHead x

-- | Modify the distinguished permission stack of a 'PermSet'
modifyDistPerms :: (DistPerms ps1 -> DistPerms ps2) ->
                   PermSet ps1 -> PermSet ps2
modifyDistPerms f (PermSet perms dperms) = PermSet perms $ f dperms

-- | Get all the permissions in the permission set as a sequence of
-- distinguished permissions
getAllPerms :: PermSet ps -> Some DistPerms
getAllPerms perms = helper (NameMap.assocs $ perms ^. varPermMap) where
  helper :: [NameAndElem ValuePerm] -> Some DistPerms
  helper [] = Some DistPermsNil
  helper (NameAndElem x p : xps) =
    case helper xps of
      Some ps -> Some $ DistPermsCons ps x p

-- | Delete permission @x:p@ from the permission set, assuming @x@ has precisely
-- permissions @p@, replacing it with @x:true@
deletePerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet ps
deletePerm x p =
  over (varPerm x) $ \p' ->
  if p' == p then ValPerm_True else error "deletePerm"

-- | Push a new distinguished permission onto the top of the stack
pushPerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet (ps :> a)
pushPerm x p (PermSet nmap ps) = PermSet nmap (DistPermsCons ps x p)

-- | Pop the top distinguished permission off of the stack
popPerm :: ExprVar a -> PermSet (ps :> a) -> (PermSet ps, ValuePerm a)
popPerm x (PermSet nmap pstk) =
  (PermSet nmap (pstk ^. distPermsTail), pstk ^. distPermsHead x)

-- | Drop the top distinguished permission on the stack
dropPerm :: ExprVar a -> PermSet (ps :> a) -> PermSet ps
dropPerm x = fst . popPerm x

-- | Introduce a proof of @x:true@ onto the top of the stack, which is the same
-- as a proof of an empty conjunction @x:ValPerm_Conj[]@
introConj :: ExprVar a -> PermSet ps -> PermSet (ps :> a)
introConj x = pushPerm x ValPerm_True

-- | Recombine an @x:true@ proof on the top of the stack by dropping it
recombineTrue :: ExprVar a -> PermSet (ps :> a) -> PermSet ps
recombineTrue x perms =
  case popPerm x perms of
    (perms', ValPerm_True) -> perms'
    _ -> error "recombineTrue"

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrL :: ExprVar a -> ValuePerm a -> PermSet (ps :> a) -> PermSet (ps :> a)
introOrL x p2 = over (topDistPerm x) (\p1 -> ValPerm_Or p1 p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrR :: ExprVar a -> ValuePerm a -> PermSet (ps :> a) -> PermSet (ps :> a)
introOrR x p1 = over (topDistPerm x) (\p2 -> ValPerm_Or p1 p2)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
introExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
               Binding tp (ValuePerm a) ->
               PermSet (ps :> a) -> PermSet (ps :> a)
introExists x e p_body =
  over (topDistPerm x) $ \p_old ->
  if p_old == subst (singletonSubst e) p_body then ValPerm_Exists p_body else
    error "introExists: permission on the top of the stack does not match"

-- | Replace an or permission for a given variable with its left disjunct
elimOrLeft :: ExprVar a -> PermSet (ps :> a) -> PermSet (ps :> a)
elimOrLeft x = over (topDistPerm x) orPermLeft

-- | Replace an or permission for a given variable with its right disjunct
elimOrRight :: ExprVar a -> PermSet (ps :> a) -> PermSet (ps :> a)
elimOrRight x = over (topDistPerm x) orPermRight

-- | Replace an existential permission for a given variable with its body
elimExists :: ExprVar a -> TypeRepr tp -> PermSet (ps :> a) ->
              Binding tp (PermSet (ps :> a))
elimExists x tp perms =
  nuWithElim1
  (\_ p_body -> set (topDistPerm x) p_body perms)
  (exPermBody tp $ perms ^. topDistPerm x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqRefl :: ExprVar a -> PermSet ps -> PermSet (ps :> a)
introEqRefl x = pushPerm x (ValPerm_Eq (PExpr_Var x))

-- | Copy an @x:eq(e)@ permission on the top of the stack
introEqCopy :: ExprVar a -> PermExpr a -> PermSet (ps :> a) ->
               PermSet (ps :> a :> a)
introEqCopy x e perms =
  case perms ^. topDistPerm x of
    ValPerm_Eq e' | e' == e -> pushPerm x (ValPerm_Eq e) perms
    _ -> error "introEqCopy: unexpected existing permission on variable"

-- | Cast a @y:p@ perm on the top of the stack to an @x:p@ perm using an
-- @x:eq(y)@ just below it on the stack
castVarPerm :: ExprVar a -> ExprVar a -> ValuePerm a ->
               PermSet (ps :> a :> a) -> PermSet (ps :> a)
castVarPerm x y p perms =
  let (perms', y_perm) = popPerm y perms in
  let (perms'', x_eq_y_perm) = popPerm x perms' in
  case x_eq_y_perm of
    ValPerm_Eq (PExpr_Var y') | y_perm == p && y' == y -> pushPerm x p perms''
    _ -> error "castVarPerm"

-- | Delete the @i@th atomic permission in the conjunct on the top of the stack,
-- assuming that conjunction contains the given atomic permissions, and put the
-- extracted atomic permission just below the top of the stack
extractConj :: ExprVar a -> [AtomicPerm a] -> Int ->
               PermSet (ps :> a) -> PermSet (ps :> a :> a)
extractConj x ps _ perms
  | perms ^. topDistPerm x /= ValPerm_Conj ps
  = error "extractConj: permissions on the top of the stack not as expected"
extractConj x ps i perms =
  pushPerm x (ValPerm_Conj [ps !! i]) $
  over (topDistPerm x) (deleteAtomicPerm i) perms

-- | Combine the two conjunctive permissions on the top of the stack
combineConj :: ExprVar a -> [AtomicPerm a] -> [AtomicPerm a] ->
               PermSet (ps :> a :> a) -> PermSet (ps :> a)
combineConj x ps1 ps2 perms =
  let (perms', p1) = popPerm x perms
      (perms'', p2) = popPerm x perms' in
  if p1 == ValPerm_Conj ps1 && p2 == ValPerm_Conj ps2 then
    pushPerm x (ValPerm_Conj (ps1 ++ ps2)) perms''
  else
    error "combineConj"

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEq :: ExprVar (LLVMPointerType w) ->
                  PermExpr (BVType w) -> PermExpr (BVType w) ->
                  PermSet (ps :> LLVMPointerType w) ->
                  PermSet (ps :> LLVMPointerType w)
castLLVMWordEq x e1 e2 =
  over (topDistPerm x) $ \p ->
  case p of
    ValPerm_Eq (PExpr_LLVMWord e1')
      | bvEq e1' e1 -> ValPerm_Eq (PExpr_LLVMWord e2)
    _ -> error "castLLVMWordEq: unexpected existing permission"

-- | Cast a @y:pps@ on the top of the stack to @x:(pps - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtr :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
               ExprVar (LLVMPointerType w) ->
               PermSet (ps :> LLVMPointerType w :> LLVMPointerType w) ->
               PermSet (ps :> LLVMPointerType w)
castLLVMPtr y off x perms =
  let (perms', y_ptr_perm) = popPerm y perms
      (perms'', x_eq_perm) = popPerm x perms' in
  case (y_ptr_perm, x_eq_perm) of
    (p@(ValPerm_Conj _), ValPerm_Eq (PExpr_Var y'))
      | y' == y -> pushPerm x p perms''
    (ValPerm_Conj pps, ValPerm_Eq (PExpr_LLVMOffset y' off))
      | y' == y ->
        pushPerm x (ValPerm_Conj $ mapMaybe (offsetLLVMAtomicPerm off) pps) perms''
    _ -> error "castLLVMPtr"

-- | Copy an LLVM free permission @free(e)@ on the top of the stack
copyLLVMFree :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                PermSet (ps :> LLVMPointerType w) ->
                PermSet (ps :> LLVMPointerType w :> LLVMPointerType w)
copyLLVMFree x e perms =
  case perms ^. topDistPerm x of
    p@(ValPerm_Conj [Perm_LLVMFree e']) | e' == e -> pushPerm x p perms
    _ -> error "copyLLVMFree"

-- | Cast a proof of @x:ptr(pps1, free(e1), pps2)@ on the top of the stack to
-- one of @x:ptr(pps1, free(e2), pps2)@
castLLVMFree :: ExprVar (LLVMPointerType w) -> Int ->
                PermExpr (BVType w) -> PermExpr (BVType w) ->
                PermSet (ps :> LLVMPointerType w) ->
                PermSet (ps :> LLVMPointerType w)
castLLVMFree x i e1 e2 =
  over (varPerm x . llvmPtrPerm i) $ \pp_i ->
  case pp_i of
    Perm_LLVMFree e | e == e1 -> Perm_LLVMFree e2
    _ -> error "castLLVMFree"

{-
-- | Move or copy a field permission of the form @(rw,off) |-> p@, which should
-- be the @i@th 'LVMPtrPerm' associated with @x@, into the @x:ptr(pps)@
-- permission on the top of of the stack, resulting in the permission of the
-- form @x:ptr(pps, (rw,off) |-> p)@ on the top of the stack. If it is a write
-- permission, it is moved, i.e., deleted from its original position, while if
-- it is a read permission, it is copied.
introLLVMField :: ExprVar (LLVMPointerType w) -> Int ->
                  PermSet (ps :> LLVMPointerType w) ->
                  PermSet (ps :> LLVMPointerType w)
introLLVMField x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    pp_i@(Perm_LLVMField (LLVMFieldPerm Write _ _)) ->
      over (varPerm x) (deleteLLVMPtrPerm i) $
      over (topDistPerm x) (addLLVMPtrPerm pp_i)
      perms
    pp_i@(Perm_LLVMField (LLVMFieldPerm (Read _) _ _)) ->
      over (topDistPerm x) (addLLVMPtrPerm pp_i) perms
    _ -> error "introLLVMField"
-}

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContents :: ExprVar (LLVMPointerType w) ->
                          ExprVar (LLVMPointerType w) ->
                          PermSet (ps :> LLVMPointerType w
                                   :> LLVMPointerType w) ->
                          PermSet (ps :> LLVMPointerType w)
introLLVMFieldContents x y perms =
  let (perms', y_perm) = popPerm y perms
      i = lastLLVMPtrPermIndex (perms ^. topDistPerm x) in
  over (topDistPerm x . llvmPtrPerm i)
  (\pp -> case pp of
      Perm_LLVMField fp
        | ValPerm_Eq (PExpr_Var y') <- llvmFieldContents fp , y' == y ->
            Perm_LLVMField $ fp { llvmFieldContents = y_perm }
      _ -> error "introLLVMFieldContents")
  perms'

-- | Eliminate a permission @x:ptr(pps1,(off,S) |-> p,pps2)@ into permissions
-- @x:ptr(pps1,(off,S) |-> eq(y),pps2)@ and @y:p@ for a fresh variable @y@. If
-- the permissions for @x@ are already of this form, just return @y@.
elimLLVMFieldContents :: ExprVar (LLVMPointerType w) -> Int -> PermSet ps ->
                         Either (ExprVar (LLVMPointerType w))
                         (Binding (LLVMPointerType w) (PermSet ps))
elimLLVMFieldContents x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    Perm_LLVMField fp
      | ValPerm_Eq (PExpr_Var y) <- llvmFieldContents fp -> Left y
    Perm_LLVMField fp ->
      Right $ nu $ \y ->
      set (varPerm y) (llvmFieldContents fp) $
      set (varPerm x . llvmPtrPerm i)
      (Perm_LLVMField $ fp { llvmFieldContents = ValPerm_Eq (PExpr_Var y) }) $
      perms
    _ -> error "elimLLVMFieldContents"

-- | Divide an array permission @x:ptr((rw,off,*stride,<len) |-> p)@ into two
-- arrays, one of length @e@ starting at @off@ and one of length @len-e@
-- starting at offset @off+e*stride@. The latter permission (at offset
-- @off+e*stride@) stays at the same index, while the former (at the original
-- offset) is moved to the end of the field permissions for @x@.
{-
divideLLVMArray :: ExprVar (LLVMPointerType w) -> Int -> PermExpr (BVType w) ->
                   PermSet ps -> PermSet ps
divideLLVMArray x i e perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    Perm_LLVMArray ap ->
      set (varPerm x . llvmPtrPerm i)
      (Perm_LLVMArray $
       ap { llvmArrayLen = bvSub (llvmArrayLen ap) e,
            llvmArrayOffset =
              bvAdd (llvmArrayOffset ap) (bvMult (arrayStrideBytes ap) e) }) $
      over (varPerm x) (addLLVMPtrPerm $
                        Perm_LLVMArray $ ap { llvmArrayLen = e }) $
      perms
    _ -> error "divideLLVMArray"
-}

-- | Perform an array indexing of the first cell of an array, by separating an
-- array permission @x:ptr((off,*stride,<len,S) |-> pps)@ into one array cell,
-- containing a copy of the pointer permissions @pps@ starting at offset @off@,
-- along with the remaining array @x:ptr((off+1,*stride,<len,S) |-> -- pps)@.
-- Return the new permission set along with the indices of the new @pps@ pointer
-- permissions.
indexLLVMArray :: ExprVar (LLVMPointerType w) -> Int -> PermSet ps ->
                  (PermSet ps, [(Int, LLVMFieldPerm w)])
indexLLVMArray x i perms =
  case perms ^. (varPerm x . llvmPtrPerm i) of
    Perm_LLVMArray ap ->
      let new_fps =
            map (offsetLLVMFieldPerm (llvmArrayOffset ap)) (llvmArrayFields ap) in
      (set (varPerm x . llvmPtrPerm i)
       (Perm_LLVMArray $ ap { llvmArrayOffset =
                            bvAdd (llvmArrayOffset ap) (bvInt 1)}) $
       over (varPerm x . llvmPtrPerms) (++ map Perm_LLVMField new_fps) $
       perms
      ,
      zip [length (perms ^. (varPerm x . llvmPtrPerms)) ..] new_fps)
    _ -> error "indexLLVMArray"

-- | Cast the the offset of the last pointer permission at the top of the stack,
-- going from @(off,S) |-> p@ to @(off',S) |-> p@, assuming that we know (or can
-- assert) that @off=off'.
castLLVMFieldOffset :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                       PermExpr (BVType w) ->
                       PermSet (ps :> LLVMPointerType w) ->
                       PermSet (ps :> LLVMPointerType w)
castLLVMFieldOffset x off off' perms =
  let i = lastLLVMPtrPermIndex (perms ^. topDistPerm x) in
  over (topDistPerm x . llvmPtrPerm i)
  (\p -> case p of
      Perm_LLVMField fp
        | llvmFieldOffset fp `bvEq` off ->
            Perm_LLVMField (fp { llvmFieldOffset = off' })
      _ -> error "castLLVMFieldOffset")
  perms

{-
FIXME: remove this...?

-- | Delete an llvm frame and its associated permissions for the pointer objects
-- that were allocated in that frame, assuming that those are the permissions
-- that are in the distinguished permission stack
deleteLLVMFrame :: ExprVar (LLVMFrameType w) -> PermSet ps -> PermSet RNil
deleteLLVMFrame frame perms
  | ValPerm_LLVMFrame fperm <- perms ^. varPerm frame
  , Some del_perms <- llvmFrameDeletionPerms fperm
  , Just Refl <- testEquality del_perms (perms ^. distPerms)
  = set (varPerm frame) ValPerm_True $
    modifyDistPerms (const DistPermsNil) perms
deleteLLVMFrame _ _ = error "deleteLLVMFrame"
-}
