{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Conversion
  ( Conversion
  , runConversion
  , TermBuilder
  , runTermBuilder
  , natConversions
  , finConversions
  , vecConversions
  , bvConversions
  , finInc_FinVal
  , finIncLim_FinVal
  , succ_NatLit
  , addNat_NatLit
  , get_VecLit
  , append_VecLit
  , append_bvNat
  , bvAdd_bvNat
  , bvSub_bvNat
  , bvule_bvNat
  , bvult_bvNat
  , get_bvNat
  , slice_bvNat
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad (guard, (>=>))
import Data.Bits
import Data.Map (Map)
import qualified Data.Vector as V

import Verifier.SAW.SharedTerm (Termlike(..))
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

----------------------------------------------------------------------
-- Matchers for terms

data Matcher t a = Matcher Net.Pat (t -> Maybe a)

thenMatcher :: Matcher t a -> (a -> Maybe b) -> Matcher t b
thenMatcher (Matcher pat match) f = Matcher pat (match >=> f)

asAny :: Matcher t t
asAny = Matcher Net.Var Just

infixl 8 <:>

(<:>) :: Termlike t => Matcher t a -> Matcher t b -> Matcher t (a, b)
(<:>) (Matcher p1 f1) (Matcher p2 f2) = Matcher (Net.App p1 p2) match
    where
      match (unwrapTermF -> FTermF (App t1 t2)) = (,) <$> f1 t1 <*> f2 t2
      match _ = Nothing

destNatLit :: Termlike t => t -> Maybe Integer
destNatLit (unwrapTermF -> FTermF (NatLit i)) = Just i
destNatLit _ = Nothing

asNatLit :: Termlike t => Matcher t Integer
asNatLit = Matcher Net.Var match
    where
      match (unwrapTermF -> FTermF (NatLit i)) = Just i
      match _ = Nothing

asVecLit :: Termlike t => Matcher t (t, V.Vector t)
asVecLit = Matcher Net.Var match
    where
      match (unwrapTermF -> FTermF (ArrayValue t xs)) = Just (t, xs)
      match _ = Nothing

asGlobalDef :: Termlike t => Ident -> Matcher t ()
asGlobalDef ident = Matcher (Net.Atom (show ident)) match
    where
      match (unwrapTermF -> FTermF (GlobalDef ident')) | ident == ident' = Just ()
      match _ = Nothing

asBoolType :: Termlike t => Matcher t ()
asBoolType = Matcher (Net.Atom (show bool)) match
    where
      match (unwrapTermF -> FTermF (DataTypeApp ident [])) | ident == bool = Just ()
      match _ = Nothing
      bool = mkIdent (mkModuleName ["Prelude"]) "Bool"

asFinValLit :: Termlike t => Matcher t (Integer, Integer)
asFinValLit = Matcher pat match
    where
      pat = Net.App (Net.App (Net.Atom (show finval)) Net.Var) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x, y]))
          | ident == finval = (,) <$> destNatLit x <*> destNatLit y
      match _ = Nothing
      finval = mkIdent (mkModuleName ["Prelude"]) "FinVal"

asSuccLit :: Termlike t => Matcher t Integer
asSuccLit = Matcher pat match
    where
      pat = Net.App (Net.Atom (show succ)) Net.Var
      match (unwrapTermF -> FTermF (CtorApp ident [x]))
          | ident == succ = destNatLit x
      match _ = Nothing
      succ = mkIdent (mkModuleName ["Prelude"]) "Succ"

asBvNatLit :: Termlike t => Matcher t (Integer, Integer)
asBvNatLit =
    thenMatcher (asGlobalDef bvNat <:> asNatLit <:> asNatLit) $
        \(((), n), x) -> guard (x < bit (fromIntegral n)) >> return (n, x)
    where
      bvNat = mkIdent (mkModuleName ["Prelude"]) "bvNat"

----------------------------------------------------------------------
-- Term builders

newtype TermBuilder t =
    TermBuilder { runTermBuilder :: forall m. Monad m => (TermF t -> m t) -> m t }

mkAny :: t -> TermBuilder t
mkAny t = TermBuilder $ \mk -> return t

mkBool :: Bool -> TermBuilder t
mkBool b = TermBuilder $ \mk ->
    mk (FTermF (CtorApp (if b then idTrue else idFalse) []))
    where
      idTrue = mkIdent (mkModuleName ["Prelude"]) "True"
      idFalse = mkIdent (mkModuleName ["Prelude"]) "False"

mkNatLit :: Integer -> TermBuilder t
mkNatLit n = TermBuilder $ \mk -> mk (FTermF (NatLit n))

mkVecLit :: t -> V.Vector t -> TermBuilder t
mkVecLit t xs = TermBuilder $ \mk -> mk (FTermF (ArrayValue t xs))

mkFinVal :: Integer -> Integer -> TermBuilder t
mkFinVal i j = TermBuilder $ \mk ->
    do i' <- mk (FTermF (NatLit i))
       j' <- mk (FTermF (NatLit j))
       mk (FTermF (CtorApp finval [i', j']))
    where
      finval = mkIdent (mkModuleName ["Prelude"]) "FinVal"

mkBvNat :: Integer -> Integer -> TermBuilder t
mkBvNat n x = TermBuilder $ \mk ->
    do n' <- mk (FTermF (NatLit n))
       x' <- mk (FTermF (NatLit x))
       t0 <- mk (FTermF (GlobalDef bvNat))
       t1 <- mk (FTermF (App t0 n'))
       t2 <- mk (FTermF (App t1 x'))
       return t2
    where
       bvNat = mkIdent (mkModuleName ["Prelude"]) "bvNat"

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

newtype Conversion t = Conversion (Matcher t (TermBuilder t))

runConversion :: Conversion t -> t -> Maybe (TermBuilder t)
runConversion (Conversion (Matcher _ f)) = f

instance Net.Pattern (Conversion t) where
    toPat (Conversion (Matcher pat _)) = pat

----------------------------------------------------------------------
-- Conversions for Prelude operations

-- | Conversions for operations on Nat literals
natConversions :: Termlike t => [Conversion t]
natConversions = [succ_NatLit, addNat_NatLit]

succ_NatLit :: Termlike t => Conversion t
succ_NatLit =
    Conversion $ thenMatcher asSuccLit (\n -> return $ mkNatLit (n + 1))

addNat_NatLit :: Termlike t => Conversion t
addNat_NatLit =
    Conversion $
    thenMatcher (asGlobalDef addNat <:> asNatLit <:> asNatLit)
    (\(((), m), n) -> return $ mkNatLit (m + n))
    where
      addNat = mkIdent (mkModuleName ["Prelude"]) "addNat"

-- | Conversions for operations on Fin literals
finConversions :: Termlike t => [Conversion t]
finConversions = [finInc_FinVal, finIncLim_FinVal]

finInc_FinVal :: Termlike t => Conversion t
finInc_FinVal =
    Conversion $
    thenMatcher (asGlobalDef finInc <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal (m + i) j))
    where
      finInc = mkIdent (mkModuleName ["Prelude"]) "finInc"

finIncLim_FinVal :: Termlike t => Conversion t
finIncLim_FinVal =
    Conversion $
    thenMatcher (asGlobalDef finIncLim <:> asNatLit <:> asNatLit <:> asFinValLit)
    (\((((), m), n), (i, j)) ->
         guard (n == i + j + 1) >> return (mkFinVal i (m + j)))
    where
      finIncLim = mkIdent (mkModuleName ["Prelude"]) "finIncLim"

-- | Conversions for operations on vector literals
vecConversions :: Termlike t => [Conversion t]
vecConversions = [get_VecLit, append_VecLit]

get_VecLit :: Termlike t => Conversion t
get_VecLit =
    Conversion $
    thenMatcher (asGlobalDef get <:> asNatLit <:> asAny <:> asVecLit <:> asFinValLit)
    (\(((((), n), e), (_, xs)), (i, j)) ->
         return $ mkAny ((V.!) xs (fromIntegral i)))
    where
      get = mkIdent (mkModuleName ["Prelude"]) "get"

append_VecLit :: Termlike t => Conversion t
append_VecLit =
    Conversion $
    thenMatcher (asGlobalDef append <:> asNatLit <:> asNatLit <:> asAny <:> asVecLit <:> asVecLit)
    (\((((((), m), n), e), (_, xs)), (_, ys)) ->
         return $ mkVecLit e ((V.++) xs ys))
    where
      append = mkIdent (mkModuleName ["Prelude"]) "append"

-- | Conversions for operations on bitvector literals
bvConversions :: Termlike t => [Conversion t]
bvConversions =
    [append_bvNat, bvAdd_bvNat, bvSub_bvNat, bvule_bvNat, bvult_bvNat, get_bvNat, slice_bvNat]

append_bvNat :: Termlike t => Conversion t
append_bvNat =
    Conversion $
    thenMatcher (asGlobalDef append <:> asNatLit <:> asNatLit <:>
                 asBoolType <:> asBvNatLit <:> asBvNatLit)
    (\((((((), m), n), _), (_, x)), (_, y)) ->
--         return $ mkBvNat (m + n) (shiftL x (fromIntegral n) .|. y)) -- ^ Assuming big-endian order
         return $ mkBvNat (m + n) (x .|. shiftL y (fromIntegral m))) -- ^ Assuming little-endian order
    where
      append = mkIdent (mkModuleName ["Prelude"]) "append"

bvAdd_bvNat :: Termlike t => Conversion t
bvAdd_bvNat =
    Conversion $
    thenMatcher (asGlobalDef bvAdd <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), n), (_, x)), (_, y)) ->
         let mask = bit (fromIntegral n) - 1
         in return $ mkBvNat n ((x + y) .&. mask))
    where
      bvAdd = mkIdent (mkModuleName ["Prelude"]) "bvAdd"

bvSub_bvNat :: Termlike t => Conversion t
bvSub_bvNat =
    Conversion $
    thenMatcher (asGlobalDef bvSub <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), n), (_, x)), (_, y)) ->
         let mask = bit (fromIntegral n) - 1
         in return $ mkBvNat n ((x - y) .&. mask))
    where
      bvSub = mkIdent (mkModuleName ["Prelude"]) "bvSub"

bvule_bvNat :: Termlike t => Conversion t
bvule_bvNat =
    Conversion $
    thenMatcher (asGlobalDef bvule <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), n), (_, x)), (_, y)) -> return $ mkBool (x <= y))
    where
      bvule = mkIdent (mkModuleName ["Prelude"]) "bvule"

bvult_bvNat :: Termlike t => Conversion t
bvult_bvNat =
    Conversion $
    thenMatcher (asGlobalDef bvult <:> asNatLit <:> asBvNatLit <:> asBvNatLit)
    (\((((), n), (_, x)), (_, y)) -> return $ mkBool (x < y))
    where
      bvult = mkIdent (mkModuleName ["Prelude"]) "bvult"

get_bvNat :: Termlike t => Conversion t
get_bvNat =
    Conversion $
    thenMatcher
    (asGlobalDef get <:> asNatLit <:> asBoolType <:> asBvNatLit <:> asFinValLit)
    (\(((((), n), ()), (n', x)), (i, j)) ->
--         return $ mkBool (testBit x (fromIntegral j))) -- ^ Assuming big-endian order
         return $ mkBool (testBit x (fromIntegral i))) -- ^ Assuming little-endian order
    where
      get = mkIdent (mkModuleName ["Prelude"]) "get"

slice_bvNat :: Termlike t => Conversion t
slice_bvNat =
    Conversion $
    thenMatcher
    (asGlobalDef slice <:> asBoolType <:>
     asNatLit <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((((), _), i), n), j), (m, x)) ->
         guard (i + n + j == m) >>
         let mask = bit (fromIntegral n) - 1
--         in return $ mkBvNat n (shiftR x (fromIntegral j) .&. mask)) -- ^ Assuming big-endian order
         in return $ mkBvNat n (shiftR x (fromIntegral i) .&. mask)) -- ^ Assuming little-endian order
    where
      slice = mkIdent (mkModuleName ["Prelude"]) "slice"
