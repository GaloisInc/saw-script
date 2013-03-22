{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Conversion
  ( Conversion
  , runConversion
  , TermBuilder
  , runTermBuilder
  , append_bvNat
  , bvAdd_bvNat
  , bvule_bvNat
  , bvult_bvNat
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad (guard, (>=>))
import Data.Bits
import Data.Map (Map)

import Verifier.SAW.SharedTerm (Termlike(..))
import qualified Verifier.SAW.TermNet as Net
import Verifier.SAW.TypedAST

----------------------------------------------------------------------
-- Matchers for terms

data Matcher t a = Matcher Net.Pat (t -> Maybe a)

thenMatcher :: Matcher t a -> (a -> Maybe b) -> Matcher t b
thenMatcher (Matcher pat match) f = Matcher pat (match >=> f)

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

mkBool :: Bool -> TermBuilder t
mkBool b = TermBuilder $ \mk ->
    mk (FTermF (CtorApp (if b then idTrue else idFalse) []))
    where
      idTrue = mkIdent (mkModuleName ["Prelude"]) "True"
      idFalse = mkIdent (mkModuleName ["Prelude"]) "False"

mkNatLit :: Integer -> TermBuilder t
mkNatLit n = TermBuilder $ \mk -> mk (FTermF (NatLit n))

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

append_bvNat :: Termlike t => Conversion t
append_bvNat =
    Conversion $
    thenMatcher (asGlobalDef append <:> asNatLit <:> asNatLit <:>
                 asBoolType <:> asBvNatLit <:> asBvNatLit)
    (\((((((), m), n), _), (_, x)), (_, y)) ->
         return $ mkBvNat (m + n) (shiftL x (fromIntegral n) .|. y))
           -- ^ Assuming big-endian order
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

slice_bvNat :: Termlike t => Conversion t
slice_bvNat =
    Conversion $
    thenMatcher
    (asGlobalDef slice <:> asBoolType <:>
     asNatLit <:> asNatLit <:> asNatLit <:> asBvNatLit)
    (\((((((), _), i), n), j), (m, x)) ->
         guard (i + n + j == m) >>
         let mask = bit (fromIntegral n) - 1
         in return $ mkBvNat n (shiftR x (fromIntegral j) .&. mask))
           -- ^ Assuming big-endian order
    where
      slice = mkIdent (mkModuleName ["Prelude"]) "slice"
