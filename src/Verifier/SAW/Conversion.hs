{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Conversion
  ( Conversion(..)
  , append_bvNat
  , bvAdd_bvNat
  , bvule_bvNat
  , bvult_bvNat
  ) where

--import Control.Applicative ((<$>), pure, (<*>))
import Control.Monad (guard)
import Data.Bits
import Data.Map (Map)

import Verifier.SAW.SharedTerm (Termlike(..))
import Verifier.SAW.TypedAST

----------------------------------------------------------------------
-- Conversions

-- | These are conversions in the LCF-style term-rewriting sense: A
-- conversion is a function that takes a term and returns (possibly) a
-- rewritten term. We use conversions to model the behavior of
-- primitive operations in SAWCore.

data Conversion =
    Conversion { runConversion ::
        forall m t. (Monad m, Termlike t) => (TermF t -> m t) -> t -> Maybe (m t) }

----------------------------------------------------------------------
-- Destructors for terms

asApp :: Termlike t => t -> Maybe (t, t)
asApp (unwrapTermF -> FTermF (App x y)) = Just (x, y)
asApp _ = Nothing

infixl 8 <:>

(<:>) :: Termlike t => (t -> Maybe a) -> (t -> Maybe b) -> (t -> Maybe (a, b))
(<:>) f1 f2 t =
    do (t1, t2) <- asApp t
       x1 <- f1 t1
       x2 <- f2 t2
       Just (x1, x2)

asNatLit :: Termlike t => t -> Maybe Integer
asNatLit (unwrapTermF -> FTermF (NatLit i)) = Just i
asNatLit _ = Nothing

asGlobalDef :: Termlike t => Ident -> t -> Maybe ()
asGlobalDef ident (unwrapTermF -> FTermF (GlobalDef ident')) | ident == ident' = Just ()
asGlobalDef _ _ = Nothing

asBoolType :: Termlike t => t -> Maybe ()
asBoolType (unwrapTermF -> FTermF (DataTypeApp ident [])) | ident == bool = Just ()
    where
      bool = mkIdent (mkModuleName ["Prelude"]) "Bool"
asBoolType _ = Nothing

asBvNatLit :: Termlike t => t -> Maybe (Integer, Integer)
asBvNatLit t =
    do (((), n), x) <- (asGlobalDef bvNat <:> asNatLit <:> asNatLit) t
       guard (x < bit (fromIntegral n))
       return (n, x)
    where
      bvNat = mkIdent (mkModuleName ["Prelude"]) "bvNat"

----------------------------------------------------------------------
-- Constructors for return values

mkBool :: Monad m => (TermF t -> m t) -> Bool -> m t
mkBool mk b = mk (FTermF (CtorApp (if b then idTrue else idFalse) []))
    where
      idTrue = mkIdent (mkModuleName ["Prelude"]) "True"
      idFalse = mkIdent (mkModuleName ["Prelude"]) "False"

mkBvNat :: Monad m => (TermF t -> m t) -> Integer -> Integer -> m t
mkBvNat mk n x =
    do n' <- mk (FTermF (NatLit n))
       x' <- mk (FTermF (NatLit x))
       t0 <- mk (FTermF (GlobalDef bvNat))
       t1 <- mk (FTermF (App t0 n'))
       t2 <- mk (FTermF (App t1 x'))
       return t2
    where
       bvNat = mkIdent (mkModuleName ["Prelude"]) "bvNat"

----------------------------------------------------------------------
-- Conversions for Prelude operations

append_bvNat =
    Conversion $ \mk t ->
        do ((((((), m), n), _), (_, x)), (_, y)) <-
               (asGlobalDef append <:> asNatLit <:> asNatLit <:>
                   asBoolType <:> asBvNatLit <:> asBvNatLit) t
           return $ mkBvNat mk (m + n) (shiftL x (fromIntegral n) .|. y)
           -- ^ Assuming big-endian order
    where
      append = mkIdent (mkModuleName ["Prelude"]) "append"

bvAdd_bvNat =
    Conversion $ \mk t ->
        do ((((), n), (_, x)), (_, y)) <-
               (asGlobalDef bvAdd <:> asNatLit <:> asBvNatLit <:> asBvNatLit) t
           let mask = bit (fromIntegral n) - 1
           return $ mkBvNat mk n ((x + y) .&. mask)
    where
      bvAdd = mkIdent (mkModuleName ["Prelude"]) "bvAdd"

bvule_bvNat =
    Conversion $ \mk t ->
        do ((((), n), (_, x)), (_, y)) <-
               (asGlobalDef bvule <:> asNatLit <:> asBvNatLit <:> asBvNatLit) t
           return $ mkBool mk (x <= y)
    where
      bvule = mkIdent (mkModuleName ["Prelude"]) "bvule"

bvult_bvNat =
    Conversion $ \mk t ->
        do ((((), n), (_, x)), (_, y)) <-
               (asGlobalDef bvult <:> asNatLit <:> asBvNatLit <:> asBvNatLit) t
           return $ mkBool mk (x < y)
    where
      bvult = mkIdent (mkModuleName ["Prelude"]) "bvult"

slice_bvNat =
    Conversion $ \mk t ->
        do ((((((), _), i), n), j), (m, x)) <-
               (asGlobalDef slice <:> asBoolType <:>
                   asNatLit <:> asNatLit <:> asNatLit <:> asBvNatLit) t
           guard (i + n + j == m)
           let mask = bit (fromIntegral n) - 1
           return $ mkBvNat mk n (shiftR x (fromIntegral j) .&. mask)
           -- ^ Assuming big-endian order
    where
      slice = mkIdent (mkModuleName ["Prelude"]) "slice"
