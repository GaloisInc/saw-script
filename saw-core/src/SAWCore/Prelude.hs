{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : SAWCore.Prelude
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Prelude
  ( Module
  , module SAWCore.Prelude
  , module SAWCore.Prelude.Constants
  ) where

import qualified Data.Map as Map

import SAWCore.ParserUtils
import SAWCore.Prelude.Constants
import SAWCore.SharedTerm
import SAWCore.FiniteValue
import SAWCore.Term.Pretty (showTerm)

import SAWCore.Simulator.Concrete (evalSharedTerm)
import SAWCore.Simulator.Value (asFirstOrderTypeValue)


$(defineModuleFromFileWithFns
  "preludeModule" "scLoadPreludeModule" "saw-core/prelude/Prelude.sawcore")

-- | Given two terms, compute a term representing a decidable
--   equality test between them.  The terms are assumed to
--   be of the same type, which must be a first-order type.
--   The returned term will be of type @Bool@.
scEq :: SharedContext -> Term -> Term -> IO Term
scEq sc x y = do
  xty <- scTypeOf sc x
  mmap <- scGetModuleMap sc
  case asFirstOrderTypeValue (evalSharedTerm mmap mempty mempty xty) of
    Just fot -> scDecEq sc fot (Just (x,y))
    Nothing  -> fail ("scEq: expected first order type, but got: " ++ showTerm xty)

-- | Given a first-order type, return the decidable equality
--   operation on that type.  If arguments are provided, they
--   will be applied, returning a value of type @Bool@.  If no
--   arguments are provided a function of type @tp -> tp -> Bool@
--   will be returned.
scDecEq ::
  SharedContext ->
  FirstOrderType    {- ^ Type of elements to test for equality -} ->
  Maybe (Term,Term) {- ^ optional arguments to apply -} ->
  IO Term
scDecEq sc fot args = case fot of
  FOTBit ->
    do fn <- scGlobalDef sc "Prelude.boolEq"
       case args of
         Nothing    -> return fn
         Just (x,y) -> scApplyAll sc fn [x,y]

  FOTInt ->
    do fn <- scGlobalDef sc "Prelude.intEq"
       case args of
         Nothing    -> return fn
         Just (x,y) -> scApplyAll sc fn [x,y]

  FOTIntMod m ->
    do fn <- scGlobalDef sc "Prelude.intModEq"
       m' <- scNat sc m
       case args of
         Nothing    -> scApply sc fn m'
         Just (x,y) -> scApplyAll sc fn [m',x,y]

  FOTVec w FOTBit ->
    do fn <- scGlobalDef sc "Prelude.bvEq"
       w' <- scNat sc w
       case args of
         Nothing    -> scApply sc fn w'
         Just (x,y) -> scApplyAll sc fn [w',x,y]

  FOTVec w t ->
    do fn <- scGlobalDef sc "Prelude.vecEq"
       w' <- scNat sc w
       t' <- scFirstOrderType sc t
       subFn <- scDecEq sc t Nothing
       case args of
         Nothing    -> scApplyAll sc fn [w',t',subFn]
         Just (x,y) -> scApplyAll sc fn [w',t',subFn,x,y]

  FOTArray a b ->
    do a' <- scFirstOrderType sc a
       b' <- scFirstOrderType sc b
       fn <- scGlobalDef sc "Prelude.arrayEq"
       case args of
         Nothing    -> scApplyAll sc fn [a',b']
         Just (x,y) -> scApplyAll sc fn [a',b',x,y]

  FOTTuple []  ->
    case args of
      Nothing -> scGlobalDef sc "Prelude.unitEq"
      Just _  -> scBool sc True

  FOTTuple [t] -> scDecEq sc t args

  FOTTuple (t:ts) ->
    do fnLeft  <- scDecEq sc t Nothing
       fnRight <- scDecEq sc (FOTTuple ts) Nothing
       fn      <- scGlobalDef sc "Prelude.pairEq"
       t'      <- scFirstOrderType sc t
       ts'     <- scFirstOrderType sc (FOTTuple ts)
       case args of
         Nothing    -> scApplyAll sc fn [t',ts',fnLeft,fnRight]
         Just (x,y) -> scApplyAll sc fn [t',ts',fnLeft,fnRight,x,y]

  FOTRec fs ->
    case args of
      Just (x,y) ->
           mkRecordEqBody (Map.toList fs) x y

      Nothing -> 
        do x <- scLocalVar sc 1
           y <- scLocalVar sc 0
           tp   <- scFirstOrderType sc fot
           body <-  mkRecordEqBody (Map.toList fs) x y
           scLambdaList sc [("x",tp),("y",tp)] body

 where
  mkRecordEqBody [] _x _y = scBool sc True
  mkRecordEqBody [(f,tp)] x y =
     do xf <- scRecordSelect sc x f
        yf <- scRecordSelect sc y f
        scDecEq sc tp (Just (xf,yf))
  mkRecordEqBody ((f,tp):fs) x y =
     do xf   <- scRecordSelect sc x f
        yf   <- scRecordSelect sc y f
        fp  <- scDecEq sc tp (Just (xf,yf))
        fsp <- mkRecordEqBody fs x y
        scAnd sc fp fsp

-- | For backwards compatibility: @Bool@ used to be a datatype, and so its
-- creation function was called @scPrelude_Bool@ instead of
-- @scApplyPrelude_Bool@
scPrelude_Bool :: SharedContext -> IO Term
scPrelude_Bool = scApplyPrelude_Bool
