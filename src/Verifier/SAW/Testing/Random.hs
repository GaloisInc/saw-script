{-# LANGUAGE DoAndIfThenElse #-}
-- |
-- Module      :  Verifier.SAW.Testing.Random
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  jhendrix@galois.com, conathan@galois.com
-- Stability   :  experimental
-- Portability :  portable
--
-- This module generates random values for 'FiniteValue.FiniteType' types.
--
-- Based on 'Cryptol.Testing.Random'.

module Verifier.SAW.Testing.Random where

import Verifier.SAW.FiniteValue
  (asFiniteTypePure, scFiniteValue, FiniteType(..), FiniteValue(..))
import Verifier.SAW.Prim (Nat(..))
import Verifier.SAW.Recognizer (asBoolType, asPi)
import Verifier.SAW.SharedTerm
  (scApplyAll, scModule, scWhnf, SharedContext, SharedTerm)
import Verifier.SAW.Simulator.Concrete (evalSharedTerm, CExtra(..), CValue)
import Verifier.SAW.Simulator.Value (Value(..))
import Verifier.SAW.TypedAST (FieldName)
import Verifier.SAW.Utils (panic)

import Control.Applicative ((<$>))
import Data.List (unfoldr, genericTake)
import Data.Map (Map)
import qualified Data.Map as Map
import System.Random (RandomGen, split, random, randomR, newStdGen)

-- 'State FiniteValue g' ...
type Gen g = g -> (FiniteValue, g)

-- | Call @scRunTest@ many times, returning the first failure if any.
scRunTests :: RandomGen g => SharedContext s ->
  Integer -> SharedTerm s -> [Gen g] -> g -> IO (Maybe [FiniteValue], g)
scRunTests sc numTests fun gens g =
  if numTests < 0 then
    panic "scRunTests:" ["number of tests must be non-negative"]
  else
    go numTests g
  where
    go 0 g' = return (Nothing, g')
    go numTests' g' = do
      (result, g'') <- scRunTest sc fun gens g'
      case result of
        Nothing -> go (numTests' - 1) g''
        Just _counterExample -> return (result, g'')

{- | Apply a testable value to some randomly-generated arguments.
     Returns `Nothing` if the function returned `True`, or
     `Just counterexample` if it returned `False`.

    Use @scTestableType@ to compute the input generators.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
scRunTest :: RandomGen g => SharedContext s ->
  SharedTerm s -> [Gen g] -> g -> IO (Maybe [FiniteValue], g)
scRunTest sc fun gens g = do
  let (xs, g') = runGens gens g
  result <- apply xs
  case result of
    VExtra (CBool True) -> return $ (Nothing, g')
    VExtra (CBool False) -> do
      return $ (Just xs, g')
    _ -> panic "Type error while running test"
         [ "Expected a boolean, but got:"
         , show result ]
  where
    apply :: [FiniteValue] -> IO CValue
    apply xs = do
      xs' <- mapM (scFiniteValue sc) xs
      app <- scApplyAll sc fun xs'
      return $ evalSharedTerm (scModule sc) app

{- | Given a (function) type, compute generators for
the function's arguments. Currently we do not support polymorphic functions.
In principle, we could apply these to random types, and test the results. -}
scTestableType :: RandomGen g =>
  SharedContext s -> SharedTerm s -> IO (Maybe [Gen g])
scTestableType sc ty = do
  ty' <- scWhnf sc ty
  case ty' of
    (asPi -> Just (_nm, asFiniteTypePure -> Just dom, rng)) -> do
      let domGen = randomFiniteValue dom
      rngGens <- scTestableType sc rng
      return $ (domGen :) <$> rngGens
    (asBoolType -> Just ()) -> return $ Just []
    _ -> return Nothing

----------------------------------------------------------------

-- | Run a sequence of generators from left to right.
runGens :: RandomGen g => [Gen g] -> g -> ([FiniteValue], g)
runGens []         g = ([], g)
runGens (gen:gens) g = (v:vs, g'')
  where
  (v, g') = gen g
  (vs, g'') = runGens gens g'

randomFiniteValue :: RandomGen g => FiniteType -> Gen g
randomFiniteValue FTBit = randomBit
randomFiniteValue (FTVec n FTBit) = randomWord n
randomFiniteValue (FTVec n t) = randomVec n t
randomFiniteValue (FTTuple ts) = randomTuple ts
randomFiniteValue (FTRec fields) = randomRec fields

-- | Generate a random bit value.
randomBit :: RandomGen g => Gen g
randomBit g =
  let (b,g1) = random g
  in (FVBit b, g1)

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
randomWord :: RandomGen g => Nat -> Gen g
randomWord w g =
   let (val, g1) = randomR (0,2^(unNat w - 1)) g
   in (FVWord w val, g1)

{- | Generate a random vector.  Generally, this should be used for sequences
other than bits.  For sequences of bits use "randomWord".  The difference
is mostly about how the results will be displayed. -}
randomVec :: RandomGen g => Nat -> FiniteType -> Gen g
randomVec w t g =
  let (g1,g2) = split g
      mkElem = randomFiniteValue t
  in (FVVec t $ genericTake (unNat w) $ unfoldr (Just . mkElem) g1 , g2)

-- | Generate a random tuple value.
randomTuple :: RandomGen g => [FiniteType] -> Gen g
randomTuple ts = go [] gens
  where
  gens = map randomFiniteValue ts
  go els [] g = (FVTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem g
    in go (v : els) more g1

-- | Generate a random record value.
randomRec :: RandomGen g => (Map FieldName FiniteType) -> Gen g
randomRec fieldTys = go [] gens
  where
  gens = Map.toList . Map.map randomFiniteValue $ fieldTys
  go els [] g = (FVRec (Map.fromList . reverse $ els), g)
  go els ((l,mkElem) : more) g =
    let (v, g1) = mkElem g
    in go ((l,v) : els) more g1

_test :: IO ()
_test = do
  g <- System.Random.newStdGen
  let (s,_) = randomFiniteValue (FTVec (Nat 16) (FTVec (Nat 1) FTBit)) g
  print s
