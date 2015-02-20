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

-- ??? What is the 'Int' for? Otherwise this looks like 'State g
-- FiniteValue'. The 'Int' is never actually used, but the comment on
-- the original 'randomWord' function said:
--
--   The size parameter is assumed to vary between 1 and 100, and we
--   use it to generate smaller numbers first.
--
-- but the implementation did not actually do this.
type Gen g = Int -> g -> (FiniteValue, g)

{- | Apply a testable value to some randomly-generated arguments.
     Returns `Nothing` if the function returned `True`, or
     `Just counterexample` if it returned `False`.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
scRunTest :: RandomGen g => SharedContext s ->
  SharedTerm s -> [Gen g] -> Int -> g -> IO (Maybe [SharedTerm s], g)
scRunTest sc fun gens sz g = do
  let (xs, g') = runGens gens sz g
  result <- apply xs
  case result of
    VExtra (CBool True) -> return $ (Nothing, g')
    VExtra (CBool False) -> do
      counterExample <- mapM (scFiniteValue sc) xs
      return $ (Just counterExample, g')
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

-- | Run a sequence of generators from left to right.
runGens :: RandomGen g => [Gen g] -> Int -> g -> ([FiniteValue], g)
runGens []         _sz g = ([], g)
runGens (gen:gens)  sz g = (v:vs, g'')
  where
  (v, g') = gen sz g
  (vs, g'') = runGens gens sz g'

randomFiniteValue :: RandomGen g => FiniteType -> Gen g
randomFiniteValue FTBit = randomBit
randomFiniteValue (FTVec n FTBit) = randomWord n
randomFiniteValue (FTVec n t) = randomVec n t
randomFiniteValue (FTTuple ts) = randomTuple ts
randomFiniteValue (FTRec fields) = randomRec fields

-- | Generate a random bit value.
randomBit :: RandomGen g => Gen g
randomBit _ g =
  let (b,g1) = random g
  in (FVBit b, g1)

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
randomWord :: RandomGen g => Nat -> Gen g
randomWord w _sz g =
   let (val, g1) = randomR (0,2^(unNat w - 1)) g
   in (FVWord w val, g1)


{- | Generate a random vector.  Generally, this should be used for sequences
other than bits.  For sequences of bits use "randomWord".  The difference
is mostly about how the results will be displayed. -}
randomVec :: RandomGen g => Nat -> FiniteType -> Gen g
randomVec w t sz g =
  let (g1,g2) = split g
      mkElem = randomFiniteValue t
  in (FVVec t $ genericTake (unNat w) $ unfoldr (Just . mkElem sz) g1 , g2)

-- | Generate a random tuple value.
randomTuple :: RandomGen g => [FiniteType] -> Gen g
randomTuple ts sz = go [] gens
  where
  gens = map randomFiniteValue ts
  go els [] g = (FVTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem sz g
    in go (v : els) more g1

-- | Generate a random record value.
randomRec :: RandomGen g => (Map FieldName FiniteType) -> Gen g
randomRec fieldTys sz = go [] gens
  where
  gens = Map.toList . Map.map randomFiniteValue $ fieldTys
  go els [] g = (FVRec (Map.fromList . reverse $ els), g)
  go els ((l,mkElem) : more) g =
    let (v, g1) = mkElem sz g
    in go ((l,v) : els) more g1

_test :: IO ()
_test = do
  g <- System.Random.newStdGen
  let (s,_) = randomFiniteValue (FTVec (Nat 16) (FTVec (Nat 1) FTBit)) 100 g
  print s
