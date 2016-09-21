{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Cryptol
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol.Prims
( concretePrims
, bitblastPrims
, sbvPrims
) where

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import Data.AIG.Interface (IsAIG)
import qualified Data.AIG.Operations as AIG

import qualified Cryptol.TypeCheck.Solver.InfNat as CryNat

import Data.SBV.Dynamic as SBV

import Verifier.SAW.TypedAST
import qualified Verifier.SAW.Prim as P
import Verifier.SAW.Simulator.Value
import Verifier.SAW.Simulator.Prims
import qualified Verifier.SAW.Simulator.BitBlast as BB
import qualified Verifier.SAW.Simulator.SBV as SBV
import qualified Verifier.SAW.Simulator.Concrete as C

-- primitive ecError :: (a :: sort 0) -> (len :: Num) -> PFin len -> seq len (bitvector 8) -> a;
ecError :: Monad m => (w -> m Char) -> Value m b w i e
ecError asChar =
  strictFun $ \_a -> return $
    strictFun $ \_len -> return $
      strictFun $ \_pfin -> return $
        strictFun $ \(VVector msgChars) -> do
          let toChar (VWord w) = asChar w
              toChar _ = fail "Cryptol.ecError: unable to print message"
          msg <- mapM (toChar <=< force) $ V.toList $ msgChars
          fail $ "Cryptol.ecError: " ++ msg

bvAsChar :: Monad m => P.BitVector -> m Char
bvAsChar w = return $ toEnum $ fromInteger $ P.unsigned $ w

aigWordAsChar :: (Monad m, IsAIG l g) => g s -> AIG.BV (l s) -> m Char
aigWordAsChar g bv =
  case AIG.asUnsigned g bv of
    Just i -> return $ toEnum $ fromInteger i
    Nothing -> fail "unable to interpret bitvector as character"

sbvWordAsChar :: Monad m => SBV.SWord -> m Char
sbvWordAsChar bv =
  case SBV.svAsInteger bv of
    Just i -> return $ toEnum $ fromInteger i
    Nothing -> fail "unable to interpret bitvector as character"

--primitive tcLenFromThen_Nat :: Nat -> Nat -> Nat -> Nat;
tcLenFromThen_Nat :: Monad m => Value m b w i e
tcLenFromThen_Nat =
  natFun' "tcLenFromThen_Nat x" $ \x -> return $
  natFun' "tcLenFromThen_Nat y" $ \y -> return $
  natFun' "tcLenFromThen_Nat w" $ \w ->
    case CryNat.nLenFromThen (CryNat.Nat $ fromIntegral x)
                             (CryNat.Nat $ fromIntegral y)
                             (CryNat.Nat $ fromIntegral w) of
      Just (CryNat.Nat ans) -> return $ vNat $ fromIntegral ans
      _ -> fail "tcLenFromThen_Nat: unable to calculate length"

--primitive tcLenFromThenTo_Nat :: Nat -> Nat -> Nat -> Nat;
tcLenFromThenTo_Nat :: Monad m => Value m b w i e
tcLenFromThenTo_Nat =
  natFun' "tcLenFromThenTo_Nat x" $ \x -> return $
  natFun' "tcLenFromThenTo_Nat y" $ \y -> return $
  natFun' "tcLenFromThenTo_Nat z" $ \z ->
    case CryNat.nLenFromThenTo (CryNat.Nat $ fromIntegral x)
                               (CryNat.Nat $ fromIntegral y)
                               (CryNat.Nat $ fromIntegral z) of
      Just (CryNat.Nat ans) -> return $ vNat $ fromIntegral ans
      _ -> fail "tcLenFromThenTo_Nat: unable to calculate length"

concretePrims :: Map Ident C.CValue
concretePrims = Map.fromList
  [ ("Cryptol.ecRandom"            , error "Cryptol.ecRandom is depreciated; don't use it")
  , ("Cryptol.ecError"             , ecError bvAsChar )
  , ("Cryptol.tcLenFromThen_Nat"   , tcLenFromThen_Nat )
  , ("Cryptol.tcLenFromThenTo_Nat" , tcLenFromThenTo_Nat )
  ]

bitblastPrims :: IsAIG l g => g s -> Map Ident (BB.BValue (l s))
bitblastPrims g = Map.fromList
  [ ("Cryptol.ecRandom"            , error "Cryptol.ecRandom is depreciated; don't use it")
  , ("Cryptol.ecError"             , ecError (aigWordAsChar g) )
  , ("Cryptol.tcLenFromThen_Nat"   , tcLenFromThen_Nat )
  , ("Cryptol.tcLenFromThenTo_Nat" , tcLenFromThenTo_Nat )
  ]

sbvPrims :: Map Ident SBV.SValue
sbvPrims = Map.fromList
  [ ("Cryptol.ecRandom"            , error "Cryptol.ecRandom is depreciated; don't use it")
  , ("Cryptol.ecError"             , ecError sbvWordAsChar )
  , ("Cryptol.tcLenFromThen_Nat"   , tcLenFromThen_Nat )
  , ("Cryptol.tcLenFromThenTo_Nat" , tcLenFromThenTo_Nat )
  ]
