{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Verifier.SAW.Cryptol
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol.Prims where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor (<$>)
#endif

import GHC.Integer.Logarithms( integerLog2# )
import GHC.Exts( Int( I# ) )

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import Data.AIG.Interface (IsAIG)
import qualified Data.AIG.Operations as AIG

import Data.SBV.Dynamic as SBV

import Verifier.SAW.TypedAST
import qualified Verifier.SAW.Prim as P
import Verifier.SAW.Simulator.Value
import Verifier.SAW.Simulator.Prims
import qualified Verifier.SAW.Simulator.BitBlast as BB
import qualified Verifier.SAW.Simulator.SBV as SBV
import qualified Verifier.SAW.Simulator.Concrete as C

integerLg2 :: Integer -> Int
integerLg2 i
  | i > 0 = I# (integerLog2# i)
  | otherwise = error "integerLg2: illegal nonpositive argument"

-- primitive ecError :: (a :: sort 0) -> (len :: Num) -> PFin len -> seq len (bitvector 8) -> a;
ecError :: Monad m => (w -> m Char) -> Value m b w e
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


-- primitive lg2Nat :: Nat -> Nat;
lg2Nat :: Monad m => (Value m b w e -> m w) -> (w -> m w) -> Value m b w e
lg2Nat asWord wordLg2 =
  strictFun $ \n ->
    case n of
      VNat i   -> return $ VNat $ fromIntegral $ integerLg2 i
      VToNat v -> (VToNat . VWord) <$> (wordLg2 =<< asWord v)
      _ -> fail "Cryptol.lg2Nat: illegal argument"

-- primitive bvLg2 :: (n :: Nat) -> bitvector n -> bitvector n;
bvLg2 :: Monad m => (Value m b w e -> m w) -> (w -> m w) -> Value m b w e
bvLg2 asWord wordLg2 =
  natFun' "bvLg2 1" $ \_n -> return $
  strictFun $ \w -> VWord <$> (wordLg2 =<< asWord w)

concreteLg2 :: Monad m => P.BitVector -> m P.BitVector
concreteLg2 bv = return bv{ P.unsigned = fromIntegral $ integerLg2 $ P.unsigned bv } 

bitblastLg2 :: (Monad m, IsAIG l g) => g s -> BB.LitVector (l s) -> m (BB.LitVector (l s))
bitblastLg2 _g _w = undefined

sbvLg2 :: Monad m => SBV.SWord -> m SBV.SWord
sbvLg2 _w = undefined

sbvToWord :: SBV.SValue -> IO SBV.SWord
sbvToWord v = do
  x <- SBV.toWord v
  case x of
     Just x' -> return x'
     Nothing -> fail "sbvToWord: expected word value"

concretePrims :: Map Ident C.CValue
concretePrims = Map.fromList
  [ ("Cryptol.arithBinaryBool", error "Cryptol.arithBinaryBool is deliberately unimplemented" )
  , ("Cryptol.arithUnaryBool" , error "Cryptol.arithUnaryBool is deliberately unimplemented" )
  , ("Cryptol.ecError"        , ecError bvAsChar )
  , ("Cryptol.lg2Nat"         , lg2Nat (return . C.toWord) concreteLg2 )
  , ("Cryptol.bvLg2"          , bvLg2 (return . C.toWord) concreteLg2 )
-- , ("Cryptol.tcLenFromThen"          , )
-- , ("Cryptol.tcLenFromThenTo"          , )
  ]

bitblastPrims :: IsAIG l g => g s -> Map Ident (BB.BValue (l s))
bitblastPrims g = Map.fromList
  [ ("Cryptol.arithBinaryBool", error "Cryptol.arithBinaryBool is deliberately unimplemented" )
  , ("Cryptol.arithUnaryBool" , error "Cryptol.arithUnaryBool is deliberately unimplemented" )
  , ("Cryptol.ecError"        , ecError (aigWordAsChar g) )
  , ("Cryptol.lg2Nat"         , lg2Nat BB.toWord (bitblastLg2 g) )
  , ("Cryptol.bvLg2"          , bvLg2 BB.toWord (bitblastLg2 g) )
  ]

sbvPrims :: Map Ident SBV.SValue
sbvPrims = Map.fromList
  [ ("Cryptol.arithBinaryBool", error "Cryptol.arithBinaryBool is deliberately unimplemented" )
  , ("Cryptol.arithUnaryBool" , error "Cryptol.arithUnaryBool is deliberately unimplemented" )
  , ("Cryptol.ecError"        , ecError sbvWordAsChar )
  , ("Cryptol.lg2Nat"         , lg2Nat sbvToWord sbvLg2 )
  , ("Cryptol.bvLg2"          , bvLg2 sbvToWord sbvLg2 )
  ]
