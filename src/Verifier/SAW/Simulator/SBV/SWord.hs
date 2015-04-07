{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Verifier.SAW.Simulator.SBV.SWord
  ( SBool, SWord
  , literalSWord
  , blastLE, fromBitsLE
  , forallSWord, existsSWord, forallSWord_, existsSWord_
  , forallSBool, existsSBool, forallSBool_, existsSBool_
  ) where

import Data.List (foldl')

import Data.SBV.Dynamic

type SBool = SVal
type SWord = SVal

blastLE :: SWord -> [SBool]
blastLE x = [ svTestBit x i | i <- reverse [0 .. svBitSize x - 1] ]

fromBitsLE :: [SBool] -> SWord
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord
literalSWord w i = svInteger (KBounded False w) i

forallSWord :: String -> Int -> Symbolic SWord
forallSWord nm w = svMkSymVar (Just ALL) (KBounded False w) (Just nm)

forallSWord_ :: Int -> Symbolic SWord
forallSWord_ w = svMkSymVar (Just ALL) (KBounded False w) Nothing

existsSWord :: String -> Int -> Symbolic SWord
existsSWord nm w = svMkSymVar (Just EX) (KBounded False w) (Just nm)

existsSWord_ :: Int -> Symbolic SWord
existsSWord_ w = svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool :: String -> Symbolic SBool
forallSBool nm = svMkSymVar (Just ALL) KBool (Just nm)

existsSBool :: String -> Symbolic SBool
existsSBool nm = svMkSymVar (Just EX) KBool (Just nm)

forallSBool_ :: Symbolic SBool
forallSBool_ = svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic SBool
existsSBool_ = svMkSymVar (Just EX) KBool Nothing
