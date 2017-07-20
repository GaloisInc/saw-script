{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{- |
Module      : Verifier.SAW.Simulator.SBV.SWord
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.Simulator.SBV.SWord
  ( SBool, SWord
  , literalSWord
  , fromBitsLE
  , forallSWord, existsSWord, forallSWord_, existsSWord_
  , forallSBool, existsSBool, forallSBool_, existsSBool_
  ) where

import Control.Monad.Reader
import Data.List (foldl')

import Data.SBV.Dynamic

type SBool = SVal
type SWord = SVal

fromBitsLE :: [SBool] -> SWord
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord
literalSWord w i = svInteger (KBounded False w) i

forallSWord :: String -> Int -> Symbolic SWord
forallSWord nm w = ask >>= liftIO . svMkSymVar (Just ALL) (KBounded False w) (Just nm)

forallSWord_ :: Int -> Symbolic SWord
forallSWord_ w = ask >>= liftIO . svMkSymVar (Just ALL) (KBounded False w) Nothing

existsSWord :: String -> Int -> Symbolic SWord
existsSWord nm w = ask >>= liftIO . svMkSymVar (Just EX) (KBounded False w) (Just nm)

existsSWord_ :: Int -> Symbolic SWord
existsSWord_ w = ask >>= liftIO . svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool :: String -> Symbolic SBool
forallSBool nm = ask >>= liftIO . svMkSymVar (Just ALL) KBool (Just nm)

existsSBool :: String -> Symbolic SBool
existsSBool nm = ask >>= liftIO . svMkSymVar (Just EX) KBool (Just nm)

forallSBool_ :: Symbolic SBool
forallSBool_ = ask >>= liftIO . svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic SBool
existsSBool_ = ask >>= liftIO . svMkSymVar (Just EX) KBool Nothing
