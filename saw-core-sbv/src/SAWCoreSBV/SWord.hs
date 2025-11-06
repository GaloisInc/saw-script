{- |
Module      : SAWCoreSBV.SWord
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module SAWCoreSBV.SWord
  ( SBool, SWord, SInteger
  , literalSWord, literalSInteger
  , fromBitsLE
  , forallSWord, existsSWord, forallSWord_, existsSWord_
  , forallSBool, existsSBool, forallSBool_, existsSBool_
  , forallSInteger, existsSInteger, forallSInteger_, existsSInteger_
  ) where

import Control.Monad.Reader
import Data.List (foldl')

import Data.SBV ( symbolicEnv )
import Data.SBV.Internals( VarContext(NonQueryVar) )

import Data.SBV.Dynamic

type SBool = SVal
type SWord = SVal
type SInteger = SVal

fromBitsLE :: [SBool] -> SWord
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord
literalSWord w i = svInteger (KBounded False w) i

literalSInteger :: Integer -> SWord
literalSInteger i = svInteger KUnbounded i

forallSWord :: String -> Int -> Symbolic SWord
forallSWord nm w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) (KBounded False w) (Just nm)

forallSWord_ :: Int -> Symbolic SWord
forallSWord_ w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) (KBounded False w) Nothing

existsSWord :: String -> Int -> Symbolic SWord
existsSWord nm w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) (KBounded False w) (Just nm)

existsSWord_ :: Int -> Symbolic SWord
existsSWord_ w = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) (KBounded False w) Nothing

forallSBool :: String -> Symbolic SBool
forallSBool nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) KBool (Just nm)

existsSBool :: String -> Symbolic SBool
existsSBool nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) KBool (Just nm)

forallSBool_ :: Symbolic SBool
forallSBool_ = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) KBool Nothing

existsSBool_ :: Symbolic SBool
existsSBool_ = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) KBool Nothing

forallSInteger :: String -> Symbolic SInteger
forallSInteger nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) KUnbounded (Just nm)

existsSInteger :: String -> Symbolic SInteger
existsSInteger nm = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) KUnbounded (Just nm)

forallSInteger_ :: Symbolic SInteger
forallSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just ALL)) KUnbounded Nothing

existsSInteger_ :: Symbolic SInteger
existsSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) KUnbounded Nothing
