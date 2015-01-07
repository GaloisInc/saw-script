{-# LANGUAGE PatternGuards #-}

{- |
Module      : Verifier.SAW.Simulator.Value
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Value
       ( module Verifier.SAW.Simulator.Value
       , module Verifier.SAW.Simulator.MonadLazy
       ) where

import Prelude hiding (mapM)

import Control.Monad (foldM, liftM)
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import Verifier.SAW.Simulator.MonadLazy

------------------------------------------------------------
-- Values and Thunks

data Value m e
  = VFun !(Thunk m e -> m (Value m e))
  | VTuple !(Vector (Thunk m e))
  | VRecord !(Map FieldName (Thunk m e))
  | VCtorApp !Ident !(Vector (Thunk m e))
  | VVector !(Vector (Thunk m e))
  | VNat !Integer
  | VString !String
  | VFloat !Float
  | VDouble !Double
  | VType
  | VExtra e

type Thunk m e = Lazy m (Value m e)

strictFun :: Monad m => (Value m e -> m (Value m e)) -> Value m e
strictFun f = VFun (\x -> force x >>= f)

pureFun :: Monad m => (Value m e -> Value m e) -> Value m e
pureFun f = VFun (\x -> liftM f (force x))

constFun :: Monad m => Value m e -> Value m e
constFun x = VFun (\_ -> return x)

instance Show e => Show (Value m e) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VTuple xv      -> showParen True
                          (foldr (.) id (intersperse (showString ",") (map shows (toList xv))))
      VRecord _      -> error "unimplemented: show VRecord" -- !(Map FieldName Value)
      VCtorApp s xv
        | V.null xv  -> shows s
        | otherwise  -> shows s . showList (toList xv)
      VVector xv     -> showList (toList xv)
      VNat n         -> shows n
      VFloat float   -> shows float
      VDouble double -> shows double
      VString s      -> shows s
      VType          -> showString "_"
      VExtra x       -> showsPrec p x
    where
      toList = map (const Nil) . V.toList

data Nil = Nil

instance Show Nil where
  show Nil = "_"

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: (Monad m, Show e) => Int -> Value m e -> m (Value m e)
valTupleSelect i (VTuple xv) = force $ (V.!) xv (i - 1)
valTupleSelect _ v = fail $ "valTupleSelect: Not a tuple value: " ++ show v

valRecordSelect :: (Monad m, Show e) => FieldName -> Value m e -> m (Value m e)
valRecordSelect k (VRecord vm) | Just x <- Map.lookup k vm = force x
valRecordSelect _ v = fail $ "valRecordSelect: Not a record value: " ++ show v

apply :: Monad m => Value m e -> Thunk m e -> m (Value m e)
apply (VFun f) x = f x
apply _ _ = fail "Not a function value"

applyAll :: Monad m => Value m e -> [Thunk m e] -> m (Value m e)
applyAll = foldM apply
