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

data Value m b w e
  = VFun !(Thunk m b w e -> m (Value m b w e))
  | VTuple !(Vector (Thunk m b w e))
  | VRecord !(Map FieldName (Thunk m b w e))
  | VCtorApp !Ident !(Vector (Thunk m b w e))
  | VVector !(Vector (Thunk m b w e))
  | VBool b
  | VWord w
  | VNat !Integer
  | VString !String
  | VFloat !Float
  | VDouble !Double
  | VPiType !(Value m b w e) !(Thunk m b w e -> m (Value m b w e))
  | VTupleType [Value m b w e]
  | VRecordType !(Map FieldName (Value m b w e))
  | VDataType !Ident [Value m b w e]
  | VType -- ^ Other unknown type
  | VExtra e

type Thunk m b w e = Lazy m (Value m b w e)

strictFun :: Monad m => (Value m b w e -> m (Value m b w e)) -> Value m b w e
strictFun f = VFun (\x -> force x >>= f)

pureFun :: Monad m => (Value m b w e -> Value m b w e) -> Value m b w e
pureFun f = VFun (\x -> liftM f (force x))

constFun :: Monad m => Value m b w e -> Value m b w e
constFun x = VFun (\_ -> return x)

instance Show e => Show (Value m b w e) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VTuple xv      -> showParen True
                          (foldr (.) id (intersperse (showString ",") (map shows (toList xv))))
      VRecord xm      -> showString "{" .
                        foldr (.) id (intersperse (showString ", ")
                                      (map showField (Map.assocs (fmap (const Nil) xm)))) .
                        showString "}"
      VCtorApp s xv
        | V.null xv  -> shows s
        | otherwise  -> shows s . showList (toList xv)
      VVector xv     -> showList (toList xv)
      VBool _        -> showString "<<boolean>>"
      VWord _        -> showString "<<bitvector>>"
      VNat n         -> shows n
      VFloat float   -> shows float
      VDouble double -> shows double
      VString s      -> shows s
      VPiType t _    -> showParen True
                        (shows t . showString " -> ...")
      VTupleType vs  -> showString "#" .
                        showParen True
                        (foldr (.) id (intersperse (showString ",") (map shows vs)))
      VRecordType _  -> error "unimplemented: show VRecordType"
      VDataType s vs
        | null vs    -> shows s
        | otherwise  -> shows s . showList vs
      VType          -> showString "_"
      VExtra x       -> showsPrec p x
    where
      showField (name, t) = showString name . showString " = " . shows t
      toList = map (const Nil) . V.toList

data Nil = Nil

instance Show Nil where
  show Nil = "_"

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: (Monad m, Show e) => Int -> Value m b w e -> m (Value m b w e)
valTupleSelect i (VTuple xv) = force $ (V.!) xv (i - 1)
valTupleSelect _ v = fail $ "valTupleSelect: Not a tuple value: " ++ show v

valRecordSelect :: (Monad m, Show e) => FieldName -> Value m b w e -> m (Value m b w e)
valRecordSelect k (VRecord vm) | Just x <- Map.lookup k vm = force x
valRecordSelect _ v = fail $ "valRecordSelect: Not a record value: " ++ show v

apply :: Monad m => Value m b w e -> Thunk m b w e -> m (Value m b w e)
apply (VFun f) x = f x
apply _ _ = fail "Not a function value"

applyAll :: Monad m => Value m b w e -> [Thunk m b w e] -> m (Value m b w e)
applyAll = foldM apply
