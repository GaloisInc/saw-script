{-# LANGUAGE PatternGuards #-}

{- |
Module      : Verifier.SAW.Simulator.Value
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Simulator.Value where

import Prelude hiding (mapM)

import Control.Monad (foldM, liftM)
import Control.Monad.IO.Class
import Data.IORef
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Vector (Vector)
import qualified Data.Vector as V

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

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

data Thunk m e
  = Thunk !(IORef (Either (m (Value m e)) (Value m e)))
  | Ready !(Value m e)

force :: MonadIO m => Thunk m e -> m (Value m e)
force (Ready v) = return v
force (Thunk ref) = do
  r <- liftIO $ readIORef ref
  case r of
    Left m -> do
      v <- m
      liftIO $ writeIORef ref (Right v)
      return v
    Right v -> return v

delay :: MonadIO m => m (Value m e) -> m (Thunk m e)
delay m = liftM Thunk $ liftIO (newIORef (Left m))

strictFun :: MonadIO m => (Value m e -> m (Value m e)) -> Value m e
strictFun f = VFun (\x -> force x >>= f)

instance Show e => Show (Value m e) where
  showsPrec p v =
    case v of
      VFun {}        -> showString "<<fun>>"
      VTuple xv      -> showParen True
                          (foldr (.) id (intersperse (showString ",") (map shows (V.toList xv))))
      VRecord _      -> error "unimplemented: show VRecord" -- !(Map FieldName Value)
      VCtorApp s xv
        | V.null xv  -> shows s
        | otherwise  -> shows s . showList (V.toList xv)
      VVector xv     -> showList (V.toList xv)
      VNat n         -> shows n
      VFloat float   -> shows float
      VDouble double -> shows double
      VString s      -> shows s
      VType          -> showString "_"
      VExtra x       -> showsPrec p x

instance Show e => Show (Thunk m e) where
  showsPrec _ (Thunk _) = showString "<<thunk>>"
  showsPrec p (Ready v) = showsPrec p v

------------------------------------------------------------
-- Basic operations on values

valTupleSelect :: MonadIO m => Int -> Value m e -> m (Value m e)
valTupleSelect i (VTuple xv) = force $ (V.!) xv (i - 1)
valTupleSelect _ _ = fail "valTupleSelect: Not a tuple value"

valRecordSelect :: MonadIO m => FieldName -> Value m e -> m (Value m e)
valRecordSelect k (VRecord vm) | Just x <- Map.lookup k vm = force x
valRecordSelect _ _ = fail "valRecordSelect: Not a record value"

apply :: Monad m => Value m e -> Thunk m e -> m (Value m e)
apply (VFun f) x = f x
apply _ _ = fail "Not a function value"

applyAll :: Monad m => Value m e -> [Thunk m e] -> m (Value m e)
applyAll = foldM apply
