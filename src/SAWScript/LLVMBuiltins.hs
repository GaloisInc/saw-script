{- |
Module      : SAWScript.LLVMBuiltins
Description : Implementations of LLVM-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

module SAWScript.LLVMBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Lens
import Control.Monad.State hiding (mapM)
import Control.Monad.ST (stToIO)
import Control.Monad.Trans.Except
import Data.Function (on)
import Data.List (find, partition, sortBy, groupBy)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String
import qualified Data.Vector as V
import Text.Parsec as P

import Text.LLVM (modDataLayout)
import qualified Text.LLVM.AST as LLVM
import qualified Data.LLVM.BitCode as LLVM
import qualified Text.LLVM.PP as LLVM
import qualified Text.LLVM.DebugUtils as DU
import qualified Text.LLVM.Parser as LLVM (parseType)

import Verifier.SAW.Cryptol (exportFirstOrderValue)
import Verifier.SAW.FiniteValue (FirstOrderValue)
import Verifier.SAW.Recognizer (asExtCns)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.CryptolEnv (schemaNoUser)

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Builtins
import SAWScript.Options as Opt
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Utils
import SAWScript.Value as SV

import qualified SAWScript.CrucibleLLVM as Crucible (translateModule)
import qualified Cryptol.Eval.Monad as Cryptol (runEval)
import qualified Cryptol.Eval.Value as Cryptol (ppValue)
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pretty)

llvm_load_module :: FilePath -> TopLevel LLVMModule
llvm_load_module file =
  io (LLVM.parseBitCodeFromFile file) >>= \case
    Left err -> fail (LLVM.formatError err)
    Right llvm_mod -> do
      halloc <- getHandleAlloc
      mtrans <- io $ stToIO $ Crucible.translateModule halloc llvm_mod
      return (LLVMModule file llvm_mod mtrans)

llvm_type :: String -> TopLevel LLVM.Type
llvm_type str =
  case LLVM.parseType str of
    Left e -> fail (show e)
    Right t -> return t

llvm_int :: Int -> LLVM.Type
llvm_int n = LLVM.PrimType (LLVM.Integer (fromIntegral n))

llvm_float :: LLVM.Type
llvm_float = LLVM.PrimType (LLVM.FloatType LLVM.Float)

llvm_double :: LLVM.Type
llvm_double = LLVM.PrimType (LLVM.FloatType LLVM.Double)

llvm_array :: Int -> LLVM.Type -> LLVM.Type
llvm_array n t = LLVM.Array (fromIntegral n) t

llvm_struct :: String -> LLVM.Type
llvm_struct n = LLVM.Alias (fromString n)
