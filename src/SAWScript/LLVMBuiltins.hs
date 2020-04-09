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
import Data.String
import Data.Parameterized.Some

import qualified Text.LLVM.AST as LLVM
import qualified Data.LLVM.BitCode as LLVM
import qualified Text.LLVM.Parser as LLVM (parseType)

import SAWScript.Value as SV

import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible (translateModule)
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMS (LLVMModule(..))

llvm_load_module :: FilePath -> TopLevel (Some CMS.LLVMModule)
llvm_load_module file =
  io (LLVM.parseBitCodeFromFile file) >>= \case
    Left err -> fail (LLVM.formatError err)
    Right llvm_mod -> do
      halloc <- getHandleAlloc
      Some mtrans <- io $ Crucible.translateModule halloc llvm_mod
      return (Some (CMS.LLVMModule file llvm_mod mtrans))

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
