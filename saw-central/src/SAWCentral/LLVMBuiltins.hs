{- |
Module      : SAWCentral.LLVMBuiltins
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

module SAWCentral.LLVMBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Data.String
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some
import Control.Monad (unless)
import Control.Monad.State (gets)

import qualified Text.LLVM.AST as LLVM
import qualified Data.LLVM.BitCode as LLVM
import qualified Text.LLVM.Parser as LLVM (parseType)

import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as CL
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMS (LLVMModule, loadLLVMModule)
import SAWCentral.Options
import SAWCentral.Value as SV

llvm_load_module :: FilePath -> TopLevel (Some CMS.LLVMModule)
llvm_load_module file =
  do laxArith <- gets rwLaxArith
     debugIntrinsics <- gets rwDebugIntrinsics
     let ?transOpts = CL.defaultTranslationOptions
                        { CL.laxArith = laxArith
                        , CL.debugIntrinsics = debugIntrinsics
                        }
     halloc <- getHandleAlloc
     io (CMS.loadLLVMModule file halloc) >>= \case
       Left err -> fail (LLVM.formatError err)
       Right (llvm_mod, warnings) -> do
         unless (null warnings) $
           printOutLnTop Warn $ show $ LLVM.ppParseWarnings warnings
         return llvm_mod

llvm_type :: Text -> TopLevel LLVM.Type
llvm_type str =
  case LLVM.parseType (Text.unpack str) of
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

llvm_alias :: Text -> LLVM.Type
llvm_alias n = LLVM.Alias (fromString $ Text.unpack n)

llvm_packed_struct_type :: [LLVM.Type] -> LLVM.Type
llvm_packed_struct_type = LLVM.PackedStruct

llvm_pointer :: LLVM.Type -> LLVM.Type
llvm_pointer = LLVM.PtrTo

llvm_struct_type :: [LLVM.Type] -> LLVM.Type
llvm_struct_type = LLVM.Struct
