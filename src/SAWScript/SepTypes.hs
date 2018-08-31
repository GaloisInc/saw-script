{- |
Module      : SAWScript.SepTypes
Description : Extraction of SAW terms from Crucible using Separable Types
License     : BSD3
Maintainer  : westbrook
Stability   : provisional
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module SAWScript.SepTypes
       (crucible_llvm_septypes_extract
       ) where

import qualified SAWScript.CrucibleLLVM as Crucible
import SAWScript.CrucibleBuiltins
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Options

crucible_llvm_septypes_extract :: BuiltinContext -> Options -> LLVMModule -> String -> TopLevel String
crucible_llvm_septypes_extract bic opts lm fn_name =
  do _cfg <- crucible_llvm_cfg bic opts lm fn_name
     return "Foo"
