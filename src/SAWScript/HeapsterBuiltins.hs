{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.HeapsterBuiltins
       ( heapster_extract
       ) where

import qualified Data.Map as Map
import Control.Monad.IO.Class

import Verifier.SAW.SharedTerm

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension

import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.TopLevel
import SAWScript.Value
import SAWScript.Utils as SS
import SAWScript.Options
import SAWScript.CrucibleBuiltins
import SAWScript.Builtins

import SAWScript.Heapster.Permissions
import SAWScript.Heapster.TypedCrucible
import SAWScript.Heapster.JudgmentTranslation

data SomeFunPerms where
  SomeFunPerms ::
    CtxRepr ghosts -> CtxRepr init -> TypeRepr ret ->
    PermSet (ghosts <+> init) -> PermSet (ghosts <+> init ::> ret) ->
    SomeFunPerms

heapsterPermsList :: [SomeFunPerms]
heapsterPermsList =
  []

translateTypedCFG :: SharedContext ->
                     TypedCFG ext blocks ghosts init ret ->
                     IO Term
translateTypedCFG = error "FIXME HERE"

withCFG :: SAW_CFG ->
           (forall ext blocks init ret.
            (TraverseExt ext, PrettyExt ext) =>
            CFG ext blocks init ret -> a) -> a
withCFG (LLVM_CFG (AnyCFG cfg)) f = f cfg
withCFG (JVM_CFG (AnyCFG cfg)) f = f cfg

heapster_extract :: BuiltinContext -> Options ->
                    LLVMModule -> String -> Int ->
                    TopLevel String
heapster_extract bic opts lm fn_name perms_num =
  do cfg <- crucible_llvm_cfg bic opts lm fn_name
     pp_opts <- getTopLevelPPOpts
     somePerms <-
       if perms_num >= length heapsterPermsList then
         fail "heapster_extract: perms index out of bounds"
       else return (heapsterPermsList !! perms_num)
     withCFG cfg $ \cfg ->
       case somePerms of
         SomeFunPerms ghosts init ret permsIn permsOut
           | Just Refl <- testEquality init (cfgArgTypes cfg)
           , Just Refl <- testEquality ret (cfgReturnType cfg) ->
             do let typed_cfg = tcCFG ghosts permsIn permsOut cfg
                sc <- getSharedContext
                fun_term <- liftIO $ translateTypedCFG sc typed_cfg
                return $ scPrettyTerm pp_opts fun_term
