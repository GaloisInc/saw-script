-- | Utilities for resolving 'SetupValue's that are used across language
-- backends.
module SAWCentral.Crucible.Common.ResolveSetupValue
  ( resolveBoolTerm
  ) where

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4

import SAWCore.SharedTerm

import qualified SAWCore.Simulator.Concrete as Concrete

import SAWCoreWhat4.ReturnTrip

import SAWCentral.Crucible.Common

-- | Resolve a SAWCore 'Term' into a What4 'W4.Pred'.
resolveBoolTerm :: Sym -> Term -> IO (W4.Pred Sym)
resolveBoolTerm sym tm =
  do st <- sawCoreState sym
     let sc = saw_ctx st
     mx <- case getAllExts tm of
             -- concretely evaluate if it is a closed term
             [] ->
               do modmap <- scGetModuleMap sc
                  let v = Concrete.evalSharedTerm modmap mempty mempty tm
                  pure (Just (Concrete.toBool v))
             _ -> return Nothing
     case mx of
       Just x  -> return (W4.backendPred sym x)
       Nothing -> bindSAWTerm sym st W4.BaseBoolRepr tm
