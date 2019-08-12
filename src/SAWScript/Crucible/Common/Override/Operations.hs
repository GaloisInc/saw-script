{- |
Module      : SAWScript.Crucible.Common.Override.Operations
Description : Operations in the OverrideMatcher monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

module SAWScript.Crucible.Common.Override.Operations
  ( stateCond
  , resolveSAWPred
  , assignTerm
  , matchTerm
  , instantiateSetupValue
  ) where

import Control.Lens

import           Control.Monad.IO.Class (liftIO)
import           Data.Map (Map)
import qualified Data.Set as Set

import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4

import qualified Verifier.SAW.SharedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm (Term, SharedContext)
import           Verifier.SAW.TypedTerm (TypedTerm(..))
import qualified Verifier.SAW.Term.Functor as SAWVerifier
import           Verifier.SAW.Term.Functor (TermF(..), ExtCns(..), VarIndex)
import           Verifier.SAW.Term.Functor (FlatTermF(ExtCns))
import           Verifier.SAW.Prelude (scEq)

import           SAWScript.Crucible.Common (Sym)
import           SAWScript.Crucible.Common.MethodSpec (PrePost(..), SetupValue(..))
import           SAWScript.Crucible.Common.Override.Monad

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

resolveSAWPred :: Sym -> Term -> IO (W4.Pred Sym)
resolveSAWPred sym tm = CrucibleSAW.bindSAWTerm sym W4.BaseBoolRepr tm

assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  Sym                                                              ->
  W4.ProgramLoc                                                    ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher env md ()

assignTerm sc cc loc prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old -> matchTerm sc cc loc prepost val old


matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  Sym                                                           ->
  W4.ProgramLoc                                                    ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher ext md ()
matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc sym loc prepost real expect =
  do free <- OM (use omFree)
     case SAWVerifier.unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc sym loc prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            p <- liftIO $ resolveSAWPred sym t
            addAssert p $ Crucible.SimError loc $ Crucible.AssertFailureSimError $ unlines $
              [ "Literal equality " ++ stateCond prepost
              , "Expected term: " ++ prettyTerm expect
              , "Actual term:   " ++ prettyTerm real
              ]
  where prettyTerm term =
          let pretty_ = show (SAWVerifier.ppTerm SAWVerifier.defaultPPOpts term)
          in if length pretty_ < 200 then pretty_ else "<term omitted due to size>"

------------------------------------------------------------------------

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue ext        ->
  IO (SetupValue ext)
instantiateSetupValue sc s v =
  case v of
    SetupVar{}               -> return v
    SetupTerm tt             -> SetupTerm       <$> doTerm tt
    SetupStruct b p vs       -> SetupStruct b p <$> mapM (instantiateSetupValue sc s) vs
    SetupArray b vs          -> SetupArray b    <$> mapM (instantiateSetupValue sc s) vs
    SetupElem{}              -> return v
    SetupField{}             -> return v
    SetupNull{}              -> return v
    SetupGlobal{}            -> return v
    SetupGlobalInitializer{} -> return v
  where
    doTerm (TypedTerm schema t) =
      TypedTerm schema <$> SAWVerifier.scInstantiateExt sc s t
