{- |
Module      : SAWScript.Crucible.Common.Override.Operations
Description : Operations in the OverrideMatcher monad
License     : BSD3
Maintainer  : langston
Stability   : provisional
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.Crucible.Common.Override.Operations
  ( stateCond
  , resolveSAWPred
  , assignTerm
  , matchTerm
  , instantiateSetupValue

  , matchGhost
  , matchGhostVariablesOM
  , writeGhost
  , writeGhostVariables
  , writeGhostVariablesOM
  ) where

import Control.Lens

import           Control.Monad (foldM)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (traverse_)
import           Data.Map (Map)
import qualified Data.Set as Set
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW

import qualified Lang.Crucible.Simulator.GlobalState as Crucible

import qualified What4.Interface as W4
import qualified What4.LabeledPred as W4
import qualified What4.ProgramLoc as W4

import qualified Verifier.SAW.SharedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm (Term, SharedContext)
import qualified Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.TypedTerm (TypedTerm(..))
import qualified Verifier.SAW.Term.Functor as SAWVerifier
import           Verifier.SAW.Term.Functor (TermF(..), ExtCns(..), VarIndex)
import           Verifier.SAW.Term.Functor (FlatTermF(ExtCns))
import           Verifier.SAW.Prelude (scEq)

import           SAWScript.Crucible.Common (Sym, LabeledPred')
import           SAWScript.Crucible.Common.MethodSpec (PrePost(..), SetupValue(..))
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.Common.Override.Monad

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

resolveSAWPred :: Sym -> Term -> IO (W4.Pred Sym)
resolveSAWPred sym tm = CrucibleSAW.bindSAWTerm sym W4.BaseBoolRepr tm

assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  Sym                                                              ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher env md (Maybe (LabeledPred' Sym))

assignTerm sc cc prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val) >> pure Nothing
       Just old -> matchTerm sc cc prepost val old


matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  Sym                                                           ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher ext md (Maybe (LabeledPred' Sym))
matchTerm _ _ _ real expect | real == expect = return Nothing
matchTerm sc sym prepost real expect =
  do free <- OM (use omFree)
     case SAWVerifier.unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc sym prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            p <- liftIO $ resolveSAWPred sym t
            return $ Just $ W4.LabeledPred p $ PP.vcat $ map PP.text
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

------------------------------------------------------------------------
-- ** Ghost state

-- Enforcing a pre- or post- conditions on ghost variables
--
-- This has symmetric behavior between pre- and post-conditions in verification
-- and override application:
--
-- Verification:
-- * Precondition: Insert the value of the variable into the global state
-- * Postcondition: Match the value against what's in the global state
--
-- Override:
-- * Precondition: Match the value against what's in the global state
-- * Postcondition: Insert the new value into the global state

-- Verification\/post, override\/pre
matchGhost ::
  SharedContext             ->
  PrePost                   ->
  W4.ProgramLoc             ->
  MS.GhostGlobal            ->
  TypedTerm                 ->
  OverrideMatcher ext md (Maybe (LabeledPred' Sym))
matchGhost sc prepost loc ghostVar expected = do
  sym <- getSymInterface
  tryReadGlobal ghostVar >>=
    \case
      Nothing -> fail $ unwords
        [ "Couldn't find ghost global: " ++ show ghostVar
        , "in " ++ stateCond prepost
        , "at " ++ show (PP.pretty (W4.plSourceLoc loc) )
        ]
      Just actual ->
        matchTerm sc sym prepost (SAWVerifier.ttTerm actual) (SAWVerifier.ttTerm expected)

matchGhostVariablesOM ::
  SharedContext ->
  PrePost                   ->
  [MS.GhostCondition] ->
  OverrideMatcher ext md ()
matchGhostVariablesOM sc prepost = traverse_ $
  \(MS.GhostCondition loc var term) -> matchGhost sc prepost loc var term

-- Verification\/pre, override\/post
writeGhost ::
  SharedContext                ->
  Map VarIndex Term            ->
  MS.GhostGlobal               ->
  TypedTerm                    ->
  Crucible.SymGlobalState Sym  ->
  IO (Crucible.SymGlobalState Sym)
writeGhost sc termSub_ ghostVar val state = do
  val' <- SAWVerifier.ttTermLens
            (SAWVerifier.scInstantiateExt sc termSub_)
            val
  return $ Crucible.insertGlobal ghostVar val' state

-- | Write a bunch of ghost variables in a row
writeGhostVariables ::
  SharedContext ->
  Map VarIndex Term ->
  [MS.GhostCondition] ->
  (Crucible.SymGlobalState Sym) ->
  IO (Crucible.SymGlobalState Sym)
writeGhostVariables sc termSub_ ghostVars state = foldM go state ghostVars
  where go state' (MS.GhostCondition _loc var term) =
          writeGhost sc termSub_ var term state'

-- | Like 'writeGhost', but uses the state in the 'OverrideMatcher' monad
writeGhostOM ::
  SharedContext ->
  MS.GhostGlobal ->
  TypedTerm ->
  OverrideMatcher ext md ()
writeGhostOM sc var val = do
  termSub_ <- OM (use termSub)
  state <- OM (use omGlobals)
  state' <- liftIO $ writeGhost sc termSub_ var val state
  omGlobals .= state'

writeGhostVariablesOM ::
  SharedContext ->
  [MS.GhostCondition] ->
  OverrideMatcher ext md ()
writeGhostVariablesOM sc =
  traverse_ $ \(MS.GhostCondition _loc var term) -> writeGhostOM sc var term
