{- |
Module      : SAWCentral.Yosys.Theorem
Description : Utilities for rewriting/compositional verification of HDL modules
License     : BSD3
Maintainer  : sbreese
Stability   : experimental
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language LambdaCase #-}
{-# Language ViewPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SAWCentral.Yosys.Theorem where

import Control.Lens.TH (makeLenses)

import Control.Lens ((^.))

import Data.Text (Text)
import Data.Map (Map)


import qualified SAWCore.Cache as SC
import qualified SAWCore.Name as SC
import qualified SAWCore.Prelude.Constants as SC (preludeModuleName)
import qualified SAWCore.SharedTerm as SC
import qualified CryptolSAWCore.TypedTerm as SC
import qualified SAWCore.Recognizer as R
import qualified SAWCore.QualName as QN

import qualified CryptolSAWCore.Cryptol as CSC

import qualified Cryptol.TypeCheck.Type as C

import SAWCentral.Yosys.Utils

newtype YosysImport = YosysImport { yosysImport :: Map Text SC.TypedTerm }

data YosysTheorem = YosysTheorem
  { _theoremQualName:: QN.QualName -- ^ qualified name identifying overridden module
  , _theoremInputCryptolType :: C.Type -- ^ cryptol type of r
  , _theoremOutputCryptolType :: C.Type -- ^ cryptol type of (module r)
  , _theoremInputType :: SC.Term -- ^ type of r
  , _theoremOutputType :: SC.Term -- ^ type of (module r)
  , _theoremModule :: SC.Term -- ^ {{ \r -> module r }}
  , _theoremPrecond :: Maybe SC.Term -- ^ {{ \r -> precond r }}
  , _theoremBody :: SC.Term -- ^ {{ \r -> other r }}
  }
makeLenses ''YosysTheorem

-- | Construct a SAWCore proposition for the given theorem.
-- In pseudo-Cryptol, this looks like {{ \r -> precond r ==> (module r == body r) }}
theoremProp ::
  SC.SharedContext ->
  YosysTheorem ->
  IO SC.TypedTerm
theoremProp sc thm =
  do r <- SC.scFreshVariable sc "r" $ thm ^. theoremInputType
     modr <- SC.scApply sc (thm ^. theoremModule) r
     bodyr <- SC.scApply sc (thm ^. theoremBody) r
     equality <- eqBvRecords sc (thm ^. theoremOutputCryptolType) modr bodyr
     res <-
       case thm ^. theoremPrecond of
         Nothing -> pure equality
         Just pc ->
           do pcr <- SC.scApply sc pc r
              SC.scImplies sc pcr equality
     func <- SC.scAbstractTerms sc [r] res
     let cty = C.tFun (thm ^. theoremInputCryptolType) C.tBit
     pure (SC.TypedTerm (SC.TypedTermSchema (C.tMono cty)) func)

-- | Construct a SAWCore proposition for the given theorem.
-- In pseudo-Cryptol, this looks like {{ \r -> if precond r then body r else module r }}
theoremReplacement ::
  SC.SharedContext ->
  YosysTheorem ->
  IO SC.Term
theoremReplacement sc thm =
  do r <- SC.scFreshVariable sc "r" $ thm ^. theoremInputType
     body <-
       case thm ^. theoremPrecond of
          Nothing -> SC.scApply sc (thm ^. theoremBody) r
          Just pc ->
            do precond <- SC.scApply sc pc r
               thenCase <- SC.scApply sc (thm ^. theoremBody) r
               elseCase <- SC.scApply sc (thm ^. theoremModule) r
               SC.scIte sc (thm ^. theoremOutputType) precond thenCase elseCase
     SC.scAbstractTerms sc [r] body

-- | Given a SAWCore term corresponding to an HDL module, a specification, and a precondition:
-- Construct a theorem summarizing the relationship between the module and the specification.
buildTheorem ::
  SC.SharedContext ->
  SC.TypedTerm ->
  SC.Term ->
  Maybe SC.TypedTerm ->
  SC.TypedTerm ->
  IO YosysTheorem
buildTheorem sc ymod newmod precond body = do
  cty <-
    case SC.ttType ymod of
      SC.TypedTermSchema (C.Forall [] [] cty) -> pure cty
      _ -> yosysError YosysErrorInvalidOverrideTarget
  (cinpTy, coutTy) <-
    case cty of
      C.TCon (C.TC C.TCFun) [ci, co] -> pure (ci, co)
      _ -> yosysError YosysErrorInvalidOverrideTarget
  inpTy <- CSC.importType sc CSC.emptyEnv cinpTy
  outTy <- CSC.importType sc CSC.emptyEnv coutTy
  nmi <-
    case reduceSelectors (SC.ttTerm ymod) of
      (R.asConstant -> Just (SC.Name _ nmi)) -> pure nmi
      _ -> yosysError YosysErrorInvalidOverrideTarget
  qn <-
    case nmi of
      SC.ImportedName qn _ -> pure qn
      _ -> yosysError YosysErrorInvalidOverrideTarget
  pure YosysTheorem
    { _theoremQualName = qn
    , _theoremInputCryptolType = cinpTy
    , _theoremOutputCryptolType = coutTy
    , _theoremInputType = inpTy
    , _theoremOutputType = outTy
    , _theoremModule = newmod
    , _theoremPrecond = SC.ttTerm <$> precond
    , _theoremBody = SC.ttTerm body
    }

-- | Reduce nested tuple and record selectors at the top-level of the
-- given term, if possible.
reduceSelectors :: SC.Term -> SC.Term
reduceSelectors t =
  case t of
    (R.asPairSelector -> Just (t1, b)) ->
      case R.asPairValue (reduceSelectors t1) of
        Nothing -> t
        Just (x, y) -> if b then y else x
    (R.asRecordSelector -> Just (t1, fname)) ->
      case R.asRecordValue (reduceSelectors t1) of
        Nothing -> t
        Just tm ->
          case lookup fname tm of
            Nothing -> t
            Just t' -> t'
    _ -> t

-- | Applying a theorem thm as an "override" in a Yosys-derived term t proceeds as follows:
--  1) unfold all names except thm.theoremQualName in t
--  2) traverse t, looking for constants named thm.theoremQualName
--  4) replace the constant term with either thm.theoremBody, or
--     {{ \r -> if thm.theoremPrecond r then thm.theoremBody r else thm.theoremQualName r }}
--     in the presence of a precondition
applyOverride ::
  SC.SharedContext ->
  YosysTheorem ->
  SC.Term ->
  IO SC.Term
applyOverride sc thm t = do
  tidx <-
    do result <- SC.scResolveQualName sc $ thm ^. theoremQualName
       case result of
         Nothing -> yosysError . YosysErrorOverrideNameNotFound . QN.render $ thm ^. theoremQualName
         Just i -> pure i
  -- unfold everything except for theoremQualName and prelude constants
  let isPreludeName (SC.ModuleIdentifier ident) = SC.identModule ident == SC.preludeModuleName
      isPreludeName _ = False
  let unfold nm = SC.nameIndex nm /= tidx && not (isPreludeName (SC.nameInfo nm))
  unfolded <- SC.scUnfoldConstants sc unfold t
  cache <- SC.newIntCache
  let
    go :: SC.Term -> IO SC.Term
    go s =
      SC.useIntCache cache (SC.termIndex s) $
      case SC.unwrapTermF s of
        SC.Constant (SC.Name idx _)
          | idx == tidx -> theoremReplacement sc thm
          | otherwise -> pure s
        _ -> SC.scTermF sc =<< traverse go (SC.unwrapTermF s)
  go unfolded
