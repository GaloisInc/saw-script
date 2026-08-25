{- |
Module      : CryptolSAWCore.IntroRule
Description : Sets of introduction rules
Copyright   : Galois, Inc. 2012-2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module CryptolSAWCore.IntroRule
  ( IntroRule
  , mkIntroRule
  , IntroRuleSet
  , emptyIntroRuleSet
  , insertIntroRuleSet
  , proveWithIntros
  ) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans (lift)
import qualified Data.IntMap as IntMap
import Data.Maybe (mapMaybe)

import SAWCore.Conversion (termPat)
import SAWCore.Name (VarName(..))
import SAWCore.Recognizer
import SAWCore.Rewriter (scMatch)
import SAWCore.SharedTerm
import qualified SAWCore.TermNet as TermNet

-- | An introduction rule of the form @forall ctxt. hyps -> concl@,
-- along with a proof term inhabiting that type.
--
-- Invariant: The 'proof' field inhabits the same type returned by
-- @scPiList sc ctxt =<< scFunAll sc hyps concl@.
-- Invariant: All variables in 'ctxt' should occur free in 'concl'.
data IntroRule =
  IntroRule
  { ctxt :: [(VarName, Term)]
  , hyps :: [Term]
  , concl :: Term
  , proof :: Term
  }
  deriving Eq

mkIntroRule :: SharedContext -> Term -> IO IntroRule
mkIntroRule sc t0 =
  do ty <- scTypeOf sc t0
     let (vs, hs, c) = go ty
     pure (IntroRule vs hs c t0)
  where
    go :: Term -> ([(VarName, Term)], [Term], Term)
    go t =
      case asPi t of
        Just (x, ty, body)
          | IntMap.member (vnIndex x) (varTypes body) ->
            let (vs, hs, c) = go body in ((x, ty) : vs, hs, c)
          | otherwise ->
            let (hs, c) = asFunAll body in ([], ty : hs, c)
        Nothing ->
          ([], [], t)

-- | A set of 'IntroRule's, indexed by conclusion in a a
-- 'TermNet.Net'.
newtype IntroRuleSet = IntroRuleSet (TermNet.Net IntroRule)

emptyIntroRuleSet :: IntroRuleSet
emptyIntroRuleSet = IntroRuleSet TermNet.empty

insertIntroRuleSet :: IntroRule -> IntroRuleSet -> IntroRuleSet
insertIntroRuleSet r (IntroRuleSet net) =
  IntroRuleSet (TermNet.insert_term (termPat (concl r), r) net)

-- | Attempt to construct a term inhabiting a given type using a set
-- of introduction rules.
-- A failing 'Left' result includes the type of a subgoal with no
-- matching rule; a successful 'Right' result includes a proof term.
proveWithIntros :: SharedContext -> IntroRuleSet -> Term -> IO (Either Term Term)
proveWithIntros sc (IntroRuleSet net) t0 = runExceptT (solve t0)
  where
    solve :: Term -> ExceptT Term IO Term
    solve t = try (TermNet.match_term net (termPat t)) t

    try :: [IntroRule] -> Term -> ExceptT Term IO Term
    try [] t = throwError t
    try (rule : rules) t =
      do result <- lift $ scMatch sc (ctxt rule) (concl rule) t
         case result of
           Nothing -> try rules t
           Just inst ->
             do subgoals <- lift $ traverse (scInstantiate sc inst) (hyps rule)
                subproofs <- traverse solve subgoals
                let params = mapMaybe (\(x, _) -> IntMap.lookup (vnIndex x) inst) (ctxt rule)
                lift $ scApplyAll sc (proof rule) (params ++ subproofs)
