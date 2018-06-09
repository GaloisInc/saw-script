{- |
Module      : SAWScript.VerificationCheck
Description : Equality and predicate assertions.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
module SAWScript.VerificationCheck where

import Control.Monad
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Eval.Monad as CV
import qualified Cryptol.Eval.Value as CV
import Verifier.SAW.Cryptol (exportValueWithSchema, scCryptolType)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Simulator.Concrete (CValue)
import Text.PrettyPrint.ANSI.Leijen

import Verifier.SAW.Cryptol (scCryptolEq)
import qualified SAWScript.Value as SV (PPOpts(..), cryptolPPOpts, quietEvalOpts)

data VerificationCheck
  = AssertionCheck String Term
    -- ^ A predicate to check with a name and term.
  | EqualityCheck String  -- Name of value to compare
                  Term    -- Value returned by implementation.
                  Term    -- Expected value in Spec.
    -- ^ Check that equality assertion is true.

vcName :: VerificationCheck -> String
vcName (AssertionCheck nm _) = nm
vcName (EqualityCheck nm _ _) = nm

-- | Returns goal that one needs to prove.
vcGoal :: SharedContext -> VerificationCheck -> IO Term
vcGoal _ (AssertionCheck _ n) = return n
vcGoal sc (EqualityCheck _ x y) = scCryptolEq sc x y

type CounterexampleFn = (Term -> IO CValue) -> IO Doc

-- | Returns documentation for check that fails.
vcCounterexample :: SharedContext -> SV.PPOpts -> VerificationCheck -> CounterexampleFn
vcCounterexample _ opts (AssertionCheck nm n) _ = do
  let opts' = defaultPPOpts { ppBase = SV.ppOptsBase opts }
  return $ text ("Assertion " ++ nm ++ " is unsatisfied:") <+>
           ppTerm opts' n
vcCounterexample sc opts (EqualityCheck nm impNode specNode) evalFn =
  do ln <- evalFn impNode
     sn <- evalFn specNode
     lty <- scTypeOf sc impNode
     lct <- scCryptolType sc lty
     sty <- scTypeOf sc specNode
     sct <- scCryptolType sc sty
     let lschema = (C.Forall [] [] lct)
         sschema = (C.Forall [] [] sct)
     unless (lschema == sschema) $ fail "Mismatched schemas in counterexample"
     let lv = exportValueWithSchema lschema ln
         sv = exportValueWithSchema sschema sn
         opts' = SV.cryptolPPOpts opts
     -- Grr. Different pretty-printers.
     lv_doc <- CV.runEval SV.quietEvalOpts (CV.ppValue opts' lv)
     sv_doc <- CV.runEval SV.quietEvalOpts (CV.ppValue opts' sv)

     return (text nm <$$>
        nest 2 (text "Encountered: " <+>
                text (show lv_doc)) <$$>
        nest 2 (text "Expected:    " <+>
                text (show sv_doc)))

ppCheck :: VerificationCheck -> Doc
ppCheck (AssertionCheck nm tm) =
  hsep [ text (nm ++ ":")
       , ppTerm defaultPPOpts tm
       ]
ppCheck (EqualityCheck nm tm tm') =
  hsep [ text (nm ++ ":")
       , ppTerm defaultPPOpts tm
       , text ":="
       , ppTerm defaultPPOpts tm'
       ]
