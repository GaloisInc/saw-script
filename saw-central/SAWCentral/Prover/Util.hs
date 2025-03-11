module SAWScript.Prover.Util where

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue
import Verifier.SAW.TypedTerm

import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty)

import SAWScript.Crucible.Common.MethodSpec (ppTypedTermType)

-- | Is this a bool, or something that returns bool.
checkBooleanType :: C.Type -> IO ()
checkBooleanType ty
  | C.tIsBit ty                 = return ()
  | Just (_,ty') <- C.tIsFun ty = checkBooleanType ty'
  | otherwise = fail ("Invalid non-boolean type: " ++ pretty ty)

-- | Make sure that this schema is monomorphic, and either boolean,
-- or something that returns a boolean.
checkBooleanSchema :: TypedTermType -> IO ()
checkBooleanSchema (TypedTermSchema (C.Forall [] [] t)) = checkBooleanType t
checkBooleanSchema (TypedTermSchema s) = fail ("Invalid polymorphic type: " ++ pretty s)
checkBooleanSchema tp =
  fail ("Expected boolean type, but got " ++ show (ppTypedTermType tp))

bindAllExts :: SharedContext -> Term -> IO Term
bindAllExts sc body = scAbstractExts sc (getAllExts body) body

liftCexBB :: [FiniteType] -> [Bool] -> Either String [FiniteValue]
liftCexBB tys bs =
  case readFiniteValues tys bs of
    Nothing -> Left "Failed to lift counterexample"
    Just fvs -> Right fvs

-- | Lift a counterexample containing little-endian words
liftLECexBB :: [FiniteType] -> [Bool] -> Either String [FiniteValue]
liftLECexBB tys bs =
  case readFiniteValuesLE tys bs of
    Nothing -> Left "Failed to lift counterexample"
    Just fvs -> Right fvs
