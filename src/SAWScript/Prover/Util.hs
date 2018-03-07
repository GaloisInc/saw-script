module SAWScript.Prover.Util where

import Verifier.SAW.SharedTerm
import Verifier.SAW.FiniteValue

import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty)

-- | Is this a bool, or something that returns bool.
checkBooleanType :: C.Type -> IO ()
checkBooleanType ty
  | C.tIsBit ty                 = return ()
  | Just (_,ty') <- C.tIsFun ty = checkBooleanType ty'
  | otherwise = fail ("Invalid non-boolean type: " ++ pretty ty)

-- | Make sure that this schema is monomorphic, and either boolean,
-- or something that returns a boolean.
checkBooleanSchema :: C.Schema -> IO ()
checkBooleanSchema (C.Forall [] [] t) = checkBooleanType t
checkBooleanSchema s = fail ("Invalid polymorphic type: " ++ pretty s)

bindAllExts :: SharedContext -> Term -> IO Term
bindAllExts sc body = scAbstractExts sc (getAllExts body) body

liftCexBB :: [FiniteType] -> [Bool] -> Either String [FiniteValue]
liftCexBB tys bs =
  case readFiniteValues tys bs of
    Nothing -> Left "Failed to lift counterexample"
    Just fvs -> Right fvs



