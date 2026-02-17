module SAWCentral.Prover.Util where

import qualified Data.Text as Text

import qualified Cryptol.TypeCheck.AST as C

import qualified SAWSupport.Pretty as PPS

import SAWCore.SharedTerm
import SAWCore.FiniteValue
import qualified CryptolSAWCore.Pretty as CryPP
import CryptolSAWCore.TypedTerm


-- | Is this a bool, or something that returns bool.
checkBooleanType :: C.Type -> IO ()
checkBooleanType ty
  | C.tIsBit ty                 = return ()
  | Just (_,ty') <- C.tIsFun ty = checkBooleanType ty'
  | otherwise = fail ("Invalid non-boolean type: " ++ Text.unpack (CryPP.pp ty))

-- | Make sure that this schema is monomorphic, and either boolean,
-- or something that returns a boolean.
checkBooleanSchema :: SharedContext -> TypedTermType -> IO ()
checkBooleanSchema _ (TypedTermSchema (C.Forall [] [] t)) = checkBooleanType t
checkBooleanSchema _ (TypedTermSchema s) = fail $ "Invalid polymorphic type: " ++ Text.unpack (CryPP.pp s)
checkBooleanSchema sc tp = do
  tp' <- ppTypedTermType sc PPS.defaultOpts tp
  fail $ "Expected boolean type, but got " ++ (Text.unpack tp')

bindAllExts :: SharedContext -> Term -> IO Term
bindAllExts sc body = scLambdaList sc (getAllVars body) body

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
