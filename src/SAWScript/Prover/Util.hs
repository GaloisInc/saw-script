module SAWScript.Prover.Util where


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



