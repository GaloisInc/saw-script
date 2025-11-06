-- | Utilities for resolving 'SetupValue's that are used across language
-- backends.
{-# Language DataKinds, TypeOperators, GADTs, TypeApplications #-}
{-# Language ImplicitParams #-}
module SAWCentral.Crucible.Common.ResolveSetupValue ( 
  resolveBoolTerm, resolveBoolTerm',
  resolveBitvectorTerm, resolveBitvectorTerm',
  ResolveRewrite(..),
  ) where

import qualified Data.Map as Map
import           Data.Set(Set)
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4


import SAWCore.SharedTerm
import SAWCore.Name
import qualified SAWCore.Prim as Prim

import qualified SAWCore.Simulator.Concrete as Concrete
import qualified Lang.Crucible.Types as Crucible
import qualified Lang.Crucible.Simulator.RegValue as Crucible

import SAWCoreWhat4.ReturnTrip

import SAWCentral.Crucible.Common

import SAWCentral.Proof (TheoremNonce)
import SAWCore.Rewriter (Simpset, rewriteSharedTermTypeSafe)
import qualified CryptolSAWCore.Simpset as Cryptol
import SAWCoreWhat4.What4(w4EvalAny, valueToSymExpr)

import Cryptol.TypeCheck.Type (tIsBit, tIsSeq, tIsNum)
import CryptolSAWCore.TypedTerm (mkTypedTerm, ttType, ttIsMono, ppTypedTermType)
import qualified Cryptol.Utils.PP as PP


-- | Optional rewrites to do when resolving a term
data ResolveRewrite = ResolveRewrite {
  rrBasicSS :: Maybe (Simpset TheoremNonce),
  -- ^ Rewrite terms using these rewrites

  rrWhat4Eval :: Bool
  -- ^ Also simplify terms using What4 evaluation
}

-- | Don't do any rewriting
noResolveRewrite :: ResolveRewrite
noResolveRewrite = ResolveRewrite { rrBasicSS = Nothing, rrWhat4Eval = False }

-- Convert a term to a What4 expression, trying to simplify it in the process.
-- Currently this expects the terms to be either boolean or bit-vectors, as
-- that's all we use it for.   It should be fairly straightforward to generalize
-- if need be.
resolveTerm ::
  Sym {- ^ Backend state -} ->
  Set VarIndex {- ^ Keep these opaque -} ->
  W4.BaseTypeRepr t  {- ^ Type of term -} ->
  ResolveRewrite {- ^ Optional rewrites to do on the term -} ->
  Term {- ^ Term to process -} ->
  IO (Crucible.RegValue Sym (Crucible.BaseToType t))
resolveTerm sym unint bt rr tm =
  do
    st       <- sawCoreState sym
    let sc = saw_ctx st
    checkType sc
    tm'      <- basicRewrite sc tm
    canFold <- isConstFoldTerm sc unint tm'
    case () of
      _ | canFold ->
          do -- Evaluate as constant
            modmap <- scGetModuleMap sc
            let v = Concrete.evalSharedTerm modmap mempty mempty tm'
            case bt of
              W4.BaseBoolRepr -> pure (W4.backendPred sym (Concrete.toBool v))
              W4.BaseBVRepr w -> W4.bvLit sym w (BV.mkBV w (Prim.unsigned (Concrete.toWord v)))
              _ -> fail "resolveTerm: expected `Bool` or bit-vector"

        | rrWhat4Eval rr ->
          do -- Try to use rewrites to simplify the term
            cryptol_ss <- Cryptol.mkCryptolSimpset @TheoremNonce sc
            tm''       <- snd <$> rewriteSharedTermTypeSafe sc cryptol_ss tm'
            tm'''      <- basicRewrite sc tm''
            if all isPreludeName (Map.elems (getConstantSet tm''')) then
              do
                (_, _, _, p) <- w4EvalAny sym st sc mempty unint tm'''
                case valueToSymExpr p of
                  Just (Some y)
                    | Just Refl <- testEquality bt ty -> pure y
                    | otherwise -> typeError (show ty)
                    where ty = W4.exprType y
                  _ -> fail ("resolveTerm: unexpected w4Eval result " ++ show p)
              else
                bindSAWTerm sym st bt tm'''

          -- Just bind the term
        | otherwise -> bindSAWTerm sym st bt tm'

  where
  basicRewrite sc =
    case rrBasicSS rr of
      Nothing -> pure
      Just ss -> \t -> snd <$> rewriteSharedTermTypeSafe sc ss t

  isPreludeName nm =
    case nm of
      ModuleIdentifier ident -> identModule ident == preludeName
      _ -> False

  checkType sc =
    do
      schema <- ttType <$> mkTypedTerm sc tm
      case ttIsMono schema of
          Just ty
            | tIsBit ty, W4.BaseBoolRepr <- bt -> pure ()
            | Just (n,el) <- (tIsSeq ty)
            , tIsBit el, Just i <- tIsNum n, W4.BaseBVRepr w <- bt
            , intValue w == i -> pure ()
            | otherwise -> typeError (show (PP.pp ty)) :: IO ()
          Nothing -> typeError (show (ppTypedTermType schema))

  typeError :: String -> IO a
  typeError t = fail $ unlines [
    "Expected type: " ++ (
      case bt of
        W4.BaseBoolRepr  -> "Bit"
        W4.BaseBVRepr w  -> "[" ++ show w ++ "]"
        _             -> show bt),
    "Actual type:   " ++ t
    ]

-- 'resolveTerm' specialized to booleans.
resolveBoolTerm' :: Sym -> Set VarIndex -> ResolveRewrite -> Term -> IO (W4.Pred Sym)
resolveBoolTerm' sym unint = resolveTerm sym unint W4.BaseBoolRepr

-- 'resolveTerm' specialized to booleans, without rewriting.
resolveBoolTerm :: Sym -> Set VarIndex -> Term -> IO (W4.Pred Sym)
resolveBoolTerm sym unint = resolveBoolTerm' sym unint noResolveRewrite

-- 'resolveTerm' specialized to bit-vectors.
resolveBitvectorTerm' ::
  (1 W4.<= w) => Sym -> Set VarIndex -> W4.NatRepr w -> ResolveRewrite -> Term -> IO (W4.SymBV Sym w)
resolveBitvectorTerm' sym unint w = resolveTerm sym unint (W4.BaseBVRepr w)
                  
-- 'resolveTerm' specialized to bit-vectors, without rewriting.
resolveBitvectorTerm :: 
  (1 W4.<= w) => Sym -> Set VarIndex -> W4.NatRepr w -> Term -> IO (W4.SymBV Sym w)
resolveBitvectorTerm sym unint w = resolveBitvectorTerm' sym unint w noResolveRewrite

