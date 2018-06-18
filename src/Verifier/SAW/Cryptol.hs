{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : Verifier.SAW.Cryptol
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Cryptol where

import Control.Monad (foldM, join, unless)
import qualified Data.Foldable as Fold
import Data.List
import qualified Data.IntTrie as IntTrie
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import Prelude ()
import Prelude.Compat

import qualified Cryptol.Eval.Type as TV
import qualified Cryptol.Eval.Monad as V
import qualified Cryptol.Eval.Value as V
import Cryptol.Eval.Type (evalValType)
import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.Subst as C (Subst, apSubst, singleSubst)
import qualified Cryptol.ModuleSystem.Name as C (asPrim, nameIdent)
import qualified Cryptol.Utils.Ident as C (Ident, packIdent, unpackIdent)
import qualified Cryptol.Utils.Logger as C (quietLogger)
import Cryptol.TypeCheck.TypeOf (fastTypeOf, fastSchemaOf)
import Cryptol.Utils.PP (pretty)

import Verifier.SAW.Conversion
import Verifier.SAW.FiniteValue (FirstOrderType(..), FirstOrderValue(..))
import qualified Verifier.SAW.Simulator.Concrete as SC
import Verifier.SAW.Prim (BitVector(..))
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Simulator.MonadLazy (force)
import Verifier.SAW.TypedAST (mkSort, mkModuleName, showTerm)

unimplemented :: Monad m => String -> m a
unimplemented name = fail ("unimplemented: " ++ name)

panic :: Monad m => String -> m a
panic name = fail ("panic: " ++ name)

--------------------------------------------------------------------------------
-- Type Environments

-- | SharedTerms are paired with a deferred shift amount for loose variables
data Env = Env
  { envT :: Map Int    (Term, Int) -- ^ Type variables are referenced by unique id
  , envE :: Map C.Name (Term, Int) -- ^ Term variables are referenced by name
  , envP :: Map C.Prop (Term, Int) -- ^ Bound propositions are referenced implicitly by their types
  , envC :: Map C.Name C.Schema    -- ^ Cryptol type environment
  , envS :: [Term]                 -- ^ SAW-Core bound variable environment (for type checking)
  }

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty []

liftTerm :: (Term, Int) -> (Term, Int)
liftTerm (t, j) = (t, j + 1)

-- | Increment dangling bound variables of all types in environment.
liftEnv :: Env -> Env
liftEnv env =
  Env { envT = fmap liftTerm (envT env)
      , envE = fmap liftTerm (envE env)
      , envP = fmap liftTerm (envP env)
      , envC = envC env
      , envS = envS env
      }

bindTParam :: SharedContext -> C.TParam -> Env -> IO Env
bindTParam sc tp env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  k <- importKind sc (C.tpKind tp)
  return $ env' { envT = Map.insert (C.tpUnique tp) (v, 0) (envT env')
                , envS = k : envS env }

bindName :: SharedContext -> C.Name -> C.Schema -> Env -> IO Env
bindName sc name schema env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  t <- importSchema sc env schema
  return $ env' { envE = Map.insert name (v, 0) (envE env')
                , envC = Map.insert name schema (envC env')
                , envS = t : envS env' }

bindProp :: SharedContext -> C.Prop -> Env -> IO Env
bindProp sc prop env = do
  let env' = liftEnv env
  v <- scLocalVar sc 0
  k <- scSort sc (mkSort 0)
  return $ env' { envP = Map.insert prop (v, 0) (envP env')
                , envS = k : envS env' }

--------------------------------------------------------------------------------

importKind :: SharedContext -> C.Kind -> IO Term
importKind sc kind =
  case kind of
    C.KType       -> scSort sc (mkSort 0)
    C.KNum        -> scDataTypeApp sc "Cryptol.Num" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

importTFun :: SharedContext -> C.TFun -> IO Term
importTFun sc tf =
  case tf of
    C.TCWidth         -> scGlobalDef sc "Cryptol.tcWidth"
    C.TCAdd           -> scGlobalDef sc "Cryptol.tcAdd"
    C.TCSub           -> scGlobalDef sc "Cryptol.tcSub"
    C.TCMul           -> scGlobalDef sc "Cryptol.tcMul"
    C.TCDiv           -> scGlobalDef sc "Cryptol.tcDiv"
    C.TCMod           -> scGlobalDef sc "Cryptol.tcMod"
    C.TCExp           -> scGlobalDef sc "Cryptol.tcExp"
    C.TCMin           -> scGlobalDef sc "Cryptol.tcMin"
    C.TCMax           -> scGlobalDef sc "Cryptol.tcMax"
    C.TCCeilDiv       -> scGlobalDef sc "Cryptol.tcCeilDiv"
    C.TCCeilMod       -> scGlobalDef sc "Cryptol.tcCeilMod"
    C.TCLenFromThen   -> scGlobalDef sc "Cryptol.tcLenFromThen"
    C.TCLenFromThenTo -> scGlobalDef sc "Cryptol.tcLenFromThenTo"

importPC :: SharedContext -> C.PC -> IO Term
importPC sc pc =
  case pc of
    C.PEqual     -> panic "importPC PEqual"
    C.PNeq       -> panic "importPC PNeq"
    C.PGeq       -> panic "importPC PGeq"
    C.PFin       -> panic "importPC PFin"
    C.PHas _     -> panic "importPC PHas"
    C.PZero      -> scGlobalDef sc "Cryptol.PZero"
    C.PLogic     -> scGlobalDef sc "Cryptol.PLogic"
    C.PArith     -> scGlobalDef sc "Cryptol.PArith"
    C.PCmp       -> scGlobalDef sc "Cryptol.PCmp"
    C.PSignedCmp -> scGlobalDef sc "Cryptol.PSignedCmp"
    C.PAnd       -> panic "importPC PAnd"
    C.PTrue      -> panic "importPC PTrue"

-- | Translate size types to SAW values of type Num, value types to SAW types of sort 0.
importType :: SharedContext -> Env -> C.Type -> IO Term
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} -> unimplemented "TVFree"
        C.TVBound v -> case Map.lookup (C.tpUnique v) (envT env) of
                         Just (t, j) -> incVars sc 0 j t
                         Nothing -> panic "importType TVBound"
    C.TUser _ _ t  -> go t
    C.TRec fs -> scRecordType sc =<< mapM (\(f,t) -> (f,) <$> go t) tm
      where tm = [ (C.unpackIdent n, t) | (n, t) <- fs ]
    C.TCon tcon tyargs ->
      case tcon of
        C.TC tc ->
          case tc of
            C.TCNum n    -> scCtorApp sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger n)]
            C.TCInf      -> scCtorApp sc "Cryptol.TCInf" []
            C.TCBit      -> scBoolType sc
            C.TCInteger  -> scIntegerType sc
            C.TCSeq      -> scGlobalApply sc "Cryptol.seq" =<< traverse go tyargs
            C.TCFun      -> do a <- go (tyargs !! 0)
                               b <- go (tyargs !! 1)
                               scFun sc a b
            C.TCTuple _n -> scTupleType sc =<< traverse go tyargs
            C.TCNewtype (C.UserTC _qn _k) -> unimplemented "TCNewtype" -- user-defined, @T@
            C.TCIntMod   -> unimplemented "TCIntMod"
        C.PC pc ->
          do pc' <- importPC sc pc
             tyargs' <- traverse go tyargs
             scApplyAll sc pc' tyargs'
        C.TF tf ->
          do tf' <- importTFun sc tf
             tyargs' <- traverse go tyargs
             scApplyAll sc tf' tyargs'
        C.TError _k _msg ->
          panic "importType TError"
  where
    go = importType sc env

isErasedProp :: C.Prop -> Bool
isErasedProp prop =
  case prop of
    C.TCon (C.PC C.PZero     ) _ -> False
    C.TCon (C.PC C.PLogic    ) _ -> False
    C.TCon (C.PC C.PArith    ) _ -> False
    C.TCon (C.PC C.PCmp      ) _ -> False
    C.TCon (C.PC C.PSignedCmp) _ -> False
    _ -> True

importPropsType :: SharedContext -> Env -> [C.Prop] -> C.Type -> IO Term
importPropsType sc env [] ty = importType sc env ty
importPropsType sc env (prop : props) ty
  | isErasedProp prop = importPropsType sc env props ty
  | otherwise =
    do p <- importType sc env prop
       t <- importPropsType sc env props ty
       scFun sc p t

nameToString :: C.Name -> String
nameToString = C.unpackIdent . C.nameIdent

tparamToString :: C.TParam -> String
--tparamToString tp = maybe "_" nameToString (C.tpName tp)
tparamToString tp = maybe ("u" ++ show (C.tpUnique tp)) nameToString (C.tpName tp)

importPolyType :: SharedContext -> Env -> [C.TParam] -> [C.Prop] -> C.Type -> IO Term
importPolyType sc env [] props ty = importPropsType sc env props ty
importPolyType sc env (tp : tps) props ty =
  do k <- importKind sc (C.tpKind tp)
     env' <- bindTParam sc tp env
     t <- importPolyType sc env' tps props ty
     scPi sc (tparamToString tp) k t

importSchema :: SharedContext -> Env -> C.Schema -> IO Term
importSchema sc env (C.Forall tparams props ty) = importPolyType sc env tparams props ty

proveProp :: SharedContext -> Env -> C.Prop -> IO Term
proveProp sc env prop =
  case Map.lookup prop (envP env) of
    Just (prf, j) -> incVars sc 0 j prf
    Nothing ->
      case prop of
        -- instance Zero Bit
        (C.pIsZero -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PZeroBit" []
        -- instance Zero Integer
        (C.pIsZero -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PZeroInteger" []
        -- instance Zero [n]
        (C.pIsZero -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PZeroSeqBool" [n']
        -- instance (Zero a) => Zero [n]a
        (C.pIsZero -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- proveProp sc env (C.pZero a)
                scGlobalApply sc "Cryptol.PZeroSeq" [n', a', pa]
        -- instance (Zero b) => Zero (a -> b)
        (C.pIsZero -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- proveProp sc env (C.pZero b)
                scGlobalApply sc "Cryptol.PZeroFun" [a', b', pb]
        -- instance (Zero a, Zero b, ...) => Zero (a, b, ...)
        (C.pIsZero -> Just (C.tIsTuple -> Just ts))
          -> do ps <- traverse (proveProp sc env . C.pZero) ts
                scTuple sc ps
        -- instance (Zero a, Zero b, ...) => Zero { x : a, y : b, ... }
        (C.pIsZero -> Just (C.tIsRec -> Just fs))
          -> do let tm = Map.fromList [ (C.unpackIdent n, t) | (n, t) <- fs ]
                pm <- traverse (proveProp sc env . C.pZero) tm
                scRecord sc pm

        -- instance Logic Bit
        (C.pIsLogic -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PLogicBit" []
        -- instance Logic [n]
        (C.pIsLogic -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PLogicSeqBool" [n']
        -- instance (Logic a) => Logic [n]a
        (C.pIsLogic -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- proveProp sc env (C.pLogic a)
                scGlobalApply sc "Cryptol.PLogicSeq" [n', a', pa]
        -- instance (Logic b) => Logic (a -> b)
        (C.pIsLogic -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- proveProp sc env (C.pLogic b)
                scGlobalApply sc "Cryptol.PLogicFun" [a', b', pb]
        -- instance Logic ()
        (C.pIsLogic -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PLogicUnit" []
        -- instance (Logic a, Logic b) => Logic (a, b)
        (C.pIsLogic -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- proveProp sc env (C.pLogic t)
                pb <- proveProp sc env (C.pLogic (C.tTuple ts))
                scGlobalApply sc "Cryptol.PLogicPair" [a, b, pa, pb]
        -- instance Logic {}
        (C.pIsLogic -> Just (C.tIsRec -> Just []))
          -> do scGlobalApply sc "Cryptol.PLogicEmpty" []
        -- instance (Logic a, Logic b) => instance Logic { x : a, y : b }
        (C.pIsLogic -> Just (C.tIsRec -> Just ((n, t) : fs)))
          -> do s <- scString sc (C.unpackIdent n)
                a <- importType sc env t
                b <- importType sc env (C.TRec fs)
                pa <- proveProp sc env (C.pLogic t)
                pb <- proveProp sc env (C.pLogic (C.TRec fs))
                scGlobalApply sc "Cryptol.PLogicField" [s, a, b, pa, pb]

        -- instance Arith Integer
        (C.pIsArith -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PArithInteger" []
        -- instance (fin n) => Arith [n]
        (C.pIsArith -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PArithSeqBool" [n']
        -- instance (Arith a) => Arith [n]a
        (C.pIsArith -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- proveProp sc env (C.pArith a)
                scGlobalApply sc "Cryptol.PArithSeq" [n', a', pa]
        -- instance (Arith b) => Arith (a -> b)
        (C.pIsArith -> Just (C.tIsFun -> Just (a, b)))
          -> do a' <- importType sc env a
                b' <- importType sc env b
                pb <- proveProp sc env (C.pArith b)
                scGlobalApply sc "Cryptol.PArithFun" [a', b', pb]
        -- instance Arith ()
        (C.pIsArith -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PArithUnit" []
        -- instance (Arith a, Arith b) => Arith (a, b)
        (C.pIsArith -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- proveProp sc env (C.pArith t)
                pb <- proveProp sc env (C.pArith (C.tTuple ts))
                scGlobalApply sc "Cryptol.PArithPair" [a, b, pa, pb]
        -- instance Arith {}
        (C.pIsArith -> Just (C.tIsRec -> Just []))
          -> do scGlobalApply sc "Cryptol.PArithEmpty" []
        -- instance (Arith a, Arith b) => instance Arith { x : a, y : b }
        (C.pIsArith -> Just (C.tIsRec -> Just ((n, t) : fs)))
          -> do s <- scString sc (C.unpackIdent n)
                a <- importType sc env t
                b <- importType sc env (C.TRec fs)
                pa <- proveProp sc env (C.pArith t)
                pb <- proveProp sc env (C.pArith (C.TRec fs))
                scGlobalApply sc "Cryptol.PArithField" [s, a, b, pa, pb]

        -- instance Cmp Bit
        (C.pIsCmp -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PCmpBit" []
        -- instance Cmp Integer
        (C.pIsCmp -> Just (C.tIsInteger -> True))
          -> do scGlobalApply sc "Cryptol.PCmpInteger" []
        -- instance (fin n) => Cmp [n]
        (C.pIsCmp -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PCmpSeqBool" [n']
        -- instance (fin n, Cmp a) => Cmp [n]a
        (C.pIsCmp -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- proveProp sc env (C.pCmp a)
                scGlobalApply sc "Cryptol.PCmpSeq" [n', a', pa]
        -- instance Cmp ()
        (C.pIsCmp -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PCmpUnit" []
        -- instance (Cmp a, Cmp b) => Cmp (a, b)
        (C.pIsCmp -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- proveProp sc env (C.pCmp t)
                pb <- proveProp sc env (C.pCmp (C.tTuple ts))
                scGlobalApply sc "Cryptol.PCmpPair" [a, b, pa, pb]
        -- instance Cmp {}
        (C.pIsCmp -> Just (C.tIsRec -> Just []))
          -> do scGlobalApply sc "Cryptol.PCmpEmpty" []
        -- instance (Cmp a, Cmp b) => instance Cmp { x : a, y : b }
        (C.pIsCmp -> Just (C.tIsRec -> Just ((n, t) : fs)))
          -> do s <- scString sc (C.unpackIdent n)
                a <- importType sc env t
                b <- importType sc env (C.TRec fs)
                pa <- proveProp sc env (C.pCmp t)
                pb <- proveProp sc env (C.pCmp (C.TRec fs))
                scGlobalApply sc "Cryptol.PCmpField" [s, a, b, pa, pb]

        -- instance SignedCmp Bit
        (C.pIsSignedCmp -> Just (C.tIsBit -> True))
          -> do scGlobalApply sc "Cryptol.PSignedCmpBit" []
        -- instance (fin n) => SignedCmp [n]
        (C.pIsSignedCmp -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
          -> do n' <- importType sc env n
                scGlobalApply sc "Cryptol.PSignedCmpSeqBool" [n']
        -- instance (fin n, SignedCmp a) => SignedCmp [n]a
        (C.pIsSignedCmp -> Just (C.tIsSeq -> Just (n, a)))
          -> do n' <- importType sc env n
                a' <- importType sc env a
                pa <- proveProp sc env (C.pSignedCmp a)
                scGlobalApply sc "Cryptol.PSignedCmpSeq" [n', a', pa]
        -- instance SignedCmp ()
        (C.pIsSignedCmp -> Just (C.tIsTuple -> Just []))
          -> do scGlobalApply sc "Cryptol.PSignedCmpUnit" []
        -- instance (SignedCmp a, SignedCmp b) => SignedCmp (a, b)
        (C.pIsSignedCmp -> Just (C.tIsTuple -> Just (t : ts)))
          -> do a <- importType sc env t
                b <- importType sc env (C.tTuple ts)
                pa <- proveProp sc env (C.pSignedCmp t)
                pb <- proveProp sc env (C.pSignedCmp (C.tTuple ts))
                scGlobalApply sc "Cryptol.PSignedCmpPair" [a, b, pa, pb]
        -- instance SignedCmp {}
        (C.pIsSignedCmp -> Just (C.tIsRec -> Just []))
          -> do scGlobalApply sc "Cryptol.PSignedCmpEmpty" []
        -- instance (SignedCmp a, SignedCmp b) => instance SignedCmp { x : a, y : b }
        (C.pIsSignedCmp -> Just (C.tIsRec -> Just ((n, t) : fs)))
          -> do s <- scString sc (C.unpackIdent n)
                a <- importType sc env t
                b <- importType sc env (C.TRec fs)
                pa <- proveProp sc env (C.pSignedCmp t)
                pb <- proveProp sc env (C.pSignedCmp (C.TRec fs))
                scGlobalApply sc "Cryptol.PSignedCmpField" [s, a, b, pa, pb]

        _ -> do panic $ "proveProp: " ++ pretty prop

importPrimitive :: SharedContext -> C.Name -> IO Term
importPrimitive sc (C.asPrim -> Just nm) =
  case nm of
    "True"          -> scBool sc True
    "False"         -> scBool sc False
    "demote"        -> scGlobalDef sc "Cryptol.ecDemote"      -- Converts a numeric type into its corresponding value.
                                                     -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    "integer"       -> scGlobalDef sc "Cryptol.ecInteger"     -- {n} (fin n) => Integer
    "toInteger"     -> scGlobalDef sc "Cryptol.ecToInteger"   -- {n} (fin n) => [n] -> Integer
    "fromInteger"   -> scGlobalDef sc "Cryptol.ecFromInteger" -- {n} (fin n) => Integer -> [n]
    "+"             -> scGlobalDef sc "Cryptol.ecPlus"        -- {a} (Arith a) => a -> a -> a
    "-"             -> scGlobalDef sc "Cryptol.ecMinus"       -- {a} (Arith a) => a -> a -> a
    "*"             -> scGlobalDef sc "Cryptol.ecMul"         -- {a} (Arith a) => a -> a -> a
    "/"             -> scGlobalDef sc "Cryptol.ecDiv"         -- {a} (Arith a) => a -> a -> a
    "%"             -> scGlobalDef sc "Cryptol.ecMod"         -- {a} (Arith a) => a -> a -> a
    "^^"            -> scGlobalDef sc "Cryptol.ecExp"         -- {a} (Arith a) => a -> a -> a
    "lg2"           -> scGlobalDef sc "Cryptol.ecLg2"         -- {a} (Arith a) => a -> a
    "negate"        -> scGlobalDef sc "Cryptol.ecNeg"         -- {a} (Arith a) => a -> a
    "/$"            -> scGlobalDef sc "Cryptol.ecSDiv"        -- {a} (Arith a) => a -> a -> a
    "%$"            -> scGlobalDef sc "Cryptol.ecSMod"        -- {a} (Arith a) => a -> a -> a
    "<"             -> scGlobalDef sc "Cryptol.ecLt"          -- {a} (Cmp a) => a -> a -> Bit
    ">"             -> scGlobalDef sc "Cryptol.ecGt"          -- {a} (Cmp a) => a -> a -> Bit
    "<="            -> scGlobalDef sc "Cryptol.ecLtEq"        -- {a} (Cmp a) => a -> a -> Bit
    ">="            -> scGlobalDef sc "Cryptol.ecGtEq"        -- {a} (Cmp a) => a -> a -> Bit
    "=="            -> scGlobalDef sc "Cryptol.ecEq"          -- {a} (Cmp a) => a -> a -> Bit
    "!="            -> scGlobalDef sc "Cryptol.ecNotEq"       -- {a} (Cmp a) => a -> a -> Bit
    "<$"            -> scGlobalDef sc "Cryptol.ecSLt"         -- {a} (SignedCmp a) => a -> a -> Bit
    ">>$"           -> scGlobalDef sc "Cryptol.ecSShiftR"     -- {n, k} (fin n, n >= 1, fin k) => [n] -> [k] -> [n]
    "&&"            -> scGlobalDef sc "Cryptol.ecAnd"         -- {a} (Logic a) => a -> a -> a
    "||"            -> scGlobalDef sc "Cryptol.ecOr"          -- {a} (Logic a) => a -> a -> a
    "^"             -> scGlobalDef sc "Cryptol.ecXor"         -- {a} (Logic a) => a -> a -> a
    "complement"    -> scGlobalDef sc "Cryptol.ecCompl"       -- {a} (Logic a) => a -> a
    "zero"          -> scGlobalDef sc "Cryptol.ecZero"        -- {a} (Zero a) => a
    "carry"         -> scGlobalDef sc "Cryptol.ecCarry"       -- {n} (fin n) => [n] -> [n] -> Bit
    "scarry"        -> scGlobalDef sc "Cryptol.ecSCarry"      -- {n} (fin n, n >= 1) => [n] -> [n] -> Bit
    "<<"            -> scGlobalDef sc "Cryptol.ecShiftL"      -- {m,n,a} (fin n, Zero a) => [m] a -> [n] -> [m] a
    ">>"            -> scGlobalDef sc "Cryptol.ecShiftR"      -- {m,n,a} (fin n, Zero a) => [m] a -> [n] -> [m] a
    "<<<"           -> scGlobalDef sc "Cryptol.ecRotL"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    ">>>"           -> scGlobalDef sc "Cryptol.ecRotR"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    "#"             -> scGlobalDef sc "Cryptol.ecCat"         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    "splitAt"       -> scGlobalDef sc "Cryptol.ecSplitAt"     -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    "join"          -> scGlobalDef sc "Cryptol.ecJoin"        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    "split"         -> scGlobalDef sc "Cryptol.ecSplit"       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    "reverse"       -> scGlobalDef sc "Cryptol.ecReverse"     -- {a,b} (fin a) => [a] b -> [a] b
    "transpose"     -> scGlobalDef sc "Cryptol.ecTranspose"   -- {a,b,c} [a][b]c -> [b][a]c
    "@"             -> scGlobalDef sc "Cryptol.ecAt"          -- {n,a,i} (fin i) => [n]a -> [i] -> a
    "!"             -> scGlobalDef sc "Cryptol.ecAtBack"      -- {n,a,i} (fin n, fin i) => [n]a -> [i] -> a
    "update"        -> scGlobalDef sc "Cryptol.ecUpdate"      -- {a,b,c} (fin c) => [a]b -> [c] -> b -> [a]b
    "updateEnd"     -> scGlobalDef sc "Cryptol.ecUpdateEnd"   -- {a,b,c} (fin a, fin c) => [a]b -> [c] -> b -> [a]b
    "fromThen"      -> scGlobalDef sc "Cryptol.ecFromThen"
                               -- fromThen : {first,next,bits,len}
                               --             ( fin first, fin next, fin bits
                               --             , bits >= width first, bits >= width next
                               --             , lengthFromThen first next bits == len
                               --             )
                               --          => [len] [bits]
    "fromTo"        -> scGlobalDef sc "Cryptol.ecFromTo"
                               -- fromTo : {first, last, bits}
                               --           ( fin last, fin bits, last >== first, bits >== width last)
                               --        => [1 + (last - first)] [bits]
    "fromThenTo"    -> scGlobalDef sc "Cryptol.ecFromThenTo"
    "infFrom"       -> scGlobalDef sc "Cryptol.ecInfFrom"     -- {a} (fin a) => [a] -> [inf][a]
    "infFromThen"   -> scGlobalDef sc "Cryptol.ecInfFromThen" -- {a} (fin a) => [a] -> [a] -> [inf][a]
    "error"         -> scGlobalDef sc "Cryptol.ecError"       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
    "random"        -> scGlobalDef sc "Cryptol.ecRandom"      -- {a} => [32] -> a -- Random values
    "trace"         -> scGlobalDef sc "Cryptol.ecTrace"       -- {n,a,b} [n][8] -> a -> b -> b

    _ -> panic $ unwords ["Unknown Cryptol primitive name:", C.unpackIdent nm]

importPrimitive _ nm =
  panic $ unwords ["Improper Cryptol primitive name:", show nm]


-- | Convert a Cryptol expression to a SAW-Core term. Calling
-- 'scTypeOf' on the result of @'importExpr' sc env expr@ must yield a
-- type that is equivalent (i.e. convertible) with the one returned by
-- @'importSchema' sc env ('fastTypeOf' ('envC' env) expr)@.
importExpr :: SharedContext -> Env -> C.Expr -> IO Term
importExpr sc env expr =
  case expr of
    C.EList es t ->
      do t' <- importType sc env t
         es' <- traverse (importExpr' sc env (C.tMono t)) es
         scVector sc t' es'

    C.ETuple es ->
      do es' <- traverse (importExpr sc env) es
         scTuple sc es'

    C.ERec fs ->
      do let em = Map.fromList [ (C.unpackIdent n, e) | (n, e) <- fs ]
         em' <- traverse (importExpr sc env) em
         scRecord sc em'

    C.ESel e sel ->
      -- Elimination for tuple/record/list
      case sel of
        C.TupleSel i _maybeLen ->
          do e' <- importExpr sc env e
             let t = fastTypeOf (envC env) e
             case C.tIsTuple t of
               Just _  ->
                 do scTupleSelector sc e' (i+1)
               Nothing ->
                 do f <- mapTupleSelector sc env i t
                    scApply sc f e'
        C.RecordSel x _ ->
          do e' <- importExpr sc env e
             let t = fastTypeOf (envC env) e
             case t of
               C.TRec{} ->
                 do scRecordSelect sc e' (C.unpackIdent x)
               _ ->
                 do f <- mapRecordSelector sc env x t
                    scApply sc f e'
        C.ListSel i _maybeLen ->
          do let t = fastTypeOf (envC env) e
             (n, a) <-
               case C.tIsSeq t of
                 Just (n, a) -> return (n, a)
                 Nothing -> fail "ListSel: not a list type"
             a' <- importType sc env a
             n' <- importType sc env n
             e' <- importExpr sc env e
             i' <- scNat sc (fromIntegral i)
             scGlobalApply sc "Cryptol.eListSel" [a', n', e', i']

    C.EIf e1 e2 e3 ->
      do let ty = fastTypeOf (envC env) e2
         ty' <- importType sc env ty
         e1' <- importExpr sc env e1
         e2' <- importExpr sc env e2
         e3' <- importExpr' sc env (C.tMono ty) e3
         scGlobalApply sc "Prelude.ite" [ty', e1', e2', e3']

    C.EComp len eltty e mss ->
      importComp sc env len eltty e mss

    C.EVar qname ->
      case Map.lookup qname (envE env) of
        Just (e', j) -> incVars sc 0 j e'
        Nothing      -> panic $ "importExpr: unknown variable: " ++ show qname

    C.ETAbs tp e ->
      do env' <- bindTParam sc tp env
         k <- importKind sc (C.tpKind tp)
         e' <- importExpr sc env' e
         scLambda sc (tparamToString tp) k e'

    C.ETApp e t ->
      do e' <- importExpr sc env e
         t' <- importType sc env t
         scApply sc e' t'

    C.EApp e1 e2 ->
      do e1' <- importExpr sc env e1
         let t1 = fastTypeOf (envC env) e1
         t1a <-
           case C.tIsFun t1 of
             Just (a, _) -> return a
             Nothing -> panic "importExpr: expected function type"
         e2' <- importExpr' sc env (C.tMono t1a) e2
         scApply sc e1' e2'

    C.EAbs x t e ->
      do t' <- importType sc env t
         env' <- bindName sc x (C.tMono t) env
         e' <- importExpr sc env' e
         scLambda sc (nameToString x) t' e'

    C.EProofAbs prop e
      | isErasedProp prop -> importExpr sc env e
      | otherwise ->
        do p' <- importType sc env prop
           env' <- bindProp sc prop env
           e' <- importExpr sc env' e
           scLambda sc "_P" p' e'

    C.EProofApp e ->
      case fastSchemaOf (envC env) e of
        C.Forall [] (p : _ps) _ty
          | isErasedProp p -> importExpr sc env e
          | otherwise ->
            do e' <- importExpr sc env e
               prf <- proveProp sc env p
               scApply sc e' prf
        s -> panic $ "EProofApp: invalid type: " ++ show (e, s)

    C.EWhere e dgs ->
      do env' <- importDeclGroups sc env dgs
         importExpr sc env' e

-- | Convert a Cryptol expression with the given type schema to a
-- SAW-Core term. Calling 'scTypeOf' on the result of @'importExpr''
-- sc env schema expr@ must yield a type that is equivalent (i.e.
-- convertible) with the one returned by @'importSchema' sc env
-- schema@.
importExpr' :: SharedContext -> Env -> C.Schema -> C.Expr -> IO Term
importExpr' sc env schema expr =
  case expr of
    C.ETuple es ->
      do ty <- the (C.isMono schema)
         ts <- the (C.tIsTuple ty)
         es' <- sequence (zipWith go ts es)
         scTuple sc es'

    C.ERec fs ->
      do ty <- the (C.isMono schema)
         ts <- the (C.tIsRec ty)
         let tm = Map.fromList [ (C.unpackIdent n, t) | (n, t) <- ts ]
         let em = Map.fromList [ (C.unpackIdent n, e) | (n, e) <- fs ]
         em' <- sequence (Map.intersectionWith go tm em)
         scRecord sc em'

    C.EIf e1 e2 e3 ->
      do ty <- the (C.isMono schema)
         ty' <- importType sc env ty
         e1' <- importExpr sc env e1
         e2' <- importExpr' sc env schema e2
         e3' <- importExpr' sc env schema e3
         scGlobalApply sc "Prelude.ite" [ty', e1', e2', e3']

    C.ETAbs tp e ->
      do schema' <-
           case schema of
             C.Forall (tp1 : tparams) props ty ->
               let s = C.singleSubst (C.TVBound tp1) (C.TVar (C.TVBound tp))
               in return (C.Forall tparams (map (plainSubst s) props) (plainSubst s ty))
             C.Forall [] _ _ -> panic "internal error: unexpected type abstraction"
         env' <- bindTParam sc tp env
         k <- importKind sc (C.tpKind tp)
         e' <- importExpr' sc env' schema' e
         scLambda sc (tparamToString tp) k e'

    C.EAbs x _ e ->
      do ty <- the (C.isMono schema)
         (a, b) <- the (C.tIsFun ty)
         a' <- importType sc env a
         env' <- bindName sc x (C.tMono a) env
         e' <- importExpr' sc env' (C.tMono b) e
         scLambda sc (nameToString x) a' e'

    C.EProofAbs _ e ->
      do (prop, schema') <-
           case schema of
             C.Forall [] (p : ps) ty -> return (p, C.Forall [] ps ty)
             C.Forall _ _ _ -> panic "importExpr: internal type error"
         if isErasedProp prop
           then importExpr' sc env schema' e
           else do p' <- importType sc env prop
                   env' <- bindProp sc prop env
                   e' <- importExpr' sc env' schema' e
                   scLambda sc "_P" p' e'

    C.EWhere e dgs ->
      do env' <- importDeclGroups sc env dgs
         importExpr' sc env' schema e

    C.EList     {} -> fallback
    C.ESel      {} -> fallback
    C.EComp     {} -> fallback
    C.EVar      {} -> fallback
    C.EApp      {} -> fallback
    C.ETApp     {} -> fallback
    C.EProofApp {} -> fallback

  where
    go :: C.Type -> C.Expr -> IO Term
    go t = importExpr' sc env (C.tMono t)

    the :: Maybe a -> IO a
    the = maybe (panic "importExpr: internal type error") return

    fallback :: IO Term
    fallback =
      do let t1 = fastTypeOf (envC env) expr
         t2 <- the (C.isMono schema)
         expr' <- importExpr sc env expr
         coerceTerm sc env t1 t2 expr'

mapTupleSelector :: SharedContext -> Env -> Int -> C.Type -> IO Term
mapTupleSelector sc env i = fmap fst . go
  where
    go :: C.Type -> IO (Term, C.Type)
    go t =
      case C.tNoUser t of
        (C.tIsSeq -> Just (n, a)) -> do
          (f, b) <- go a
          a' <- importType sc env a
          b' <- importType sc env b
          n' <- importType sc env n
          g <- scGlobalApply sc "Cryptol.seqMap" [a', b', n', f]
          return (g, C.tSeq n b)
        (C.tIsFun -> Just (n, a)) -> do
          (f, b) <- go a
          a' <- importType sc env a
          b' <- importType sc env b
          n' <- importType sc env n
          g <- scGlobalApply sc "Cryptol.compose" [n', a', b', f]
          return (g, C.tFun n b)
        (C.tIsTuple -> Just ts) -> do
          x <- scLocalVar sc 0
          y <- scTupleSelector sc x (i+1)
          t' <- importType sc env t
          f <- scLambda sc "x" t' y
          return (f, ts !! i)
        _ -> panic $ unwords ["importExpr: invalid tuple selector", show i, show t]

mapRecordSelector :: SharedContext -> Env -> C.Ident -> C.Type -> IO Term
mapRecordSelector sc env i = fmap fst . go
  where
    go :: C.Type -> IO (Term, C.Type)
    go t =
      case C.tNoUser t of
        (C.tIsSeq -> Just (n, a)) -> do
          (f, b) <- go a
          a' <- importType sc env a
          b' <- importType sc env b
          n' <- importType sc env n
          g <- scGlobalApply sc "Cryptol.seqMap" [a', b', n', f]
          return (g, C.tSeq n b)
        (C.tIsFun -> Just (n, a)) -> do
          (f, b) <- go a
          a' <- importType sc env a
          b' <- importType sc env b
          n' <- importType sc env n
          g <- scGlobalApply sc "Cryptol.compose" [n', a', b', f]
          return (g, C.tFun n b)
        (C.tIsRec -> Just ts) | Just b <- lookup i ts -> do
          x <- scLocalVar sc 0
          y <- scRecordSelect sc x (C.unpackIdent i)
          t' <- importType sc env t
          f <- scLambda sc "x" t' y
          return (f, b)
        _ -> panic $ unwords ["importExpr: invalid record selector", show i, show t]

-- | Apply a substitution to a type *without* simplifying
-- constraints like @Arith [n]a@ to @Arith a@. (This is in contrast to
-- 'apSubst', which performs simplifications wherever possible.)
plainSubst :: C.Subst -> C.Type -> C.Type
plainSubst s ty =
  case ty of
    C.TCon tc ts   -> C.TCon tc (map (plainSubst s) ts)
    C.TUser f ts t -> C.TUser f (map (plainSubst s) ts) (plainSubst s t)
    C.TRec fs      -> C.TRec [ (x, plainSubst s t) | (x, t) <- fs ]
    C.TVar x       -> C.apSubst s (C.TVar x)

-- | Currently this imports declaration groups by inlining all the
-- definitions. (With subterm sharing, this is not as bad as it might
-- seem.) We might want to think about generating let or where
-- expressions instead.
importDeclGroup :: Bool -> SharedContext -> Env -> C.DeclGroup -> IO Env

importDeclGroup isTopLevel sc env (C.Recursive [decl]) =
  case C.dDefinition decl of
    C.DPrim ->
      panic $ unwords ["Primitive declarations cannot be recursive:", show (C.dName decl)]
    C.DExpr expr ->
      do env1 <- bindName sc (C.dName decl) (C.dSignature decl) env
         t' <- importSchema sc env (C.dSignature decl)
         e' <- importExpr' sc env1 (C.dSignature decl) expr
         let x = nameToString (C.dName decl)
         f' <- scLambda sc x t' e'
         rhs <- scGlobalApply sc "Prelude.fix" [t', f']
         rhs' <- if not isTopLevel then return rhs else scConstant sc x rhs t'
         let env' = env { envE = Map.insert (C.dName decl) (rhs', 0) (envE env)
                        , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
         return env'


-- - A group of mutually-recursive declarations -
-- We handle this by "tupling up" all the declarations using a record and
-- taking the fixpoint at this record type.  The desired declarations are then
-- achieved by projecting the field names from this record.
importDeclGroup isTopLevel sc env (C.Recursive decls) =
  do -- build the environment for the declaration bodies
     let dm = Map.fromList [ (C.dName d, d) | d <- decls ]

     -- grab a reference to the outermost variable; this will be the record in the body
     -- of the lambda we build later
     v0 <- scLocalVar sc 0

     -- build a list of projections from a record variable
     vm <- traverse (scRecordSelect sc v0 . nameToString . C.dName) dm

     -- the types of the declarations
     tm <- traverse (importSchema sc env . C.dSignature) dm
     -- the type of the recursive record
     rect <- scRecordType sc (Map.assocs $ Map.mapKeys nameToString tm)

     let env1 = liftEnv env
     let env2 = env1 { envE = Map.union (fmap (\v -> (v, 0)) vm) (envE env1)
                     , envC = Map.union (fmap C.dSignature dm) (envC env1)
                     , envS = rect : envS env1 }

     let extractDeclExpr decl =
           case C.dDefinition decl of
             C.DExpr expr -> importExpr' sc env2 (C.dSignature decl) expr
             C.DPrim ->
                panic $ unwords [ "Primitive declarations cannot be recursive:"
                                , show (C.dName decl)]

     -- the raw imported bodies of the declarations
     em <- traverse extractDeclExpr dm

     -- the body of the recursive record
     recv <- scRecord sc (Map.mapKeys nameToString em)

     -- build a lambda from the record body...
     f <- scLambda sc "fixRecord" rect recv

     -- and take its fixpoint
     rhs <- scGlobalApply sc "Prelude.fix" [rect, f]

     -- finally, build projections from the fixed record to shove into the environment
     -- if toplevel, then wrap each binding with a Constant constructor
     let mkRhs d t =
           do let s = nameToString (C.dName d)
              r <- scRecordSelect sc rhs s
              if isTopLevel then scConstant sc s r t else return r
     rhss <- sequence (Map.intersectionWith mkRhs dm tm)

     let env' = env { envE = Map.union (fmap (\v -> (v, 0)) rhss) (envE env)
                    , envC = Map.union (fmap C.dSignature dm) (envC env)
                    }
     return env'

importDeclGroup isTopLevel sc env (C.NonRecursive decl) =
  case C.dDefinition decl of
    C.DPrim
     | isTopLevel -> do
        rhs <- importPrimitive sc (C.dName decl)
        let env' = env { envE = Map.insert (C.dName decl) (rhs, 0) (envE env)
                      , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
        return env'
     | otherwise -> do
        panic $ unwords ["Primitive declarations only allowed at top-level:", show (C.dName decl)]

    C.DExpr expr -> do
     rhs <- importExpr' sc env (C.dSignature decl) expr
     rhs' <- if not isTopLevel then return rhs else do
       t <- importSchema sc env (C.dSignature decl)
       scConstant sc (nameToString (C.dName decl)) rhs t
     let env' = env { envE = Map.insert (C.dName decl) (rhs', 0) (envE env)
                    , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
     return env'

importDeclGroups :: SharedContext -> Env -> [C.DeclGroup] -> IO Env
importDeclGroups sc = foldM (importDeclGroup False sc)

importTopLevelDeclGroups :: SharedContext -> Env -> [C.DeclGroup] -> IO Env
importTopLevelDeclGroups sc = foldM (importDeclGroup True sc)

coerceTerm :: SharedContext -> Env -> C.Type -> C.Type -> Term -> IO Term
coerceTerm sc env t1 t2 e
  | t1 == t2 = do return e
  | otherwise =
    do t1' <- importType sc env t1
       t2' <- importType sc env t2
       q <- proveEq sc env t1 t2
       scGlobalApply sc "Prelude.coerce" [t1', t2', q, e]

proveEq :: SharedContext -> Env -> C.Type -> C.Type -> IO Term
proveEq sc env t1 t2
  | t1 == t2 =
    do s <- scSort sc (mkSort 0)
       t' <- importType sc env t1
       scCtorApp sc "Prelude.Refl" [s, t']
  | otherwise =
    case (C.tNoUser t1, C.tNoUser t2) of
      (C.tIsSeq -> Just (n1, a1), C.tIsSeq -> Just (n2, a2)) ->
        do n1' <- importType sc env n1
           n2' <- importType sc env n2
           a1' <- importType sc env a1
           a2' <- importType sc env a2
           num <- scDataTypeApp sc "Cryptol.Num" []
           nEq <- if n1 == n2
                  then scGlobalApply sc "Prelude.Refl" [num, n1']
                  else scGlobalApply sc "Prelude.unsafeAssert" [num, n1', n2']
           aEq <- proveEq sc env a1 a2
           if a1 == a2
             then scGlobalApply sc "Cryptol.seqEq1" [n1', n2', a1', nEq]
             else scGlobalApply sc "Cryptol.seqEq" [n1', n2', a1', a2', nEq, aEq]
      (C.tIsFun -> Just (a1, b1), C.tIsFun -> Just (a2, b2)) ->
        do a1' <- importType sc env a1
           a2' <- importType sc env a2
           b1' <- importType sc env b1
           b2' <- importType sc env b2
           aEq <- proveEq sc env a1 a2
           bEq <- proveEq sc env b1 b2
           scGlobalApply sc "Cryptol.funEq" [a1', a2', b1', b2', aEq, bEq]
      (C.tIsTuple -> Just (a1 : ts1), C.tIsTuple -> Just (a2 : ts2))
        | length ts1 == length ts2 ->
          do let b1 = C.tTuple ts1
                 b2 = C.tTuple ts2
             a1' <- importType sc env a1
             a2' <- importType sc env a2
             b1' <- importType sc env b1
             b2' <- importType sc env b2
             aEq <- proveEq sc env a1 a2
             bEq <- proveEq sc env b1 b2
             if b1 == b2
               then scGlobalApply sc "Cryptol.pairEq1" [a1', a2', b1', aEq]
               else if a1 == a2
                    then scGlobalApply sc "Cryptol.pairEq2" [a1', b1', b2', bEq]
                    else scGlobalApply sc "Cryptol.pairEq" [a1', a2', b1', b2', aEq, bEq]
      (C.tIsRec -> Just ts1, C.tIsRec -> Just ts2)
        | map fst ts1 == map fst ts2 ->
          do panic $ unwords ["unimplemented type coercion:", pretty t1, pretty t2]
      (_, _) ->
        panic $ unwords ["Internal type error:", pretty t1, pretty t2]

--------------------------------------------------------------------------------
-- List comprehensions

importComp :: SharedContext -> Env -> C.Type -> C.Type -> C.Expr -> [[C.Match]] -> IO Term
importComp sc env lenT elemT expr mss =
  do let zipAll [] = panic "zero-branch list comprehension"
         zipAll [branch] =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              return (xs, m, a, [args], len)
         zipAll (branch : branches) =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              (ys, n, b, argss, len') <- zipAll branches
              zs <- scGlobalApply sc "Cryptol.seqZip" [a, b, m, n, xs, ys]
              mn <- scGlobalApply sc "Cryptol.tcMin" [m, n]
              ab <- scTupleType sc [a, b]
              return (zs, mn, ab, args : argss, C.tMin len len')
     (xs, n, a, argss, lenT') <- zipAll mss
     f <- lambdaTuples sc env elemT expr argss
     b <- importType sc env elemT
     ys <- scGlobalApply sc "Cryptol.seqMap" [a, b, n, f, xs]
     -- The resulting type might not match the annotation, so we coerce
     coerceTerm sc env (C.tSeq lenT' elemT) (C.tSeq lenT elemT) ys

lambdaTuples :: SharedContext -> Env -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> IO Term
lambdaTuples sc env _ty expr [] = importExpr sc env expr
lambdaTuples sc env ty expr (args : argss) =
  do f <- lambdaTuple sc env ty expr argss args
     if null args || null argss
       then return f
       else do a <- importType sc env (tNestedTuple (map snd args))
               b <- importType sc env (tNestedTuple (map (tNestedTuple . map snd) argss))
               c <- importType sc env ty
               scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

lambdaTuple :: SharedContext -> Env -> C.Type -> C.Expr -> [[(C.Name, C.Type)]] -> [(C.Name, C.Type)] -> IO Term
lambdaTuple sc env ty expr argss [] = lambdaTuples sc env ty expr argss
lambdaTuple sc env ty expr argss ((x, t) : args) =
  do a <- importType sc env t
     env' <- bindName sc x (C.Forall [] [] t) env
     e <- lambdaTuple sc env' ty expr argss args
     f <- scLambda sc (nameToString x) a e
     if null args
        then return f
        else do b <- importType sc env (tNestedTuple (map snd args))
                let tuple = tNestedTuple (map (tNestedTuple . map snd) argss)
                c <- importType sc env (if null argss then ty else C.tFun tuple ty)
                scGlobalApply sc "Prelude.uncurry" [a, b, c, f]

tNestedTuple :: [C.Type] -> C.Type
tNestedTuple [] = C.tTuple []
tNestedTuple [t] = t
tNestedTuple (t : ts) = C.tTuple [t, tNestedTuple ts]


-- | Returns the shared term, length type, element tuple type, bound
-- variables.
importMatches :: SharedContext -> Env -> [C.Match]
              -> IO (Term, C.Type, C.Type, [(C.Name, C.Type)])
importMatches _sc _env [] = fail "importMatches: empty comprehension branch"

importMatches sc env [C.From name _len _eltty expr] = do
  (len, ty) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                 Just x -> return x
                 Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  xs <- importExpr sc env expr
  return (xs, len, ty, [(name, ty)])

importMatches sc env (C.From name _len _eltty expr : matches) = do
  (len1, ty1) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                   Just x -> return x
                   Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  m <- importType sc env len1
  a <- importType sc env ty1
  xs <- importExpr sc env expr
  env' <- bindName sc name (C.Forall [] [] ty1) env
  (body, len2, ty2, args) <- importMatches sc env' matches
  n <- importType sc env len2
  b <- importType sc env ty2
  f <- scLambda sc (nameToString name) a body
  result <- scGlobalApply sc "Cryptol.from" [a, b, m, n, xs, f]
  return (result, C.tMul len1 len2, C.tTuple [ty1, ty2], (name, ty1) : args)

importMatches sc env [C.Let decl]
  | C.DPrim <- C.dDefinition decl = do
     fail $ unwords ["Primitive declarations not allowed in 'let':", show (C.dName decl)]
  | C.DExpr expr <- C.dDefinition decl = do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType sc env ty1
     result <- scGlobalApply sc "Prelude.single" [a, e]
     return (result, C.tOne, ty1, [(C.dName decl, ty1)])

importMatches sc env (C.Let decl : matches) =
  case C.dDefinition decl of
    C.DPrim -> do
     fail $ unwords ["Primitive declarations not allowed in 'let':", show (C.dName decl)]
    C.DExpr expr -> do
     e <- importExpr sc env expr
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType sc env ty1
     env' <- bindName sc (C.dName decl) (C.dSignature decl) env
     (body, len, ty2, args) <- importMatches sc env' matches
     n <- importType sc env len
     b <- importType sc env ty2
     f <- scLambda sc (nameToString (C.dName decl)) a body
     result <- scGlobalApply sc "Cryptol.mlet" [a, b, n, e, f]
     return (result, len, C.tTuple [ty1, ty2], (C.dName decl, ty1) : args)

pIsNeq :: C.Type -> Maybe (C.Type, C.Type)
pIsNeq ty = case C.tNoUser ty of
              C.TCon (C.PC C.PNeq) [t1, t2] -> Just (t1, t2)
              _                             -> Nothing

--------------------------------------------------------------------------------
-- Utilities

asCryptolTypeValue :: SC.CValue -> Maybe C.Type
asCryptolTypeValue v =
  case v of
    SC.VBoolType -> return C.tBit
    SC.VIntType -> return C.tInteger
    SC.VVecType (SC.VNat n) v2 -> do
      t2 <- asCryptolTypeValue v2
      return (C.tSeq (C.tNum n) t2)
    SC.VDataType "Prelude.Stream" [v1] -> do
      t1 <- asCryptolTypeValue v1
      return (C.tSeq C.tInf t1)
    (SC.asVTupleType -> Just tps) ->
      C.tTuple <$> mapM asCryptolTypeValue tps
    SC.VRecordType elems ->
      do elems' <- mapM (\(f,tp) ->
                          let f_id = C.packIdent f in
                          (f_id,) <$> asCryptolTypeValue tp) elems
         return (C.tRec elems')
    SC.VUnitType -> return (C.tTuple [])
    SC.VPairType v1 v2 -> do
      t1 <- asCryptolTypeValue v1
      ts <- asCryptolTypeValue v2 >>= C.tIsTuple
      return (C.tTuple (t1 : ts))
    SC.VEmptyType -> return (C.tRec [])
    SC.VFieldType k v1 v2 -> do
      let name = C.packIdent k
      t1 <- asCryptolTypeValue v1
      fs <- asCryptolTypeValue v2 >>= C.tIsRec
      return (C.tRec ((name, t1) : fs))
    SC.VPiType v1 f -> do
      case v1 of
        -- if we see that the parameter is a Cryptol.Num, it's a
        -- pretty good guess that it originally was a
        -- polimorphic number type.
        SC.VDataType "Cryptol.Num" [] ->
          let msg= unwords ["asCryptolTypeValue: can't infer a polymorphic Cryptol"
                           ,"type. Please, make sure all numeric types are"
                           ,"specialized before constructing a typed term."
                           ]
          in error msg
            -- otherwise we issue a generic error about dependent type inference
        _ -> do
          let msg = unwords ["asCryptolTypeValue: can't infer a Cryptol type"
                            ,"for a dependent SAW-Core type."
                            ]
          let v2 = SC.runIdentity (f (error msg))
          t1 <- asCryptolTypeValue v1
          t2 <- asCryptolTypeValue v2
          return (C.tFun t1 t2)
    _ -> Nothing

scCryptolType :: SharedContext -> Term -> IO C.Type
scCryptolType sc t =
  scGetModuleMap sc >>= \modmap ->
  case asCryptolTypeValue (SC.evalSharedTerm modmap Map.empty t) of
    Just ty -> return ty
    Nothing -> fail $ "scCryptolType: unsupported type " ++ showTerm t

scCryptolEq :: SharedContext -> Term -> Term -> IO Term
scCryptolEq sc x y = do
  rules <- concat <$> traverse defRewrites (defs1 ++ defs2)
  let ss = addConvs natConversions (addRules rules emptySimpset)
  tx <- scTypeOf sc x >>= rewriteSharedTerm sc ss >>= scCryptolType sc
  ty <- scTypeOf sc y >>= rewriteSharedTerm sc ss >>= scCryptolType sc
  unless (tx == ty) $ fail $ unwords [ "scCryptolEq: type mismatch between"
                                     , pretty tx
                                     , "and"
                                     , pretty ty
                                     ]

  -- Actually apply the equality function, along with the bogus "proof" ePCmp
  t <- scTypeOf sc x
  c <- scCryptolType sc t
  k <- importType sc emptyEnv c
  cmpPrf <- scGlobalApply sc "Cryptol.ePCmp" [k]
  scGlobalApply sc "Cryptol.ecEq" [k, cmpPrf, x, y]

  where
    defs1 = map (mkIdent (mkModuleName ["Prelude"])) ["bitvector"]
    defs2 = map (mkIdent (mkModuleName ["Cryptol"])) ["seq", "ty"]
    defRewrites ident =
      do maybe_def <- scFindDef sc ident
         case maybe_def of
           Nothing -> return []
           Just def -> scDefRewriteRules sc def

-- | Convert from SAWCore's Value type to Cryptol's, guided by the
-- Cryptol type schema.
exportValueWithSchema :: C.Schema -> SC.CValue -> V.Value
exportValueWithSchema (C.Forall [] [] ty) v = exportValue (evalValType Map.empty ty) v
exportValueWithSchema _ _ = V.VPoly (error "exportValueWithSchema")
-- TODO: proper support for polymorphic values

exportValue :: TV.TValue -> SC.CValue -> V.Value
exportValue ty v = case ty of

  TV.TVBit ->
    V.VBit (SC.toBool v)

  TV.TVInteger ->
    V.VInteger (case v of SC.VInt x -> x; _ -> error "exportValue: expected integer")

  TV.TVSeq _ e ->
    case v of
      SC.VWord w -> V.word (toInteger (width w)) (unsigned w)
      SC.VVector xs
        | TV.isTBit e -> V.VWord (toInteger (Vector.length xs)) (V.ready (V.LargeBitsVal (fromIntegral (Vector.length xs))
                            (V.finiteSeqMap . map (V.ready . V.VBit . SC.toBool . SC.runIdentity . force) $ Fold.toList xs)))
        | otherwise   -> V.VSeq (toInteger (Vector.length xs)) $ V.finiteSeqMap $
                            map (V.ready . exportValue e . SC.runIdentity . force) $ Vector.toList xs
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- infinite streams
  TV.TVStream e ->
    case v of
      SC.VExtra (SC.CStream trie) -> V.VStream (V.IndexSeqMap $ \i -> V.ready $ exportValue e (IntTrie.apply trie i))
      _ -> error $ "exportValue (on seq type " ++ show ty ++ ")"

  -- tuples
  TV.TVTuple etys -> V.VTuple (exportTupleValue etys v)

  -- records
  TV.TVRec fields ->
      V.VRecord (exportRecordValue (Map.assocs (Map.fromList fields)) v)

  -- functions
  TV.TVFun _aty _bty ->
    V.VFun (error "exportValue: TODO functions")

  TV.TVIntMod _n ->
    V.VInteger (case v of SC.VInt x -> x; _ -> error "exportValue: expected integer")

exportTupleValue :: [TV.TValue] -> SC.CValue -> [V.Eval V.Value]
exportTupleValue tys v =
  case (tys, v) of
    ([]    , SC.VUnit    ) -> []
    (t : ts, SC.VPair x y) -> (V.ready $ exportValue t (run x)) : exportTupleValue ts (run y)
    (_     , SC.asVTuple -> Just xs) ->
      zipWith (\t x -> V.ready $ exportValue t (run x)) tys xs
    _                      -> error $ "exportValue: expected tuple"
  where
    run = SC.runIdentity . force

exportRecordValue :: [(C.Ident, TV.TValue)] -> SC.CValue -> [(C.Ident, V.Eval V.Value)]
exportRecordValue fields v =
  case (fields, v) of
    ([]         , SC.VEmpty      ) -> []
    ((n, t) : ts, SC.VField _ x y) ->
      (n, V.ready $ exportValue t (run x)) : exportRecordValue ts y
    (_, SC.VRecordValue (alistAllFields
                         (map (C.unpackIdent . fst) fields) -> Just ths)) ->
      zipWith (\(n,t) x -> (n, V.ready $ exportValue t (run x))) fields ths
    _                              -> error $ "exportValue: expected record"
  where
    run = SC.runIdentity . force

fvAsBool :: FirstOrderValue -> Bool
fvAsBool (FOVBit b) = b
fvAsBool _ = error "fvAsBool: expected FOVBit value"

exportFirstOrderValue :: FirstOrderValue -> V.Value
exportFirstOrderValue fv =
  case fv of
    FOVBit b    -> V.VBit b
    FOVInt i    -> V.VInteger i
    FOVWord w x -> V.word (toInteger w) x
    FOVVec t vs
      | t == FOTBit -> V.VWord len (V.ready (V.LargeBitsVal len (V.finiteSeqMap . map (V.ready . V.VBit . fvAsBool) $ vs)))
      | otherwise   -> V.VSeq  len (V.finiteSeqMap (map (V.ready . exportFirstOrderValue) vs))
      where len = toInteger (length vs)
    FOVTuple vs -> V.VTuple (map (V.ready . exportFirstOrderValue) vs)
    FOVRec vm   -> V.VRecord [ (C.packIdent n, V.ready $ exportFirstOrderValue v) | (n, v) <- Map.assocs vm ]

importFirstOrderValue :: FirstOrderType -> V.Value -> IO FirstOrderValue
importFirstOrderValue t0 v0 = V.runEval (V.EvalOpts C.quietLogger V.defaultPPOpts) (go t0 v0)
  where
  go :: FirstOrderType -> V.Value -> V.Eval FirstOrderValue
  go t v = case (t,v) of
    (FOTBit         , V.VBit b)        -> return (FOVBit b)
    (FOTInt         , V.VInteger i)    -> return (FOVInt i)
    (FOTVec _ FOTBit, V.VWord w wv)    -> FOVWord (fromIntegral w) . V.bvVal <$> (V.asWordVal =<< wv)
    (FOTVec _ ty    , V.VSeq len xs)   -> FOVVec ty <$> traverse (go ty =<<) (V.enumerateSeqMap len xs)
    (FOTTuple tys   , V.VTuple xs)     -> FOVTuple <$> traverse (\(ty, x) -> go ty =<< x) (zip tys xs)
    (FOTRec fs      , V.VRecord xs)    ->
        do xs' <- Map.fromList <$> mapM importField xs
           let missing = Set.difference (Map.keysSet fs) (Map.keysSet xs')
           unless (Set.null missing)
                  (fail $ unwords $ ["Missing fields while importing finite value:"] ++ Set.toList missing)
           return $ FOVRec $ xs'
      where
       importField :: (C.Ident, V.Eval V.Value) -> V.Eval (String, FirstOrderValue)
       importField (C.unpackIdent -> nm,x)
         | Just ty <- Map.lookup nm fs = do
                x' <- go ty =<< x
                return (nm, x')
         | otherwise = fail $ unwords ["Unexpected field name while importing finite value:", show nm]

    _ -> fail $ unwords ["Expected finite value of type:", show t, "but got", show v]
