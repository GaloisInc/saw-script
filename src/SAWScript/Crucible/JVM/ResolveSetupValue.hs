{- |
Module      : SAWScript.Crucible.JVM.ResolveSetupValue
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.Crucible.JVM.ResolveSetupValue
  ( JVMVal(..)
  , JVMRefVal
  , resolveSetupVal
  -- , typeOfJVMVal
  , typeOfSetupValue
  , resolveTypedTerm
  , resolveBoolTerm
  , resolveSAWPred
  -- , resolveSetupFieldIndex
  , equalValsPred
  ) where

import           Control.Lens
import qualified Control.Monad.Fail as Fail
import           Data.IORef
import qualified Data.BitVector.Sized as BV
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Void (absurd)

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.ProgramLoc as W4

import qualified Lang.Crucible.Backend.SAWCore as Crucible

import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

-- crucible
import qualified Lang.Crucible.Simulator as Crucible (RegValue)

-- what4
import qualified What4.Partial as W4

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- sbv
import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord, toBool)
import qualified Data.SBV.Dynamic as SBV (svAsInteger, svAsBool)

-- jvm-parser
import qualified Language.JVM.Parser as J

import SAWScript.Crucible.Common (Sym)
import SAWScript.Crucible.Common.MethodSpec (AllocIndex(..))

--import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Prover.Rewrite
import SAWScript.Crucible.JVM.MethodSpecIR
import qualified SAWScript.Crucible.Common.MethodSpec as MS

--import qualified SAWScript.LLVMBuiltins as LB

data JVMVal
  = RVal (Crucible.RegValue Sym CJ.JVMRefType)
  | IVal (Crucible.RegValue Sym CJ.JVMIntType)
  | LVal (Crucible.RegValue Sym CJ.JVMLongType)

instance Show JVMVal where
  show (RVal _) = "RVal"
  show (IVal _) = "IVal"
  show (LVal _) = "LVal"

type JVMRefVal = Crucible.RegValue Sym CJ.JVMRefType

type SetupValue = MS.SetupValue CJ.JVM

typeOfSetupValue ::
  Fail.MonadFail m =>
  JVMCrucibleContext ->
  Map AllocIndex (W4.ProgramLoc, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  m J.Type
typeOfSetupValue _cc env _nameEnv val =
  case val of
    MS.SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("typeOfSetupValue: Unresolved prestate variable:" ++ show i)
        Just (_, alloc) -> return (allocationType alloc)
    MS.SetupTerm tt ->
      case ttSchema tt of
        Cryptol.Forall [] [] ty ->
          case toJVMType (Cryptol.evalValType mempty ty) of
            Nothing -> fail "typeOfSetupValue: non-representable type"
            Just jty -> return jty
        s -> fail $ unlines [ "typeOfSetupValue: expected monomorphic term"
                            , "instead got:"
                            , show (Cryptol.pp s)
                            ]
    MS.SetupNull () ->
      -- We arbitrarily set the type of NULL to java.lang.Object,
      -- because a) it is memory-compatible with any type that NULL
      -- can be used at, and b) it prevents us from doing any
      -- type-safe field accesses.
      return (J.ClassType (J.mkClassName "java/lang/Object"))
    MS.SetupGlobal () name ->
      fail ("typeOfSetupValue: unimplemented jvm_global: " ++ name)
    MS.SetupStruct empty _ _          -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty

-- | Translate a SetupValue into a Crucible JVM value, resolving
-- references
resolveSetupVal ::
  JVMCrucibleContext ->
  Map AllocIndex JVMRefVal ->
  Map AllocIndex (W4.ProgramLoc, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  IO JVMVal
resolveSetupVal cc env _tyenv _nameEnv val =
  case val of
    MS.SetupVar i
      | Just v <- Map.lookup i env -> return (RVal v)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    MS.SetupTerm tm -> resolveTypedTerm cc tm
    MS.SetupNull () ->
      return (RVal (W4.maybePartExpr sym Nothing))
    MS.SetupGlobal () name ->
      fail $ "resolveSetupVal: unimplemented jvm_global: " ++ name
    MS.SetupStruct empty _ _          -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
  where
    sym = cc^.jccBackend

resolveTypedTerm ::
  JVMCrucibleContext ->
  TypedTerm       ->
  IO JVMVal
resolveTypedTerm cc tm =
  case ttSchema tm of
    Cryptol.Forall [] [] ty ->
      resolveSAWTerm cc (Cryptol.evalValType mempty ty) (ttTerm tm)
    _ -> fail "resolveSetupVal: expected monomorphic term"

resolveSAWPred ::
  JVMCrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm =
  Crucible.bindSAWTerm (cc^.jccBackend) W4.BaseBoolRepr tm

resolveSAWTerm ::
  JVMCrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO JVMVal
resolveSAWTerm cc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym tm
         x0 <- W4.bvLit sym W4.knownNat (BV.zero W4.knownNat)
         x1 <- W4.bvLit sym W4.knownNat (BV.one  W4.knownNat)
         x <- W4.bvIte sym b x1 x0
         return (IVal x)
    Cryptol.TVInteger ->
      fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
    Cryptol.TVIntMod _ ->
      fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
    Cryptol.TVFloat{} ->
      fail "resolveSAWTerm: unimplemented type Float e p (FIXME)"
    Cryptol.TVArray{} ->
      fail "resolveSAWTerm: unimplemented type Array a b (FIXME)"
    Cryptol.TVRational ->
      fail "resolveSAWTerm: unimplemented type Rational (FIXME)"
    Cryptol.TVSeq sz Cryptol.TVBit ->
      case sz of
        8  -> fail "resolveSAWTerm: unimplemented type char (FIXME)"
        16 -> fail "resolveSAWTerm: unimplemented type short (FIXME)"
        32 -> IVal <$> resolveBitvectorTerm sym W4.knownNat tm
        64 -> LVal <$> resolveBitvectorTerm sym W4.knownNat tm
        _  -> fail ("Invalid bitvector width: " ++ show sz)
    Cryptol.TVSeq _sz _tp' ->
      fail "resolveSAWTerm: unimplemented sequence type"
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: unsupported infinite stream type"
    Cryptol.TVTuple _tps ->
      fail "resolveSAWTerm: unsupported tuple type"
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unsupported record type"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: unsupported function type"
    Cryptol.TVAbstract _ _ ->
      fail "resolveSAWTerm: unsupported abstract type"
  where
    sym = cc^.jccBackend

-- TODO: Instead of evaluating in SBV backend, just evaluate in W4 backend directly.
resolveBitvectorTerm ::
  forall w.
  (1 W4.<= w) =>
  Sym ->
  W4.NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveBitvectorTerm sym w tm =
  do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
     --ss <- basic_ss sc
     --tm' <- rewriteSharedTerm sc ss tm
     let tm' = tm
     mx <- case getAllExts tm' of
             [] ->
               do -- Evaluate in SBV to test whether 'tm' is a concrete value
                  modmap <- scGetModuleMap sc
                  sbv <- SBV.toWord =<< SBV.sbvSolveBasic modmap Map.empty [] tm'
                  return (SBV.svAsInteger sbv)
             _ -> return Nothing
     case mx of
       Just x  -> W4.bvLit sym w (BV.mkBV w x)
       Nothing -> Crucible.bindSAWTerm sym (W4.BaseBVRepr w) tm'

-- TODO: Instead of evaluating in SBV backend, just evaluate in W4 backend directly.
resolveBoolTerm :: Sym -> Term -> IO (W4.Pred Sym)
resolveBoolTerm sym tm =
  do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
     ss <- basic_ss sc
     tm' <- rewriteSharedTerm sc ss tm
     mx <- case getAllExts tm' of
             [] ->
               do -- Evaluate in SBV to test whether 'tm' is a concrete value
                  modmap <- scGetModuleMap sc
                  sbv <- SBV.toBool <$> SBV.sbvSolveBasic modmap Map.empty [] tm'
                  return (SBV.svAsBool sbv)
             _ -> return Nothing
     case mx of
       Just x  -> return (W4.backendPred sym x)
       Nothing -> Crucible.bindSAWTerm sym W4.BaseBoolRepr tm'

toJVMType :: Cryptol.TValue -> Maybe J.Type
toJVMType tp =
  case tp of
    Cryptol.TVBit -> Just J.BooleanType
    Cryptol.TVInteger -> Nothing
    Cryptol.TVIntMod _ -> Nothing
    Cryptol.TVFloat{} -> Nothing
    Cryptol.TVArray{} -> Nothing
    Cryptol.TVRational -> Nothing
    Cryptol.TVSeq n Cryptol.TVBit ->
      case n of
        8  -> Just J.CharType
        16 -> Just J.ShortType
        32 -> Just J.IntType
        64 -> Just J.LongType
        _  -> Nothing
    Cryptol.TVSeq _n t ->
      do t' <- toJVMType t
         Just (J.ArrayType t')
    Cryptol.TVStream _tp' -> Nothing
    Cryptol.TVTuple _tps -> Nothing
    Cryptol.TVRec _flds -> Nothing
    Cryptol.TVFun _ _ -> Nothing
    Cryptol.TVAbstract _ _ -> Nothing

equalValsPred ::
  JVMCrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 = go (v1, v2)
  where
  go :: (JVMVal, JVMVal) -> IO (W4.Pred Sym)
  go (RVal r1, RVal r2) = CJ.refIsEqual sym r1 r2
  go (IVal i1, IVal i2) = W4.bvEq sym i1 i2
  go (LVal l1, LVal l2) = W4.bvEq sym l1 l2
  go _ = return (W4.falsePred sym)

  sym = cc^.jccBackend
