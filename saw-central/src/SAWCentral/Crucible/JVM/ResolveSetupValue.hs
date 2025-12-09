{- |
Module      : SAWCentral.Crucible.JVM.ResolveSetupValue
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module SAWCentral.Crucible.JVM.ResolveSetupValue
  ( JVMVal(..)
  , JVMRefVal
  , resolveSetupVal
  -- , typeOfJVMVal
  , typeOfSetupValue
  , lookupAllocIndex
  , toJVMType
  , resolveTypedTerm
  , resolveBoolTerm
  , resolveSAWPred
  -- , resolveSetupFieldIndex
  , equalValsPred
  , JVMTypeOfError(..)
  ) where

import           Control.Lens
import qualified Control.Monad.Catch as X
import qualified Data.BitVector.Sized as BV
import qualified Data.Text as Text
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Void (absurd)

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Type, Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4

import SAWCore.SharedTerm
import CryptolSAWCore.TypedTerm

-- crucible

import qualified Lang.Crucible.Simulator as Crucible (RegValue)

-- what4
import qualified What4.Partial as W4

-- crucible-jvm
import qualified Lang.Crucible.JVM as CJ

-- jvm-parser
import qualified Language.JVM.Parser as J

import SAWCentral.Crucible.Common
import SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..))

import SAWCentral.Panic
import SAWCentral.Crucible.JVM.MethodSpecIR
import SAWCentral.Crucible.JVM.Setup.Value (JVMRefVal, jccUninterp)
import qualified SAWCentral.Crucible.Common.MethodSpec as MS
import SAWCentral.Crucible.Common.ResolveSetupValue (resolveBoolTerm, resolveBitvectorTerm)


data JVMVal
  = RVal (Crucible.RegValue Sym CJ.JVMRefType)
  | IVal (Crucible.RegValue Sym CJ.JVMIntType)
  | LVal (Crucible.RegValue Sym CJ.JVMLongType)

instance Show JVMVal where
  show (RVal _) = "RVal"
  show (IVal _) = "IVal"
  show (LVal _) = "LVal"

type SetupValue = MS.SetupValue CJ.JVM

data JVMTypeOfError
  = JVMPolymorphicType Cryptol.Schema
  | JVMNonRepresentableType Cryptol.Type
  | JVMInvalidTypedTerm TypedTermType

instance Show JVMTypeOfError where
  show (JVMPolymorphicType s) =
    unlines
    [ "Expected monomorphic term"
    , "instead got:"
    , show (Cryptol.pp s)
    ]
  show (JVMNonRepresentableType ty) =
    unlines
    [ "Type not representable in JVM:"
    , show (Cryptol.pp ty)
    ]
  show (JVMInvalidTypedTerm tp) =
    unlines
    [ "Expected typed term with Cryptol representable type, but got"
    , show (prettyTypedTermTypePure tp)
    ]

instance X.Exception JVMTypeOfError

typeOfSetupValue ::
  X.MonadThrow m =>
  JVMCrucibleContext ->
  Map AllocIndex (MS.ConditionMetadata, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  m J.Type
typeOfSetupValue _cc env _nameEnv val =
  case val of
    MS.SetupVar i ->
      case Map.lookup i env of
        Nothing ->
            panic "JVMSetup (in typeOfSetupValue)" [
                "Unresolved prestate variable: " <> Text.pack (show i)
            ]
        Just (_, alloc) -> return (allocationType alloc)
    MS.SetupTerm tt ->
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toJVMType (Cryptol.evalValType mempty ty) of
            Nothing -> X.throwM (JVMNonRepresentableType ty)
            Just jty -> return jty
        TypedTermSchema s -> X.throwM (JVMPolymorphicType s)
        tp -> X.throwM (JVMInvalidTypedTerm tp)

    MS.SetupNull () ->
      -- We arbitrarily set the type of NULL to java.lang.Object,
      -- because a) it is memory-compatible with any type that NULL
      -- can be used at, and b) it prevents us from doing any
      -- type-safe field accesses.
      return (J.ClassType (J.mkClassName "java/lang/Object"))
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct empty _            -> absurd empty
    MS.SetupEnum empty                -> absurd empty
    MS.SetupTuple empty _             -> absurd empty
    MS.SetupSlice empty               -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
    MS.SetupMux empty _ _ _           -> absurd empty

lookupAllocIndex :: Map AllocIndex a -> AllocIndex -> a
lookupAllocIndex env i =
  case Map.lookup i env of
    Just x -> x
    Nothing ->
      panic "JVMSetup (in lookupAllocIndex" [
          "Unresolved prestate variable: " <> Text.pack (show i)
      ]

-- | Translate a SetupValue into a Crucible JVM value, resolving
-- references
resolveSetupVal ::
  JVMCrucibleContext ->
  Map AllocIndex JVMRefVal ->
  Map AllocIndex (MS.ConditionMetadata, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  IO JVMVal
resolveSetupVal cc env _tyenv _nameEnv val =
  case val of
    MS.SetupVar i ->
      pure (RVal (lookupAllocIndex env i))
    MS.SetupTerm tm -> resolveTypedTerm cc tm
    MS.SetupNull () ->
      return (RVal (W4.maybePartExpr sym Nothing))
    MS.SetupGlobal empty _            -> absurd empty
    MS.SetupStruct empty _            -> absurd empty
    MS.SetupEnum empty                -> absurd empty
    MS.SetupTuple empty _             -> absurd empty
    MS.SetupSlice empty               -> absurd empty
    MS.SetupArray empty _             -> absurd empty
    MS.SetupElem empty _ _            -> absurd empty
    MS.SetupField empty _ _           -> absurd empty
    MS.SetupCast empty _              -> absurd empty
    MS.SetupUnion empty _ _           -> absurd empty
    MS.SetupGlobalInitializer empty _ -> absurd empty
    MS.SetupMux empty _ _ _           -> absurd empty
  where
    sym = cc^.jccSym

resolveTypedTerm ::
  JVMCrucibleContext ->
  TypedTerm       ->
  IO JVMVal
resolveTypedTerm cc tm =
  case ttType tm of
    TypedTermSchema (Cryptol.Forall [] [] ty) ->
      resolveSAWTerm cc (Cryptol.evalValType mempty ty) (ttTerm tm)
    tp -> fail $ unlines
            [ "resolveSetupVal: expected monomorphic term"
            , "but got a term of type"
            , show (prettyTypedTermTypePure tp)
            ]

resolveSAWPred ::
  JVMCrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc = resolveBoolTerm (cc ^. jccSym) (cc ^. jccUninterp)

resolveSAWTerm ::
  JVMCrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO JVMVal
resolveSAWTerm cc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym (cc ^. jccUninterp) tm
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
      let unint = cc ^. jccUninterp in
      case sz of
        8  -> do x <- resolveBitvectorTerm sym unint (W4.knownNat @8) tm
                 IVal <$> W4.bvSext sym W4.knownNat x
        16 -> do x <- resolveBitvectorTerm sym unint (W4.knownNat @16) tm
                 IVal <$> W4.bvSext sym W4.knownNat x
        32 -> IVal <$> resolveBitvectorTerm sym unint W4.knownNat tm
        64 -> LVal <$> resolveBitvectorTerm sym unint W4.knownNat tm
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
    Cryptol.TVNominal {} ->
      fail "resolveSAWTerm: unsupported nominal type"
  where
    sym = cc^.jccSym

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
        8  -> Just J.ByteType
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
    Cryptol.TVNominal {} -> Nothing

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

  sym = cc^.jccSym
