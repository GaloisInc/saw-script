{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Move brackets to avoid $" #-}

module Verifier.SAW.Heapster.SAWTranslation where

import Prelude hiding (pi)

import Data.Maybe
import Numeric.Natural
import Data.List hiding (inits)
import Data.Text (pack)
import Data.Kind
import GHC.TypeLits
import Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import Data.Functor.Compose
import Control.Applicative
import Control.Lens hiding ((:>), Index, ix, op, getting)
import qualified Control.Monad as Monad
import Control.Monad.Reader hiding (ap)
import Control.Monad.Writer hiding (ap)
import Control.Monad.State hiding (ap)
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Fail as Fail

import What4.ProgramLoc
import What4.Interface (StringLiteral(..))

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits hiding (sym, trans)
import Data.Binding.Hobbits.Liftable ()

import Prettyprinter as PP
import Prettyprinter.Render.String

import Data.Parameterized.TraversableF

import Lang.Crucible.Types
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Core

import Verifier.SAW.Utils (panic)
import Verifier.SAW.Name
import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm

-- import Verifier.SAW.Heapster.GenMonad
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.PatternMatchUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.TypedCrucible
import Verifier.SAW.Heapster.NamedMb

import GHC.Stack


-- | FIXME: document and move to Hobbits
suffixMembers :: prx1 ctx1 -> RAssign prx2 ctx2 ->
                 RAssign (Member (ctx1 :++: ctx2)) ctx2
suffixMembers _ MNil = MNil
suffixMembers ctx1 (ctx2 :>: _) =
  RL.map Member_Step (suffixMembers ctx1 ctx2) :>: Member_Base

-- | Weaken a 'Member' proof by appending another context to the context it
-- proves membership in
weakenMemberR :: RAssign any ctx2 -> Member ctx1 a -> Member (ctx1 :++: ctx2) a
weakenMemberR MNil memb = memb
weakenMemberR (ctx1 :>: _) memb = Member_Step (weakenMemberR ctx1 memb)


----------------------------------------------------------------------
-- * Type Translations
----------------------------------------------------------------------

-- | Call 'prettyCallStack' and insert a newline in front
nlPrettyCallStack :: CallStack -> String
nlPrettyCallStack = ("\n" ++) . prettyCallStack

-- | A description of a type as either a "pure" type containg no corecursive
-- closure types (i.e., no @LRTClos@ types) or as an 'OpenTerm' of type
-- @LetRecType@ along with the SAW core type it decodes to as a 'SpecTerm'
data TypeDesc
  = TypeDescPure OpenTerm
  | TypeDescLRT OpenTerm SpecTerm

-- | Test if a 'TypeDesc' is pure
typeDescIsPure :: TypeDesc -> Bool
typeDescIsPure (TypeDescPure _) = True
typeDescIsPure (TypeDescLRT _ _) = False

-- | Get the type described by a 'TypeDesc'
typeDescType :: TypeDesc -> SpecTerm
typeDescType (TypeDescPure tp) = openTermLike tp
typeDescType (TypeDescLRT _ tp) = tp

-- | Get the pure type described by a 'TypeDesc', if there is one
typeDescPureType :: TypeDesc -> Maybe OpenTerm
typeDescPureType (TypeDescPure tp) = Just tp
typeDescPureType (TypeDescLRT _ _) = Nothing

-- | Get the @LetRecType@ that encodes the type of a 'TypeDesc'
typeDescLRT :: TypeDesc -> OpenTerm
typeDescLRT (TypeDescPure tp) = ctorOpenTerm "Prelude.LRT_Type" [tp]
typeDescLRT (TypeDescLRT lrt _) = lrt

-- | Return the pair of the @LetRecType@ of a 'TypeDesc' and the type it encodes
typeDescTypeLRT :: TypeDesc -> (OpenTerm,SpecTerm)
typeDescTypeLRT d = (typeDescLRT d, typeDescType d)

-- | Build an impure 'TypeDesc' from a term of type @LetRecType@
typeDescFromLRT :: OpenTerm -> TypeDesc
typeDescFromLRT lrt = TypeDescLRT lrt (lrtToTypeSpecTerm lrt)

-- | If all the type descriptions in a list are pure, return their pure types as
-- a list; otherwise, convert them all to impure LRT types
typeDescsPureOrLRT :: [TypeDesc] -> Either [OpenTerm] [(OpenTerm,SpecTerm)]
typeDescsPureOrLRT =
  foldr (\d descs -> case d of
            TypeDescPure tp | Left tps <- descs -> Left (tp:tps)
            _ | Right lrt_tps <- descs -> Right (typeDescTypeLRT d : lrt_tps)
            _ | Left tps <- descs ->
                Right (typeDescTypeLRT d :
                       map (typeDescTypeLRT . TypeDescPure) tps)) (Left [])

-- | Apply a binary type-forming operation to two type descriptions, using the
-- 'OpenTerm' function if the type descriptions are both pure and otherwise
-- using the supplied 'Ident' to combine @LetRecType@s and the 'SpecTerm'
-- function to combine impure types
typeDescBinOp :: (OpenTerm -> OpenTerm -> OpenTerm) -> Ident ->
                 (SpecTerm -> SpecTerm -> SpecTerm) ->
                 TypeDesc -> TypeDesc -> TypeDesc
typeDescBinOp f _ _ (TypeDescPure tp_l) (TypeDescPure tp_r) =
    TypeDescPure $ f tp_l tp_r
typeDescBinOp _ lrt_op f d_l d_r =
  TypeDescLRT
  (applyGlobalOpenTerm lrt_op [typeDescLRT d_l, typeDescLRT d_r])
  (f (typeDescType d_l) (typeDescType d_r))

-- | Build a type description for the type @BVVec w len a@
bvVecTypeDesc :: OpenTerm -> OpenTerm -> TypeDesc -> TypeDesc
bvVecTypeDesc w_term len_term (TypeDescPure elem_tp) =
  TypeDescPure (applyGlobalOpenTerm "Prelude.BVVec"
                [w_term, len_term, elem_tp])
bvVecTypeDesc w_term len_term (TypeDescLRT lrt elem_tp) =
  TypeDescLRT
  (applyGlobalOpenTerm "Prelude.LRT_BVVec" [w_term, len_term, lrt])
  (applyGlobalTermLike "Prelude.BVVec" [openTermLike w_term,
                                        openTermLike len_term, elem_tp])

-- | The 'TypeDesc' for the unit type
typeDescUnit :: TypeDesc
typeDescUnit = TypeDescPure unitTypeOpenTerm

-- | Build a type description for the pair of two type descriptions
typeDescPair :: TypeDesc -> TypeDesc -> TypeDesc
typeDescPair =
  typeDescBinOp pairTypeOpenTerm "Prelude.LRT_Pair" pairTypeTermLike

-- | Build a type description for the @Either@ of two type descriptions
typeDescEither :: TypeDesc -> TypeDesc -> TypeDesc
typeDescEither =
  typeDescBinOp
  (\tp1 tp2 -> dataTypeOpenTerm "Prelude.Either" [tp1,tp2])
  "Prelude.LRT_Either"
  (\tp1 tp2 -> dataTypeTermLike "Prelude.Either" [tp1,tp2])

-- | Build a type description for a @Sigma@ type from a pure type for the first
-- projection and a function to a type description for the second projection.
-- The Boolean flag indicates whether this function is expected to return a pure
-- type, in which case the returned dependent pair type is pure, or not, in
-- which case it isn't. It is an error if the Boolean flag is 'True' but the
-- function returns an impure type description.
typeDescSigma :: LocalName -> OpenTerm -> Bool -> (OpenTerm -> TypeDesc) ->
                 TypeDesc
typeDescSigma x tp_l True tp_r_f =
  let tp_f_trm =
        lambdaOpenTerm x tp_l $ \tr ->
        case tp_r_f tr of
          TypeDescPure tp_r -> tp_r
          TypeDescLRT _ _ ->
            panic "typeDescSigma"
            ["Expected a pure type description but got an impure one"] in
  TypeDescPure $ dataTypeOpenTerm "Prelude.Sigma" [tp_l, tp_f_trm]
typeDescSigma x tp_l False tp_r_f =
  TypeDescLRT
  (ctorOpenTerm "Prelude.LRT_Sigma"
   [tp_l, lambdaOpenTerm x tp_l (typeDescLRT . tp_r_f)])
  (dataTypeTermLike "Prelude.Sigma"
   [openTermLike tp_l,
    lambdaPureSpecTerm x (openTermLike tp_l) (typeDescType . tp_r_f)])

-- | Build the tuple type @T1 * (T2 * ... * (Tn-1 * Tn))@ of @n@ types, with the
-- special case that 0 types maps to the unit type @#()@ (and 1 type just maps
-- to itself). Note that this is different from 'tupleTypeOpenTerm', which
-- always ends with unit, i.e., which returns @T1*(T2*...*(Tn-1*(Tn*#())))@.
tupleOfTypes :: [OpenTerm] -> OpenTerm
tupleOfTypes [] = unitTypeOpenTerm
tupleOfTypes [tp] = tp
tupleOfTypes (tp:tps) = pairTypeOpenTerm tp $ tupleOfTypes tps

-- | Like 'tupleOfTypes' but applied to type descriptions
tupleOfTypeDescs :: [TypeDesc] -> TypeDesc
tupleOfTypeDescs [] = TypeDescPure unitTypeOpenTerm
tupleOfTypeDescs [tp] = tp
tupleOfTypeDescs (TypeDescPure tp_l : ds)
  | TypeDescPure tp_r <- tupleOfTypeDescs ds
  = TypeDescPure $ pairTypeOpenTerm tp_l tp_r
tupleOfTypeDescs (d : ds) =
  let d_r = tupleOfTypeDescs ds in
  TypeDescLRT
  (applyGlobalOpenTerm "Prelude.LRT_Pair" [typeDescLRT d, typeDescLRT d_r])
  (pairTypeTermLike (typeDescType d) (typeDescType d_r))

-- | Build the type description for the type @SpecM a@ for one of @a@
specMTypeDesc :: TypeDesc -> TypeDesc
specMTypeDesc d =
  TypeDescLRT (ctorOpenTerm "LRT_SpecM" [typeDescLRT d])
  (specMTypeSpecTerm $ typeDescType d)

-- | Build the tuple @(t1,(t2,(...,(tn-1,tn))))@ of @n@ terms, with the
-- special case that 0 types maps to the unit value @()@ (and 1 value just maps
-- to itself). Note that this is different from 'tupleOpenTerm', which
-- always ends with unit, i.e., which returns @t1*(t2*...*(tn-1*(tn*())))@.
tupleOfTerms :: OpenTermLike tm => [tm] -> tm
tupleOfTerms [] = unitTermLike
tupleOfTerms [t] = t
tupleOfTerms (t:ts) = pairTermLike t $ tupleOfTerms ts

-- | Project the @i@th element from a term of type @'tupleOfTypes' tps@. Note
-- that this requires knowing the length of @tps@.
projTupleOfTypes :: [OpenTerm] -> Integer -> OpenTerm -> OpenTerm
projTupleOfTypes [] _ _ =
  panic "projTupleOfTypes" ["projection of empty tuple!"]
projTupleOfTypes [_] 0 tup = tup
projTupleOfTypes (_:_) 0 tup = pairLeftOpenTerm tup
projTupleOfTypes (_:tps) i tup =
  projTupleOfTypes tps (i-1) $ pairRightOpenTerm tup

-- | Impure version of 'projTupleOfTypes'
projTupleOfTypesI :: [TypeDesc] -> Integer -> SpecTerm -> SpecTerm
projTupleOfTypesI [] _ _ =
  panic "projTupleOfTypesI" ["projection of empty tuple!"]
projTupleOfTypesI [_] 0 tup = tup
projTupleOfTypesI (_:_) 0 tup = pairLeftTermLike tup
projTupleOfTypesI (_:tps) i tup =
  projTupleOfTypesI tps (i-1) $ pairRightTermLike tup

-- | The result of translating a type-like construct such as a 'TypeRepr' or a
-- permission, parameterized by the (Haskell) type of the translations of the
-- elements of that type. This are translated to 0 or more type descriptions,
-- along with a (Haskell) function for mapping elements of the types they
-- describe to the corresponding translation construct in Haskell. Type
-- translations can either be pure, meaning they do not depend on the event type
-- and function stack of the current @SpecM@ computation and so are represented
-- with 'OpenTerm's, or impure, meaning they can depend on these objects and so
-- are represented with 'SpecTerm's. The @p@ type parameter is 'True' for pure
-- type translations and 'False' for impure ones.
data TypeTrans p tr where
  TypeTransPure :: [OpenTerm] -> ([OpenTerm] -> tr) -> TypeTrans 'True tr
  TypeTransImpure :: [TypeDesc] -> ([SpecTerm] -> tr) -> TypeTrans 'False tr

-- | A pure 'TypeTrans'
type PureTypeTrans = TypeTrans 'True

-- | An impure 'TypeTrans'
type ImpTypeTrans = TypeTrans 'False

-- | A term that is either pure, meaning it does not depend on the event type
-- and function stack of the current @SpecM@ computation and so is represented
-- as an 'OpenTerm', or impure, meaning they it depend on these objects and so
-- is represented as a 'SpecTerm'
type family PurityTerm p where
  PurityTerm 'True = OpenTerm
  PurityTerm 'False = SpecTerm

-- | Get the types in a 'TypeTrans'
typeTransTypes :: TypeTrans p tr -> [PurityTerm p]
typeTransTypes (TypeTransPure tps _) = tps
typeTransTypes (TypeTransImpure ds _) = map typeDescType ds

-- | Get the type descriptions of the types in a 'TypeTrans'
typeTransDescs :: TypeTrans p tr -> [TypeDesc]
typeTransDescs (TypeTransPure tps _) = map TypeDescPure tps
typeTransDescs (TypeTransImpure ds _) = ds

-- | Apply the function of a 'TypeTrans'
typeTransF :: HasCallStack => TypeTrans p tr -> [PurityTerm p] -> tr
typeTransF (TypeTransPure tps f) ts | length tps == length ts = f ts
typeTransF (TypeTransImpure tps f) ts | length tps == length ts = f ts
typeTransF tp_trans ts =
  error ("Type translation expected "
         ++ show (length $ typeTransTypes tp_trans) ++
         " arguments, but got " ++ show (length ts))

instance Functor (TypeTrans p) where
  fmap f (TypeTransPure ts tp_f) = TypeTransPure ts (f . tp_f)
  fmap f (TypeTransImpure ts tp_f) = TypeTransImpure ts (f . tp_f)

instance Applicative (TypeTrans 'True) where
  pure = mkPureTypeTrans0
  liftA2 f (TypeTransPure tps1 f1) (TypeTransPure tps2 f2) =
    TypeTransPure (tps1 ++ tps2)
    (\ts -> f (f1 $ take (length tps1) ts) (f2 $ drop (length tps1) ts))

instance Applicative (TypeTrans 'False) where
  pure = mkImpTypeTrans0
  liftA2 f (TypeTransImpure tps1 f1) (TypeTransImpure tps2 f2) =
    TypeTransImpure (tps1 ++ tps2)
    (\ts -> f (f1 $ take (length tps1) ts) (f2 $ drop (length tps1) ts))

-- | Build a pure 'TypeTrans' represented by 0 SAW types
mkPureTypeTrans0 :: tr -> TypeTrans 'True tr
mkPureTypeTrans0 tr = TypeTransPure [] $ \case
  [] -> tr
  _ -> panic "mkPureTypeTrans0" ["incorrect number of terms"]

-- | Build an impure 'TypeTrans' represented by 0 SAW types
mkImpTypeTrans0 :: tr -> TypeTrans 'False tr
mkImpTypeTrans0 tr = TypeTransImpure [] $ \case
  [] -> tr
  _ -> panic "mkImpTypeTrans0" ["incorrect number of terms"]

-- | Build a 'TypeTrans' represented by a "pure" (see 'TypeDesc') SAW type
mkPureTypeTrans1 :: OpenTerm -> (OpenTerm -> tr) -> TypeTrans 'True tr
mkPureTypeTrans1 tp f = TypeTransPure [tp] $ \case
  [t] -> f t
  _ -> panic "mkPureTypeTrans1" ["incorrect number of terms"]

-- | Build a 'TypeTrans' represented by a SAW type with the given description
mkImpTypeTrans1 :: TypeDesc -> (SpecTerm -> tr) -> TypeTrans 'False tr
mkImpTypeTrans1 d f = TypeTransImpure [d] $ \case
  [t] -> f t
  _ -> panic "mkImpTypeTrans1" ["incorrect number of terms"]

-- | Build a type translation whose representation type is just SAW core terms
-- of the supplied type
mkTermImpTypeTrans :: TypeDesc -> ImpTypeTrans SpecTerm
mkTermImpTypeTrans d = mkImpTypeTrans1 d id

-- | Extract out the single SAW type associated with a 'TypeTrans', or the unit
-- type if it has 0 SAW types. It is an error if it has 2 or more SAW types.
typeTransType1 :: HasCallStack => TypeTrans p tr -> PurityTerm p
typeTransType1 (TypeTransPure [] _) = unitTypeOpenTerm
typeTransType1 (TypeTransImpure [] _) = unitTypeTermLike
typeTransType1 (TypeTransPure [tp] _) = tp
typeTransType1 (TypeTransImpure [tp] _) = typeDescType tp
typeTransType1 _ =
  panic "typeTransType1" ["More than one type when at most one expected"]

-- | Extract out the single SAW type associated with a 'TypeTrans', or the unit
-- type if it has 0 SAW types. It is an error if it has 2 or more SAW types. The
-- term is always impure, i.e., returned as a 'SpecTerm'.
typeTransType1Imp :: HasCallStack => TypeTrans p tr -> SpecTerm
typeTransType1Imp (TypeTransPure [] _) = unitTypeTermLike
typeTransType1Imp (TypeTransImpure [] _) = unitTypeTermLike
typeTransType1Imp (TypeTransPure [tp] _) = openTermLike tp
typeTransType1Imp (TypeTransImpure [tp] _) = typeDescType tp
typeTransType1Imp _ =
  panic "typeTransType1Imp" ["More than one type when at most one expected"]

-- | Map the 'typeTransTypes' field of a 'TypeTrans' to a single type, where a
-- single type is mapped to itself, an empty list of types is mapped to @unit@,
-- and a list of 2 or more types is mapped to a tuple of the types
typeTransTupleType :: TypeTrans p tr -> PurityTerm p
typeTransTupleType (TypeTransPure tps _) = tupleOfTypes tps
typeTransTupleType (TypeTransImpure tps _) =
  typeDescType $ tupleOfTypeDescs tps

-- | Convert a 'TypeTrans' over 0 or more types to one over the one type
-- returned by 'typeTransTupleType'
tupleTypeTrans :: TypeTrans p tr -> TypeTrans p tr
tupleTypeTrans (TypeTransPure tps f) =
  TypeTransPure [tupleOfTypes tps]
  (\case
      [t] ->
        f $ map (\i -> projTupleOfTypes tps i t) $ take (length tps) [0..]
      _ -> panic "tupleTypeTrans" ["incorrect number of terms"])
tupleTypeTrans (TypeTransImpure tps f) =
  TypeTransImpure [tupleOfTypeDescs tps]
  (\case
      [t] ->
        f $ map (\i -> projTupleOfTypesI tps i t) $ take (length tps) [0..]
      _ -> panic "tupleTypeTrans" ["incorrect number of terms"])

-- | Form the 'TypeDesc' of the tuple of all the SAW core types in a 'TypeTrans'
typeTransTupleDesc :: TypeTrans b tr -> TypeDesc
typeTransTupleDesc = tupleOfTypeDescs . typeTransDescs

-- | Form the pure SAW core type that is the tuple of all the SAW core types in
-- a 'TypeTrans', if those types are all pure; it is an error if they are not
typeTransPureTupleType :: TypeTrans p tr -> OpenTerm
typeTransPureTupleType (TypeTransPure tps _) = tupleOfTypes tps
typeTransPureTupleType (TypeTransImpure tps _) =
  case typeDescPureType $ tupleOfTypeDescs tps of
    Just tp -> tp
    Nothing -> panic "typeTransPureTupleType"
      ["Expected pure type but found impure type"]

{-
-- | Convert a 'TypeTrans' over 0 or more types to one over 1 type of the form
-- @#(tp1, #(tp2, ... #(tpn, #()) ...))@. This is "strict" in the sense that
-- even a single type is tupled.
strictTupleTypeTrans :: TypeTrans tr -> TypeTrans tr
strictTupleTypeTrans ttrans =
  TypeTrans [tupleTypeOpenTerm $ typeTransTypes ttrans]
  (\case
      [t] ->
        typeTransF ttrans $ map (\i -> projTupleOpenTerm i t) $
        take (length $ typeTransTypes ttrans) [0..]
      _ -> error "strictTupleTypeTrans: incorrect number of terms")
-}

-- | Build a type translation for a list of translations
listTypeTrans :: [TypeTrans 'False tr] -> TypeTrans 'False [tr]
listTypeTrans [] = pure []
listTypeTrans (trans:transs) = liftA2 (:) trans $ listTypeTrans transs


----------------------------------------------------------------------
-- * Translation Monads
----------------------------------------------------------------------

-- | The result of translating a 'PermExpr' at 'CrucibleType' @a@. This is a
-- form of partially static data in the sense of partial evaluation.
data ExprTrans (a :: CrucibleType) where
  -- | LLVM pointers have their translations dictated by their permissions, so
  -- the translations of their expressions have no computational content
  ETrans_LLVM :: ExprTrans (LLVMPointerType w)

  -- | LLVM blocks also have no computational content
  ETrans_LLVMBlock :: ExprTrans (LLVMBlockType w)

  -- | Frames also have no computational content
  ETrans_LLVMFrame :: ExprTrans (LLVMFrameType w)

  -- | Lifetimes also have no computational content
  ETrans_Lifetime :: ExprTrans LifetimeType

  -- | Read-write modalities also have no computational content
  ETrans_RWModality :: ExprTrans RWModalityType

  -- | Structs are translated as a sequence of translations of the fields
  ETrans_Struct :: ExprTransCtx (CtxToRList ctx) -> ExprTrans (StructType ctx)

  -- | The computational content of functions is in their FunPerms, so functions
  -- themselves have no computational content
  ETrans_Fun :: ExprTrans (FunctionHandleType args ret)

  -- | The unit type has no computational content
  ETrans_Unit :: ExprTrans UnitType

  -- | The translation of Vectors of the Crucible any type have no content
  ETrans_AnyVector :: ExprTrans (VectorType AnyType)

  -- | The translation of a shape is a type description
  ETrans_Shape :: TypeDesc -> ExprTrans (LLVMShapeType w)

  -- | The translation of a permission is a type description
  ETrans_Perm :: TypeDesc -> ExprTrans (ValuePermType a)

  -- | The translation for every other expression type is just a SAW term. Note
  -- that this construct should not be used for the types handled above.
  ETrans_Term :: OpenTerm -> ExprTrans a

-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx = RAssign ExprTrans


-- | Destruct an 'ExprTrans' of shape type to a type description
unETransShape :: ExprTrans (LLVMShapeType w) -> TypeDesc
unETransShape (ETrans_Shape d) = d
unETransShape (ETrans_Term _) =
  panic "unETransShape" ["Incorrect translation of a shape expression"]

-- | Destruct an 'ExprTrans' of permission type to a type description
unETransPerm :: ExprTrans (ValuePermType a) -> TypeDesc
unETransPerm (ETrans_Perm d) = d
unETransPerm (ETrans_Term _) =
  panic "unETransPerm" ["Incorrect translation of a shape expression"]

-- | Describes a Haskell type that represents the translation of a term-like
-- construct that corresponds to 0 or more SAW terms
class IsTermTrans tr where
  transTerms :: HasCallStack => tr -> [SpecTerm]

-- | Describes a Haskell type that represents the translation of a term-like
-- construct that corresponds to 0 or more SAW terms that are "pure", meaning
-- they are 'OpenTerm's instead of 'SpecTerm's, i.e., they do not depend on the
-- function stack or event type
class IsPureTrans tr where
  transPureTerms :: HasCallStack => tr -> [OpenTerm]

-- | Build a tuple of the terms contained in a translation, with 0 terms mapping
-- to the unit term and one term mapping to itself. If @ttrans@ is a 'TypeTrans'
-- describing the SAW types associated with a @tr@ translation, then this
-- function returns an element of the type @'tupleTypeTrans' ttrans@.
transTupleTerm :: IsTermTrans tr => tr -> SpecTerm
transTupleTerm (transTerms -> [t]) = t
transTupleTerm tr = tupleOfTerms $ transTerms tr

{-
-- | Build a tuple of the terms contained in a translation. This is "strict" in
-- that it always makes a tuple, even for a single type, unlike
-- 'transTupleTerm'.  If @ttrans@ is a 'TypeTrans' describing the SAW types
-- associated with a @tr@ translation, then this function returns an element of
-- the type @'strictTupleTypeTrans' ttrans@.
strictTransTupleTerm :: IsTermTrans tr => tr -> OpenTerm
strictTransTupleTerm tr = tupleOpenTerm $ transTerms tr
-}

-- | Like 'transTupleTerm' but raise an error if there are more than 1 terms
transTerm1 :: HasCallStack => IsTermTrans tr => tr -> SpecTerm
transTerm1 (transTerms -> []) = unitTermLike
transTerm1 (transTerms -> [t]) = t
transTerm1 tr = panic "transTerm1" ["Expected at most one term, but found "
                                    ++ show (length $ transTerms tr)]

-- | Like 'transTerm1' but for pure terms
transPureTerm1 :: HasCallStack => IsPureTrans tr => tr -> OpenTerm
transPureTerm1 (transPureTerms -> []) = unitOpenTerm
transPureTerm1 (transPureTerms -> [t]) = t
transPureTerm1 tr = panic "transPureTerm1" ["Expected at most one term, but found "
                                            ++ show (length $ transPureTerms tr)]

instance IsTermTrans tr => IsTermTrans [tr] where
  transTerms = concatMap transTerms

instance IsPureTrans tr => IsPureTrans [tr] where
  transPureTerms = concatMap transPureTerms

instance IsPureTrans (TypeTrans 'True tr) where
  transPureTerms = typeTransTypes

instance IsTermTrans (TypeTrans 'True tr) where
  transTerms = map openTermLike . transPureTerms

instance IsTermTrans (TypeTrans 'False tr) where
  transTerms = typeTransTypes

instance IsPureTrans (ExprTrans tp) where
  transPureTerms ETrans_LLVM = []
  transPureTerms ETrans_LLVMBlock = []
  transPureTerms ETrans_LLVMFrame = []
  transPureTerms ETrans_Lifetime = []
  transPureTerms ETrans_RWModality = []
  transPureTerms (ETrans_Struct etranss) =
    concat $ RL.mapToList transPureTerms etranss
  transPureTerms ETrans_Fun = []
  transPureTerms ETrans_Unit = []
  transPureTerms ETrans_AnyVector = []
  transPureTerms (ETrans_Shape d) = [typeDescLRT d]
  transPureTerms (ETrans_Perm d) = [typeDescLRT d]
  transPureTerms (ETrans_Term t) = [t]

instance IsTermTrans (ExprTrans tp) where
  transTerms = map openTermLike . transPureTerms

instance IsPureTrans (ExprTransCtx ctx) where
  transPureTerms MNil = []
  transPureTerms (ctx :>: etrans) = transPureTerms ctx ++ transPureTerms etrans

instance IsTermTrans (ExprTransCtx ctx) where
  transTerms = map openTermLike . transPureTerms

-- | Map a context of expression translations to a list of 'SpecTerm's
exprCtxToTerms :: ExprTransCtx tps -> [SpecTerm]
exprCtxToTerms = concat . RL.mapToList transTerms

-- | Map a context of expression translations to a list of 'OpenTerm's
exprCtxToPureTerms :: ExprTransCtx tps -> [OpenTerm]
exprCtxToPureTerms = concat . RL.mapToList transPureTerms

-- | Map an 'ExprTrans' to its type translation
exprTransType :: ExprTrans tp -> PureTypeTrans (ExprTrans tp)
exprTransType ETrans_LLVM = mkPureTypeTrans0 ETrans_LLVM
exprTransType ETrans_LLVMBlock = mkPureTypeTrans0 ETrans_LLVMBlock
exprTransType ETrans_LLVMFrame = mkPureTypeTrans0 ETrans_LLVMFrame
exprTransType ETrans_Lifetime = mkPureTypeTrans0  ETrans_Lifetime
exprTransType ETrans_RWModality = mkPureTypeTrans0 ETrans_RWModality
exprTransType (ETrans_Struct etranss) = ETrans_Struct <$> exprCtxType etranss
exprTransType ETrans_Fun = mkPureTypeTrans0 ETrans_Fun
exprTransType ETrans_Unit = mkPureTypeTrans0 ETrans_Unit
exprTransType ETrans_AnyVector = mkPureTypeTrans0 ETrans_AnyVector
exprTransType (ETrans_Shape _) =
  mkPureTypeTrans1 (dataTypeOpenTerm "Prelude.LetRecType" [])
  (ETrans_Shape . typeDescFromLRT)
exprTransType (ETrans_Perm _) =
  mkPureTypeTrans1 (dataTypeOpenTerm "Prelude.LetRecType" [])
  (ETrans_Perm . typeDescFromLRT)
exprTransType (ETrans_Term t) = mkPureTypeTrans1 (openTermType t) ETrans_Term

-- | Map a context of expression translation to a list of the SAW core types of
-- all the terms it contains
exprCtxType :: ExprTransCtx ctx -> PureTypeTrans (ExprTransCtx ctx)
exprCtxType MNil = mkPureTypeTrans0 MNil
exprCtxType (ectx :>: e) = (:>:) <$> exprCtxType ectx <*> exprTransType e

-- | Map an 'ExprTrans' to the SAW core terms it contains, similarly to
-- 'transPureTerms', except that all type descriptions are mapped to pure types,
-- not terms of type @LetRecType@. Return 'Nothing' if this is not possible.
exprTransPureTypeTerms :: ExprTrans tp -> Maybe [OpenTerm]
exprTransPureTypeTerms (ETrans_Shape d) = (:[]) <$> typeDescPureType d
exprTransPureTypeTerms (ETrans_Perm d) = (:[]) <$> typeDescPureType d
exprTransPureTypeTerms etrans = Just $ transPureTerms etrans

-- | Map an 'ExprTransCtx' to the SAW core terms it contains, similarly to
-- 'transPureTerms', except that all type descriptions are mapped to pure types,
-- not terms of type @LetRecType@. Return 'Nothing' if this is not possible.
exprCtxPureTypeTerms :: ExprTransCtx tps -> Maybe [OpenTerm]
exprCtxPureTypeTerms =
  fmap concat . sequence . RL.mapToList exprTransPureTypeTerms

-- | Class for valid translation info types, which must contain at least a
-- context of expression translations
class TransInfo info where
  infoCtx :: info ctx -> ExprTransCtx ctx
  infoEnv :: info ctx -> PermEnv
  infoChecksFlag :: info ctx -> ChecksFlag
  extTransInfo :: ExprTrans tp -> info ctx -> info (ctx :> tp)

-- | A "translation monad" is a 'Reader' monad with some info type that is
-- parameterized by a translation context
newtype TransM info (ctx :: RList CrucibleType) a =
  TransM { unTransM :: Reader (info ctx) a }
  deriving (Functor, Applicative, Monad, OpenTermLike)

instance Fail.MonadFail (TransM info ctx) where
  fail = error

-- | The run function for the 'TransM' monad
runTransM :: TransM info ctx a -> info ctx -> a
runTransM (TransM m) = runReader m

instance MonadReader (info ctx) (TransM info ctx) where
  ask = TransM ask
  local f (TransM m) = TransM $ local f m

-- | Run a translation computation with a modified info object
withInfoM :: (info ctx -> info' ctx') -> TransM info' ctx' a ->
             TransM info ctx a
withInfoM f (TransM m) = TransM $ withReader f m

-- | Run a translation computation in an extended context
inExtTransM :: TransInfo info => ExprTrans tp -> TransM info (ctx :> tp) a ->
               TransM info ctx a
inExtTransM etrans (TransM m) = TransM $ withReader (extTransInfo etrans) m

-- | Run a translation computation in a context extended with multiple types
inExtMultiTransM :: TransInfo info => ExprTransCtx ctx2 ->
                    TransM info (ctx :++: ctx2) a ->
                    TransM info ctx a
inExtMultiTransM MNil m = m
inExtMultiTransM (ctx :>: etrans) m =
  inExtMultiTransM ctx $ inExtTransM etrans m

-- | Build a @sawLet@-binding in a translation monad that binds a pure variable;
-- the type must be pure as well, even though it is a 'SpecTerm'
sawLetTransM :: String -> SpecTerm -> SpecTerm -> SpecTerm ->
                (OpenTerm -> TransM info ctx SpecTerm) ->
                TransM info ctx SpecTerm
sawLetTransM x tp tp_ret rhs body_m =
  do r <- ask
     return $
       sawLetPureSpecTerm (pack x) tp tp_ret rhs $ \x' ->
       runTransM (body_m x') r

-- | Build 0 or more sawLet-bindings in a translation monad, using the same
-- variable name
sawLetTransMultiM :: String -> [SpecTerm] -> SpecTerm -> [SpecTerm] ->
                  ([OpenTerm] -> TransM info ctx SpecTerm) ->
                  TransM info ctx SpecTerm
sawLetTransMultiM _ [] _ [] f = f []
sawLetTransMultiM x (tp:tps) ret_tp (rhs:rhss) f =
  sawLetTransM x tp ret_tp rhs $ \var_tm ->
  sawLetTransMultiM x tps ret_tp rhss (\var_tms -> f (var_tm:var_tms))
sawLetTransMultiM _ _ _ _ _ =
  error "sawLetTransMultiM: numbers of types and right-hand sides disagree"

-- | Run a translation computation in an extended context, where we sawLet-bind any
-- term in the supplied expression translation
inExtTransSAWLetBindM :: TransInfo info => PureTypeTrans (ExprTrans tp) ->
                         SpecTerm -> ExprTrans tp ->
                         TransM info (ctx :> tp) SpecTerm ->
                         TransM info ctx SpecTerm
inExtTransSAWLetBindM tp_trans tp_ret etrans m =
  sawLetTransMultiM "z" (map openTermLike $
                         typeTransTypes tp_trans) tp_ret (transTerms etrans) $
  \var_tms -> inExtTransM (typeTransF tp_trans var_tms) m

-- | Run a translation computation in context @(ctx1 :++: ctx2) :++: ctx2@ by
-- copying the @ctx2@ portion of the current context
inExtMultiTransCopyLastM :: TransInfo info => prx ctx1 -> RAssign any ctx2 ->
                            TransM info ((ctx1 :++: ctx2) :++: ctx2) a ->
                            TransM info (ctx1 :++: ctx2) a
inExtMultiTransCopyLastM ctx1 ctx2 m =
  do ectx <- infoCtx <$> ask
     let (_,ectx2) = RL.split ctx1 ctx2 ectx
     inExtMultiTransM ectx2 m

-- | Run a translation computation in a specific context
inCtxTransM :: TransInfo info => ExprTransCtx ctx ->
               TransM info ctx a -> TransM info RNil a
inCtxTransM MNil m = m
inCtxTransM (ctx :>: etrans) m = inCtxTransM ctx $ inExtTransM etrans m

-- | Build a multi-binding for the current context
nuMultiTransM :: TransInfo info => (RAssign Name ctx -> b) ->
                 TransM info ctx (Mb ctx b)
nuMultiTransM f =
  do info <- ask
     return $ nuMulti (RL.map (\_ -> Proxy) (infoCtx info)) f

-- | Apply the result of a pure translation to that of another
applyPureTransM :: TransM info ctx OpenTerm -> TransM info ctx OpenTerm ->
                   TransM info ctx OpenTerm
applyPureTransM m1 m2 = applyOpenTerm <$> m1 <*> m2

-- | Apply the result of an impure translation to that of another
applyImpTransM :: TransM info ctx SpecTerm -> TransM info ctx SpecTerm ->
                  TransM info ctx SpecTerm
applyImpTransM m1 m2 = applyTermLike <$> m1 <*> m2

-- | Apply the result of a pure translation to that of multiple translations
applyMultiPureTransM :: TransM info ctx OpenTerm ->
                        [TransM info ctx OpenTerm] ->
                        TransM info ctx OpenTerm
applyMultiPureTransM m ms = foldl applyPureTransM m ms

-- | Apply the result of an impure translation to that of multiple translations
applyGlobalImpTransM :: Ident -> [TransM info ctx SpecTerm] ->
                        TransM info ctx SpecTerm
applyGlobalImpTransM ident ms =
  foldl applyImpTransM (return $ globalTermLike ident) ms

-- | Build a lambda-abstraction as an 'OpenTerm' inside the 'TransM' monad
lambdaOpenTermTransM :: String -> OpenTerm ->
                        (OpenTerm -> TransM info ctx OpenTerm) ->
                        TransM info ctx OpenTerm
lambdaOpenTermTransM x tp body_f =
  ask >>= \info ->
  return (lambdaOpenTerm (pack x) tp $ \t -> runTransM (body_f t) info)

-- | Build a lambda-abstraction as a 'SpecTerm' inside the 'TransM' monad
lambdaSpecTermTransM :: String -> SpecTerm ->
                        (SpecTerm -> TransM info ctx SpecTerm) ->
                        TransM info ctx SpecTerm
lambdaSpecTermTransM x tp body_f =
  ask >>= \info ->
  return (lambdaTermLike (pack x) tp $ \t -> runTransM (body_f t) info)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans', using the 'String' as a variable name prefix
-- for the @xi@ variables
lambdaTrans :: String -> TypeTrans p tr -> (tr -> SpecTerm) -> SpecTerm
lambdaTrans x (TypeTransPure tps tr_f) body_f =
  lambdaPureSpecTermMulti
  (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] $
   map openTermLike tps)
  (body_f . tr_f)
lambdaTrans x (TypeTransImpure tps tr_f) body_f =
  lambdaTermLikeMulti
  (zipWith (\i tp -> (pack (x ++ show (i :: Integer)),
                      typeDescType tp)) [0..] tps)
  (body_f . tr_f)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a pure 'TypeTrans', using the 'String' as a variable name
-- prefix for the @xi@ variables, returning a pure term
lambdaPureTrans :: String -> PureTypeTrans tr -> (tr -> OpenTerm) -> OpenTerm
lambdaPureTrans x (TypeTransPure tps tr_f) body_f =
  lambdaOpenTermMulti
  (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp)) [0..] tps)
  (body_f . tr_f)

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a 'TypeTrans' inside a translation monad, using the
-- 'String' as a variable name prefix for the @xi@ variables
lambdaTransM :: String -> TypeTrans p tr -> (tr -> TransM info ctx SpecTerm) ->
                TransM info ctx SpecTerm
lambdaTransM x tp body_f =
  ask >>= \info -> return (lambdaTrans x tp (flip runTransM info . body_f))

-- | Build a nested lambda-abstraction
--
-- > \x1:tp1 -> ... -> \xn:tpn -> body
--
-- over the types in a pure 'TypeTrans' inside a translation monad, using the
-- 'String' as a variable name prefix for the @xi@ variables, returning a pure
-- term
lambdaPureTransM :: String -> PureTypeTrans tr ->
                    (tr -> TransM info ctx OpenTerm) -> TransM info ctx OpenTerm
lambdaPureTransM x tp body_f =
  ask >>= \info -> return (lambdaPureTrans x tp (flip runTransM info . body_f))

-- | Build a lambda-abstraction
--
-- > \x1:(tp1, ..., tpn) -> body
--
-- over a tuple of the types in a 'TypeTrans'. Note that this always builds
-- exactly one lambda-abstraction, even if there are 0 types.
lambdaTupleTransM :: String -> TypeTrans p tr -> (tr -> TransM info ctx SpecTerm) ->
                     TransM info ctx SpecTerm
lambdaTupleTransM x ttrans body_f =
  lambdaTransM x (tupleTypeTrans ttrans) body_f

-- | Construct a @LetRecType@ inductive description
--
-- > LRT_FunDep tp1 \(x1 : tp1) -> ... -> LRT_FunDep tpn \(xn : tpn) ->
-- >   body x1 ... xn
--
-- of a pi abstraction over the types @tpi@ in a pure 'TypeTrans', passing the
-- abstracted variables to the supplied @body@ function, which should itself
-- return a @LetRecType@
piLRTTrans :: String -> PureTypeTrans tr -> (tr -> OpenTerm) -> OpenTerm
piLRTTrans x tps body_f =
  foldr (\(i,tp) rest_f vars ->
          let nm = pack (x ++ show (i :: Integer))
              t = lambdaOpenTerm nm tp (\var -> rest_f (vars ++ [var])) in
          ctorOpenTerm "Prelude.LRT_FunDep" [tp, t])
  (body_f . typeTransF tps) (zip [0..] $ typeTransTypes tps) []

-- | Perform 'piLRTTrans' inside a translation monad
piLRTTransM :: String -> TypeTrans 'True tr ->
               (tr -> TransM info ctx OpenTerm) -> TransM info ctx OpenTerm
piLRTTransM x tps body_f =
  ask >>= \info -> return (piLRTTrans x tps (flip runTransM info . body_f))

-- | Construct a @LetRecType@ inductive description
--
-- > LRT_FunClos lrt1 (LRT_FunClos lrt2 (... body ...))
--
-- of monadic arrow types over the @LetRecType@ type descriptions @lrti@ in a
-- 'TypeTrans'
arrowLRTTrans :: ImpTypeTrans tr -> OpenTerm -> OpenTerm
arrowLRTTrans tps body_top =
  foldr (\d body ->
          ctorOpenTerm "Prelude.LRT_FunClos" [typeDescLRT d, body])
  body_top (typeTransDescs tps)

-- | Perform 'arrowLRTTrans' inside a translation monad
arrowLRTTransM :: ImpTypeTrans tr ->
                  TransM info ctx OpenTerm -> TransM info ctx OpenTerm
arrowLRTTransM tps body =
  ask >>= \info -> return (arrowLRTTrans tps (runTransM body info))

-- | Build a pi-abstraction over the types in a 'TypeTrans' inside a
-- translation monad, using the 'String' as a variable name prefix
piTransM :: String -> PureTypeTrans tr -> (tr -> TransM info ctx OpenTerm) ->
            TransM info ctx OpenTerm
piTransM x tps body_f =
  ask >>= \info ->
  return (piOpenTermMulti
          (zipWith (\i tp -> (pack (x ++ show (i :: Integer)), tp))
           [0..] (typeTransTypes tps))
          (\ts -> runTransM (body_f $ typeTransF tps ts) info))

{-
-- | Build a pi-abstraction inside the 'TransM' monad
piOpenTermTransM :: String -> OpenTerm ->
                    (OpenTerm -> TransM info ctx OpenTerm) ->
                    TransM info ctx OpenTerm
piOpenTermTransM x tp body_f =
  ask >>= \info ->
  return (piOpenTerm (pack x) tp $ \t -> runTransM (body_f t) info)
-}

-- | Build a let-binding in a translation monad
letTransM :: String -> SpecTerm -> TransM info ctx SpecTerm ->
             (SpecTerm -> TransM info ctx SpecTerm) ->
             TransM info ctx SpecTerm
letTransM x tp rhs_m body_m =
  do r <- ask
     return $
       letTermLike (pack x) tp (runTransM rhs_m r) (\x' -> runTransM (body_m x') r)

-- | Build a bitvector type in a translation monad
bitvectorTransM :: TransM info ctx OpenTerm -> TransM info ctx OpenTerm
bitvectorTransM m =
  applyMultiPureTransM (return $ globalOpenTerm "Prelude.Vec")
  [m, return $ globalOpenTerm "Prelude.Bool"]

-- | Build an @Either@ type in SAW from the 'typeTransTupleType's of the left
-- and right types
eitherTypeTrans :: ImpTypeTrans trL -> ImpTypeTrans trR -> TypeDesc
eitherTypeTrans tp_l tp_r =
  typeDescEither (typeTransTupleDesc tp_l) (typeTransTupleDesc tp_r)

-- | Apply the @Left@ constructor of the @Either@ type in SAW to the
-- 'transTupleTerm' of the input
leftTrans :: IsTermTrans trL => ImpTypeTrans trL -> ImpTypeTrans trR -> trL ->
             SpecTerm
leftTrans tp_l tp_r tr =
  ctorTermLike "Prelude.Left"
  [typeTransTupleType tp_l, typeTransTupleType tp_r, transTupleTerm tr]

-- | Apply the @Right@ constructor of the @Either@ type in SAW to the
-- 'transTupleTerm' of the input
rightTrans :: IsTermTrans trR => ImpTypeTrans trL -> ImpTypeTrans trR -> trR ->
              SpecTerm
rightTrans tp_l tp_r tr =
  ctorTermLike "Prelude.Right"
  [typeTransTupleType tp_l, typeTransTupleType tp_r, transTupleTerm tr]

-- | Eliminate a SAW @Either@ type
eitherElimTransM :: ImpTypeTrans trL -> ImpTypeTrans trR ->
                    ImpTypeTrans tr -> (trL -> TransM info ctx SpecTerm) ->
                    (trR -> TransM info ctx SpecTerm) -> SpecTerm ->
                    TransM info ctx SpecTerm
eitherElimTransM tp_l tp_r tp_ret fl fr eith =
  do fl_trans <- lambdaTupleTransM "x_left" tp_l fl
     fr_trans <- lambdaTupleTransM "x_right" tp_r fr
     return $ applyTermLikeMulti (globalTermLike "Prelude.either")
       [ typeTransTupleType tp_l, typeTransTupleType tp_r,
         typeTransTupleType tp_ret, fl_trans, fr_trans, eith ]

-- | Eliminate a multi-way SAW @Eithers@ type, taking in: a list of the
-- translations of the types in the @Eithers@ type; the translation of the
-- output type; a list of functions for the branches of the @Eithers@
-- elimination; and the term of @Eithers@ type being eliminated
eithersElimTransM :: [ImpTypeTrans tr_in] -> ImpTypeTrans tr_out ->
                     [tr_in -> TransM info ctx SpecTerm] -> SpecTerm ->
                     TransM info ctx SpecTerm
eithersElimTransM tps tp_ret fs eith =
  foldr (\(tp,f) restM ->
          do f_trans <- lambdaTupleTransM "x_eith_elim" tp f
             rest <- restM
             return (ctorTermLike "Prelude.FunsTo_Cons"
                     [typeTransTupleType tp_ret,
                      typeTransTupleType tp, f_trans, rest]))
  (return $ ctorTermLike "Prelude.FunsTo_Nil" [typeTransTupleType tp_ret])
  (zip tps fs)
  >>= \elims_trans ->
  return (applyGlobalTermLike "Prelude.eithers"
          [typeTransTupleType tp_ret, elims_trans, eith])

-- | Build the dependent pair type whose first projection type is the
-- 'typeTransTupleType' of the supplied 'TypeTrans' and whose second projection
-- is given by the type translation returned by the supplied monadic function.
-- The Boolean flag indicates whether this monadic function is expected to
-- return a pure type, in which case the returned dependent pair type is pure,
-- or not, in which case it isn't. It is an error if the Boolean flag is 'True'
-- but the monadic function returns an impure type description.
sigmaTypeTransM :: LocalName -> PureTypeTrans trL -> Bool ->
                   (trL -> TransM info ctx TypeDesc) ->
                   TransM info ctx TypeDesc
sigmaTypeTransM _ ttrans@(typeTransTypes -> []) _ tp_f =
  tp_f (typeTransF ttrans [])
sigmaTypeTransM x ttrans pure_p tp_f =
  do info <- ask
     return $ typeDescSigma x (typeTransTupleType ttrans) pure_p $ \e_tup ->
       runTransM (tp_f $ typeTransF (tupleTypeTrans ttrans) [e_tup]) info

-- | Like `sigmaTypeTransM`, but translates `exists x.eq(y)` into just `x`
sigmaTypePermTransM :: TransInfo info => LocalName ->
                       PureTypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx TypeDesc
sigmaTypePermTransM x ttrans mb_p = case mbMatch mb_p of
  [nuMP| ValPerm_Eq _ |] -> return $ TypeDescPure $ typeTransTupleType ttrans
  _ ->
    sigmaTypeTransM x ttrans (hasPureTrans mb_p) $ \etrans ->
    inExtTransM etrans (typeTransTupleDesc <$> translate mb_p)

-- | Build a dependent pair of the type returned by 'sigmaTypeTransM'. Note that
-- the 'TypeTrans' returned by the type-level function will in general be in a
-- larger context than that of the right-hand projection argument, so we allow
-- the representation types to be different to allow for this.
sigmaTransM :: (IsTermTrans trL, IsTermTrans trR2) =>
               String -> PureTypeTrans trL ->
               (trL -> TransM info ctx (ImpTypeTrans trR1)) ->
               trL -> TransM info ctx trR2 ->
               TransM info ctx SpecTerm
sigmaTransM _ (typeTransTypes -> []) _ _ rhs_m = transTupleTerm <$> rhs_m
sigmaTransM x tp_l tp_r lhs rhs_m =
  do tp_r_trm <- lambdaTupleTransM x tp_l ((typeTransTupleType <$>) . tp_r)
     rhs <- transTupleTerm <$> rhs_m
     return (ctorTermLike "Prelude.exists"
             [openTermLike (typeTransTupleType tp_l), tp_r_trm,
              transTupleTerm lhs, rhs])

-- | Like `sigmaTransM`, but translates `exists x.eq(y)` into just `x`
sigmaPermTransM :: TransInfo info => String -> PureTypeTrans (ExprTrans a) ->
                   Mb (ctx :> a) (ValuePerm b) -> ExprTrans a ->
                   TransM info ctx (PermTrans ctx b) ->
                   TransM info ctx SpecTerm
sigmaPermTransM x ttrans mb_p etrans rhs_m = case mbMatch mb_p of
  [nuMP| ValPerm_Eq _ |] -> return $ transTupleTerm etrans
  _ -> sigmaTransM x ttrans (flip inExtTransM $ translate mb_p) etrans rhs_m

-- | Eliminate a dependent pair of the type returned by 'sigmaTypeTransM'
sigmaElimTransM :: (IsTermTrans trL, IsTermTrans trR) =>
                   String -> PureTypeTrans trL ->
                   (trL -> TransM info ctx (ImpTypeTrans trR)) ->
                   TransM info ctx (ImpTypeTrans trRet) ->
                   (trL -> trR -> TransM info ctx SpecTerm) ->
                   SpecTerm ->
                   TransM info ctx SpecTerm
sigmaElimTransM _ tp_l@(typeTransTypes -> []) tp_r _ f sigma =
  do let proj_l = typeTransF tp_l []
     proj_r <- flip (typeTransF . tupleTypeTrans) [sigma] <$> tp_r proj_l
     f proj_l proj_r
sigmaElimTransM x tp_l tp_r tp_ret_m f sigma =
  do let tp_l_trm = openTermLike $ typeTransTupleType tp_l
     tp_r_trm <- lambdaTupleTransM x tp_l (\tr ->
                                            typeTransTupleType <$> tp_r tr)
     let proj_l_trm =
           applyGlobalTermLike "Prelude.Sigma_proj1" [tp_l_trm, tp_r_trm, sigma]
     tp_ret <- typeTransTupleType <$> tp_ret_m
     sawLetTransM x tp_l_trm tp_ret proj_l_trm $ \proj_l_pure ->
       do let proj_l = typeTransF (tupleTypeTrans tp_l) [proj_l_pure]
          tp_r_app <- tp_r proj_l
          let proj_r_trm =
                applyGlobalTermLike "Prelude.Sigma_proj2" [tp_l_trm,
                                                           tp_r_trm, sigma]
          let proj_r = typeTransF (tupleTypeTrans tp_r_app) [proj_r_trm]
          f proj_l proj_r


-- | Like `sigmaElimTransM`, but translates `exists x.eq(y)` into just `x`
sigmaElimPermTransM :: (TransInfo info) =>
                       String -> PureTypeTrans (ExprTrans trL) ->
                       Mb (ctx :> trL) (ValuePerm trR) ->
                       TransM info ctx (ImpTypeTrans trRet) ->
                       (ExprTrans trL -> PermTrans (ctx :> trL) trR ->
                                         TransM info ctx SpecTerm) ->
                       SpecTerm ->
                       TransM info ctx SpecTerm
sigmaElimPermTransM x tp_l mb_p tp_ret_m f sigma = case mbMatch mb_p of
  [nuMP| ValPerm_Eq e |] ->
    do let tp_l_trm = openTermLike $ typeTransTupleType tp_l
       tp_ret <- typeTransTupleType <$> tp_ret_m
       sawLetTransM x tp_l_trm tp_ret sigma $ \sigma_pure ->
         f (typeTransF (tupleTypeTrans tp_l) [sigma_pure]) (PTrans_Eq e)
  _ -> sigmaElimTransM x tp_l (flip inExtTransM $ translate mb_p)
                       tp_ret_m f sigma


-- | The class for translating to SAW
class Translate info ctx a tr | ctx a -> tr where
  translate :: Mb ctx a -> TransM info ctx tr

-- | Translate to SAW and then convert to a single pure SAW term, raising an
-- error if the result has 0 or more than 1 terms
translate1Pure :: (IsPureTrans tr, Translate info ctx a tr, HasCallStack) =>
                  Mb ctx a -> TransM info ctx OpenTerm
translate1Pure a = translate a >>= \tr -> case transPureTerms tr of
  [t] -> return t
  ts -> panic "translate1" ["expected 1 term, found " ++ show (length ts)]

-- | Translate to SAW and then convert to a single SAW term, raising an error if
-- the result has 0 or more than 1 terms
translate1 :: (IsTermTrans tr, Translate info ctx a tr, HasCallStack) =>
              Mb ctx a -> TransM info ctx SpecTerm
translate1 a = translate a >>= \tr -> case transTerms tr of
  [t] -> return t
  ts -> error ("translate1: expected 1 term, found " ++ show (length ts)
               ++ nlPrettyCallStack callStack)

-- | Translate a "closed" term, that is not in a binding
translateClosed :: (TransInfo info, Translate info ctx a tr) =>
                   a -> TransM info ctx tr
translateClosed a = nuMultiTransM (const a) >>= translate

instance (Translate info ctx a tr, NuMatching a) =>
         Translate info ctx [a] [tr] where
  translate = mapM translate . mbList

-- | Generic function for testing if a particular constuct translates to a pure
-- term in the sense of not depending on the current @FunStack@ or event type,
-- meaning it is an 'OpenTerm', and also that it only contains pure 'TypeDesc's,
-- i.e., ones that do not contain closures. This is used as an optimization for
-- translating sigma types to pure types when their right-hand sides are pure.
class HasPureTrans a where
  hasPureTrans :: Mb (ctx :: RList CrucibleType) a -> Bool

instance (HasPureTrans a, NuMatching a) => HasPureTrans [a] where
  hasPureTrans = and . map hasPureTrans . mbList


----------------------------------------------------------------------
-- * Translating Types
----------------------------------------------------------------------

-- | A flag for whether or not to perform checks in the translation. We use this
-- type, rather than just 'Bool', for documentation purposes.
newtype ChecksFlag = ChecksFlag { checksFlagSet :: Bool }

-- | The 'ChecksFlag' specifying not to perform any translation checks
noChecks :: ChecksFlag
noChecks = ChecksFlag False

-- | The 'ChecksFlag' specifying to perform all translation checks
doChecks :: ChecksFlag
doChecks = ChecksFlag True

-- | Translation info for translating types and pure expressions
data TypeTransInfo ctx =
  TypeTransInfo
  {
    ttiExprCtx :: ExprTransCtx ctx,
    ttiPermEnv :: PermEnv,
    ttiChecksFlag :: ChecksFlag
  }

-- (ExprTransCtx ctx) PermEnv ChecksFlag

-- | Build an empty 'TypeTransInfo' from a 'PermEnv'
emptyTypeTransInfo :: PermEnv -> ChecksFlag -> TypeTransInfo RNil
emptyTypeTransInfo = TypeTransInfo MNil

instance TransInfo TypeTransInfo where
  infoCtx (TypeTransInfo ctx _ _) = ctx
  infoEnv (TypeTransInfo _ env _) = env
  infoChecksFlag (TypeTransInfo _ _ cflag) = cflag
  extTransInfo etrans (TypeTransInfo ctx env checks) =
    TypeTransInfo (ctx :>: etrans) env checks

-- | The translation monad specific to translating types and pure expressions
type TypeTransM = TransM TypeTransInfo

-- | Any 'TransM' can run a 'TypeTransM'
tpTransM :: TransInfo info => TypeTransM ctx a -> TransM info ctx a
tpTransM =
  withInfoM $ \info ->
  TypeTransInfo (infoCtx info) (infoEnv info) (infoChecksFlag info)

-- | Run a 'TypeTransM' computation in the empty translation context
runNilTypeTransM :: PermEnv -> ChecksFlag -> TypeTransM RNil a -> a
runNilTypeTransM env checks m = runTransM m (emptyTypeTransInfo env checks)

-- | Convert a 'TypeTransM' computation into a pure function that takes in an
-- 'ExprTransCtx'
ctxFunTypeTransM :: TypeTransM ctx a -> TypeTransM ctx' (ExprTransCtx ctx -> a)
ctxFunTypeTransM m =
  do TypeTransInfo {..} <- ask
     return $ \ectx -> runTransM m $ TypeTransInfo { ttiExprCtx = ectx, .. }

-- | Run a translation computation in an empty expression translation context
inEmptyCtxTransM :: TypeTransM RNil a -> TypeTransM ctx a
inEmptyCtxTransM =
  withInfoM (\(TypeTransInfo _ env checks) -> TypeTransInfo MNil env checks)

instance TransInfo info => Translate info ctx (NatRepr n) OpenTerm where
  translate mb_n = return $ natOpenTerm $ mbLift $ fmap natValue mb_n

-- | Return a pure type translation that uses a single term of the given type
returnType1 :: OpenTerm -> TransM info ctx (PureTypeTrans (ExprTrans a))
returnType1 tp = return $ mkPureTypeTrans1 tp ETrans_Term

-- | Translate a pure expression type to a 'TypeTrans', which both gives a list
-- of 0 or more SAW core types and also gives a function to create an expression
-- translation from SAW core terms of those types. The 'Bool' flag indicates
-- whether the translation should be only to pure types, meaning that shapes and
-- permissions are translated to SAW core types; otherwise, they are translated
-- to terms of SAW core type @LetRecType@, which can only be used for describing
-- monadic computations.
translateType :: TransInfo info => Bool -> TypeRepr a ->
                 TransM info ctx (PureTypeTrans (ExprTrans a))
translateType _ AnyRepr =
  return $ error "Translate: Any"
translateType _ UnitRepr =
  return $ mkPureTypeTrans0 ETrans_Unit
translateType _ BoolRepr =
  returnType1 $ globalOpenTerm "Prelude.Bool"
translateType _ NatRepr =
  returnType1 $ dataTypeOpenTerm "Prelude.Nat" []
translateType _ IntegerRepr =
  return $ error "translate: IntegerRepr"
translateType _ RealValRepr =
  return $ error "translate: RealValRepr"
translateType _ ComplexRealRepr =
  return $ error "translate: ComplexRealRepr"
translateType _ (SequenceRepr{}) =
  return $ error "translate: SequenceRepr"
translateType _ (BVRepr w) =
  returnType1 =<< bitvectorTransM (translateClosed w)
translateType _ (VectorRepr AnyRepr) =
  return $ mkPureTypeTrans0 ETrans_AnyVector

-- Our special-purpose intrinsic types, whose translations do not have
-- computational content
translateType _ (LLVMPointerRepr _) =
  return $ mkPureTypeTrans0 ETrans_LLVM
translateType _ (LLVMBlockRepr _) =
  return $ mkPureTypeTrans0 ETrans_LLVMBlock
translateType _ (LLVMFrameRepr _) =
  return $ mkPureTypeTrans0 ETrans_LLVMFrame
translateType _ LifetimeRepr =
  return $ mkPureTypeTrans0 ETrans_Lifetime
translateType _ PermListRepr =
  returnType1 (sortOpenTerm $ mkSort 0)
translateType _ RWModalityRepr =
  return $ mkPureTypeTrans0 ETrans_RWModality

-- Permissions and LLVM shapes translate to types (for the pure translation) or
-- LetRecTypes (for the impure translation)
translateType False (ValuePermRepr _) =
  return $ mkPureTypeTrans1 (dataTypeOpenTerm "Prelude.LetRecType" [])
  (ETrans_Perm . typeDescFromLRT)
translateType True (ValuePermRepr _) =
  return $ mkPureTypeTrans1 (sortOpenTerm $ mkSort 0)
  (ETrans_Perm . TypeDescPure)
translateType False (LLVMShapeRepr _) =
  return $ mkPureTypeTrans1 (dataTypeOpenTerm "Prelude.LetRecType" [])
  (ETrans_Shape . typeDescFromLRT)
translateType True (LLVMShapeRepr _) =
  return $ mkPureTypeTrans1 (sortOpenTerm $ mkSort 0)
  (ETrans_Shape . TypeDescPure)

-- We can't handle any other special-purpose types
translateType _ (IntrinsicRepr _ _) =
  return $ error "translate: IntrinsicRepr"

translateType _ (RecursiveRepr _ _) =
  return $ error "translate: RecursiveRepr"
translateType _ (FloatRepr _) =
  returnType1 $ dataTypeOpenTerm "Prelude.Float" []
translateType _ (IEEEFloatRepr _) =
  return $ error "translate: IEEEFloatRepr"
translateType _ CharRepr =
  return $ error "translate: CharRepr"
translateType _ (StringRepr UnicodeRepr) =
  returnType1 stringTypeOpenTerm
translateType _ (StringRepr _) =
  return $ error "translate: StringRepr non-unicode"
translateType _ (FunctionHandleRepr _ _) =
  -- NOTE: function permissions translate to the SAW function, but the function
  -- handle itself has no SAW translation
  return $ mkPureTypeTrans0 ETrans_Fun
translateType _ (MaybeRepr _) =
  return $ error "translate: MaybeRepr"
translateType _ (VectorRepr _) =
  return $ error "translate: VectorRepr (can't map to Vec without size)"
translateType b (StructRepr tps) =
  fmap ETrans_Struct <$> combineCtxTranss <$> translateCtx b (mkCruCtx tps)
translateType _ (VariantRepr _) =
  return $ error "translate: VariantRepr"
translateType _ (ReferenceRepr _) =
  return $ error "translate: ReferenceRepr"
translateType _ (WordMapRepr _ _) =
  return $ error "translate: WordMapRepr"
translateType _ (StringMapRepr _) =
  return $ error "translate: StringMapRepr"
translateType _ (SymbolicArrayRepr _ _) =
  return $ error "translate: SymbolicArrayRepr"
translateType _ (SymbolicStructRepr _) =
  return $ error "translate: SymbolicStructRepr"

instance TransInfo info =>
         Translate info ctx (TypeRepr a) (PureTypeTrans (ExprTrans a)) where
  translate mb_tp = translateType False $ mbLift mb_tp

newtype ExprTypeTrans a = ExprTypeTrans (PureTypeTrans (ExprTrans a))

-- | Translate a context of types to a type translation using 'translateType'
translateCtx :: TransInfo info => Bool -> CruCtx tps ->
                TransM info ctx (RAssign ExprTypeTrans tps)
translateCtx b ctx =
  traverseRAssign (\tp -> ExprTypeTrans <$>
                          translateType b tp) (cruCtxToTypes ctx)

-- | Combine the translations of each type in a context into a single type
-- translation for the entire context
combineCtxTranss :: RAssign ExprTypeTrans tps ->
                    PureTypeTrans (ExprTransCtx tps)
combineCtxTranss MNil = mkPureTypeTrans0 MNil
combineCtxTranss (transs :>: ExprTypeTrans trans) =
  (:>:) <$> combineCtxTranss transs <*> trans

instance TransInfo info =>
         Translate info ctx (CruCtx as) (PureTypeTrans (ExprTransCtx as)) where
  translate mb_ctx =
    combineCtxTranss <$> translateCtx False (mbLift mb_ctx)

-- | Translate all types in a 'CruCtx' to their pure types, meaning specifically
-- that permissions and shapes are translated to types and not @LetRecType@s
translateCtxPure :: TransInfo info => CruCtx ctx ->
                    TransM info ctx' (PureTypeTrans (ExprTransCtx ctx))
translateCtxPure ctx = combineCtxTranss <$> translateCtx True ctx

-- | Translate all types in a Crucible context and lambda-abstract over them
lambdaExprCtx :: TransInfo info => CruCtx ctx -> TransM info ctx SpecTerm ->
                 TransM info RNil SpecTerm
lambdaExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  lambdaTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Translate all types in a Crucible context to pure types and lambda-abstract
-- over those types
lambdaExprCtxPure :: TransInfo info => CruCtx ctx -> TransM info ctx OpenTerm ->
                     TransM info RNil OpenTerm
lambdaExprCtxPure ctx m =
  translateCtxPure ctx >>= \tptrans ->
  lambdaPureTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Translate all types in a Crucible context and pi-abstract over them
piExprCtxPure :: TransInfo info => CruCtx ctx -> TransM info ctx OpenTerm ->
                 TransM info RNil OpenTerm
piExprCtxPure ctx m =
  translateCtxPure ctx >>= \tptrans ->
  piTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Translate all types in a Crucible context and pi-abstract over them,
-- building the resulting type as a @LetRecType@
piLRTExprCtx :: TransInfo info => CruCtx ctx ->
                TransM info ctx OpenTerm ->
                TransM info RNil OpenTerm
piLRTExprCtx ctx m =
  translateClosed ctx >>= \tptrans ->
  piLRTTransM "e" tptrans (\ectx -> inCtxTransM ectx m)

-- | Like 'piLRTExprCtx' but append the newly bound variables to the current
-- context, rather than running in the empty context
piLRTExprCtxApp :: TransInfo info => CruCtx ctx2 ->
                   TransM info (ctx :++: ctx2) OpenTerm ->
                   TransM info ctx OpenTerm
piLRTExprCtxApp ctx m =
  translateClosed ctx >>= \tptrans ->
  piLRTTransM "e" tptrans (\ectx -> inExtMultiTransM ectx m)


----------------------------------------------------------------------
-- * Translating Pure Expressions
----------------------------------------------------------------------

-- FIXME HERE: move these OpenTerm operations to OpenTerm.hs

-- | Build a bitvector literal from a 'BV' value
bvBVOpenTerm :: NatRepr w -> BV w -> OpenTerm
bvBVOpenTerm w bv = bvLitOpenTerm (BV.asBitsBE w bv)

bvNatOpenTerm :: Natural -> Natural -> OpenTerm
bvNatOpenTerm w n =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvNat")
  [natOpenTerm w, natOpenTerm (n `mod` 2 ^ w)]

bvAddOpenTerm :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvAddOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvAdd")
  [natOpenTerm n, x, y]

bvMulOpenTerm :: Natural -> OpenTerm -> OpenTerm -> OpenTerm
bvMulOpenTerm n x y =
  applyOpenTermMulti (globalOpenTerm "Prelude.bvMul")
  [natOpenTerm n, x, y]

bvSplitOpenTerm :: EndianForm -> OpenTerm -> OpenTerm -> OpenTerm ->
                   (OpenTerm, OpenTerm)
bvSplitOpenTerm BigEndian sz1 sz2 e =
  (applyGlobalOpenTerm "Prelude.take" [boolTypeOpenTerm, sz1, sz2, e],
   applyGlobalOpenTerm "Prelude.drop" [boolTypeOpenTerm, sz1, sz2, e])
bvSplitOpenTerm LittleEndian sz1 sz2 e =
  (applyGlobalOpenTerm "Prelude.drop" [boolTypeOpenTerm, sz2, sz1, e],
   applyGlobalOpenTerm "Prelude.take" [boolTypeOpenTerm, sz2, sz1, e])

bvConcatOpenTerm :: EndianForm -> OpenTerm -> OpenTerm ->
                    OpenTerm -> OpenTerm -> OpenTerm
bvConcatOpenTerm BigEndian sz1 sz2 e1 e2 =
  applyGlobalOpenTerm "Prelude.append" [sz1, sz2, boolTypeOpenTerm, e1, e2]
bvConcatOpenTerm LittleEndian sz1 sz2 e1 e2 =
  applyGlobalOpenTerm "Prelude.append" [sz2, sz1, boolTypeOpenTerm, e2, e1]

-- | Translate a variable to a 'Member' proof, raising an error if the variable
-- is unbound
translateVar :: Mb ctx (ExprVar a) -> Member ctx a
translateVar mb_x | Left memb <- mbNameBoundP mb_x = memb
translateVar _ = error "translateVar: unbound variable!"

-- | Get the 'TypeRepr' of an expression
mbExprType :: KnownRepr TypeRepr a => Mb ctx (PermExpr a) -> TypeRepr a
mbExprType _ = knownRepr

-- | Get the 'TypeRepr' of an expression
mbVarType :: KnownRepr TypeRepr a => Mb ctx (ExprVar a) -> TypeRepr a
mbVarType _ = knownRepr

-- | Get the 'TypeRepr' bound by a binding
mbBindingType :: KnownRepr TypeRepr tp => Mb ctx (Binding tp a) -> TypeRepr tp
mbBindingType _ = knownRepr


instance TransInfo info =>
         Translate info ctx (ExprVar a) (ExprTrans a) where
  translate mb_x = RL.get (translateVar mb_x) <$> infoCtx <$> ask

instance TransInfo info =>
         Translate info ctx (RAssign ExprVar as) (ExprTransCtx as) where
  translate mb_exprs = case mbMatch mb_exprs of
    [nuMP| MNil |] -> return MNil
    [nuMP| ns :>: n |] ->
      (:>:) <$> translate ns <*> translate n

instance TransInfo info =>
         Translate info ctx (PermExpr a) (ExprTrans a) where
  translate mb_tr = case mbMatch mb_tr of
    [nuMP| PExpr_Var x |] -> translate x
    [nuMP| PExpr_Unit |] -> return ETrans_Unit
    [nuMP| PExpr_Bool True |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.True"
    [nuMP| PExpr_Bool False |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.False"
    [nuMP| PExpr_Nat i |] ->
      return $ ETrans_Term $ natOpenTerm $ mbLift i
    [nuMP| PExpr_String str |] ->
      return $ ETrans_Term $ stringLitOpenTerm $ pack $ mbLift str
    [nuMP| PExpr_BV bvfactors@[] off |] ->
      let w = natRepr3 bvfactors in
      return $ ETrans_Term $ bvBVOpenTerm w $ mbLift off
    [nuMP| PExpr_BV bvfactors (BV.BV 0) |] ->
      let w = natVal3 bvfactors in
      ETrans_Term <$> foldr1 (bvAddOpenTerm w) <$> translate bvfactors
    [nuMP| PExpr_BV bvfactors off |] ->
      do let w = natRepr3 bvfactors
         bv_transs <- translate bvfactors
         return $ ETrans_Term $
           foldr (bvAddOpenTerm $ natValue w) (bvBVOpenTerm w $ mbLift off) bv_transs
    [nuMP| PExpr_Struct args |] ->
      ETrans_Struct <$> translate args
    [nuMP| PExpr_Always |] ->
      return ETrans_Lifetime
    [nuMP| PExpr_LLVMWord _ |] -> return ETrans_LLVM
    [nuMP| PExpr_LLVMOffset _ _ |] -> return ETrans_LLVM
    [nuMP| PExpr_Fun _ |] -> return ETrans_Fun
    [nuMP| PExpr_PermListNil |] -> return $ ETrans_Term unitTypeOpenTerm
    [nuMP| PExpr_PermListCons _ _ p l |] ->
      ETrans_Term <$> (pairTypeOpenTerm <$>
                       (typeDescLRT <$> typeTransTupleDesc <$> translate p) <*>
                       (translate1Pure l))
    [nuMP| PExpr_RWModality _ |] -> return ETrans_RWModality

    -- LLVM shapes are translated to types
    [nuMP| PExpr_EmptyShape |] -> return $ ETrans_Shape typeDescUnit
    [nuMP| PExpr_NamedShape _ _ nmsh args |] ->
      case mbMatch $ fmap namedShapeBody nmsh of
        [nuMP| DefinedShapeBody _ |] ->
          translate (mbMap2 unfoldNamedShape nmsh args)
        [nuMP| OpaqueShapeBody _ trans_id |] ->
          exprCtxPureTypeTerms <$> translate args >>= \case
          Just args_trans ->
            return $ ETrans_Shape $ TypeDescPure $
            applyOpenTermMulti (globalOpenTerm $ mbLift trans_id) args_trans
          Nothing ->
            panic "translate"
            ["Heapster cannot yet handle opaque shapes over impure types"]
        [nuMP| RecShapeBody _ trans_id _ |] ->
          exprCtxPureTypeTerms <$> translate args >>= \case
          Just args_trans ->
            return $ ETrans_Shape $ TypeDescPure $
            applyOpenTermMulti (globalOpenTerm $ mbLift trans_id) args_trans
          Nothing ->
            panic "translate"
            ["Heapster cannot yet handle recursive shapes over impure types"]
    [nuMP| PExpr_EqShape _ _ |] -> return $ ETrans_Shape typeDescUnit
    [nuMP| PExpr_PtrShape _ _ sh |] -> translate sh
    [nuMP| PExpr_FieldShape fsh |] ->
      ETrans_Shape <$> tupleOfTypeDescs <$> translate fsh
    [nuMP| PExpr_ArrayShape mb_len _ mb_sh |] ->
      do let w = natVal4 mb_len
         let w_term = natOpenTerm w
         len_term <- translate1Pure mb_len
         elem_d <- translateShape mb_sh
         return $ ETrans_Shape $ bvVecTypeDesc w_term len_term elem_d
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      ETrans_Shape <$> (typeDescPair <$> translateShape sh1
                       <*> translateShape sh2)
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      ETrans_Shape <$> (typeDescEither
                        <$> translateShape sh1 <*> translateShape sh2)
    [nuMP| PExpr_ExShape mb_sh |] ->
      do tp_trans <- translate $ fmap bindingType mb_sh
         ETrans_Shape <$>
           (sigmaTypeTransM "x_exsh" tp_trans
            (hasPureTrans $ mbCombine RL.typeCtxProxies mb_sh) $ \e ->
             inExtTransM e (translateShape $ mbCombine RL.typeCtxProxies mb_sh))
    [nuMP| PExpr_FalseShape |] ->
      return $ ETrans_Shape $ TypeDescPure $ globalOpenTerm "Prelude.FalseProp"

    [nuMP| PExpr_ValPerm p |] ->
      ETrans_Perm <$> typeTransTupleDesc <$> translate p

-- LLVM field shapes translate to the types that the permission they contain
-- translates to
instance TransInfo info =>
         Translate info ctx (LLVMFieldShape w) [TypeDesc] where
  translate (mbMatch -> [nuMP| LLVMFieldShape p |]) =
    typeTransDescs <$> translate p

instance TransInfo info =>
         Translate info ctx (PermExprs as) (ExprTransCtx as) where
  translate mb_exprs = case mbMatch mb_exprs of
    [nuMP| PExprs_Nil |] -> return MNil
    [nuMP| PExprs_Cons es e |] ->
      (:>:) <$> translate es <*> translate e

instance TransInfo info => Translate info ctx (BVFactor w) OpenTerm where
  translate mb_f = case mbMatch mb_f of
    [nuMP| BVFactor (BV.BV 1) x |] -> translate1Pure (fmap PExpr_Var x)
    [nuMP| BVFactor i x |] ->
      let w = natRepr4 x in
      bvMulOpenTerm (natValue w) (bvBVOpenTerm w $ mbLift i) <$>
      translate1Pure (fmap PExpr_Var x)

translateShape :: (TransInfo info, HasCallStack) =>
                  Mb ctx (PermExpr (LLVMShapeType w)) ->
                  TransM info ctx TypeDesc
translateShape mb_e = unETransShape <$> translate mb_e

instance HasPureTrans (PermExpr a) where
  hasPureTrans mb_e = case mbMatch mb_e of
    [nuMP| PExpr_Var _ |] ->
      -- Variables of shape or permission type always have to quantify over
      -- arbitrary @LetRecType@s, and so are considered impure
      -- FIXME: should be type-based; only shape or perm variable are impure!
      False
    [nuMP| PExpr_Struct mb_es |] -> hasPureTrans mb_es
    [nuMP| PExpr_PermListCons _ _ p rest |] ->
      hasPureTrans p && hasPureTrans rest
    [nuMP| PExpr_EmptyShape |] -> True
    [nuMP| PExpr_NamedShape _ _ nmsh args |] ->
      case mbMatch $ fmap namedShapeBody nmsh of
        [nuMP| DefinedShapeBody _ |] ->
          hasPureTrans (mbMap2 unfoldNamedShape nmsh args)
        [nuMP| OpaqueShapeBody _ _ |] -> hasPureTrans args
        [nuMP| RecShapeBody _ _ _ |] -> hasPureTrans args
    [nuMP| PExpr_EqShape _ _ |] -> True
    [nuMP| PExpr_PtrShape _ _ sh |] -> hasPureTrans sh
    [nuMP| PExpr_FieldShape fsh |] -> hasPureTrans fsh
    [nuMP| PExpr_ArrayShape _ _ sh |] -> hasPureTrans sh
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      hasPureTrans sh1 && hasPureTrans sh2
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      hasPureTrans sh1 && hasPureTrans sh2
    [nuMP| PExpr_ExShape mb_sh |] ->
      hasPureTrans $ mbCombine RL.typeCtxProxies mb_sh
    [nuMP| PExpr_FalseShape |] -> True
    [nuMP| PExpr_ValPerm p |] -> hasPureTrans p
    [nuMP| _ |] -> True

instance HasPureTrans (PermExprs as) where
  hasPureTrans e = case mbMatch e of
    [nuMP| MNil |] -> True
    [nuMP| es :>: e' |] -> hasPureTrans es && hasPureTrans e'

instance HasPureTrans (LLVMFieldShape w) where
  hasPureTrans (mbMatch -> [nuMP| LLVMFieldShape p |]) = hasPureTrans p


----------------------------------------------------------------------
-- * Translating Permissions to Types
----------------------------------------------------------------------

-- | The result of translating a "proof element" of a permission of type
-- @'ValuePerm' a@. The idea here is that, for a permission implication or typed
-- statement that consumes or emits permission @p@, the translation consumes or
-- emits an element of the SAW type @'translate' p@.
--
-- Another way to look at a @'PermTrans'@ for permission @p@ is that it is a
-- partially static representation (in the sense of the partial evaluation
-- literature) of a SAW expression of type @'translate' p@. Note that we do
-- not include special representations for disjunctions, existentials, or
-- recursive permissions, however, because our type-checker does not
-- generally introduce these forms as intermediate values.
data PermTrans (ctx :: RList CrucibleType) (a :: CrucibleType) where
  -- | An @eq(e)@ permission has no computational content
  PTrans_Eq :: Mb ctx (PermExpr a) -> PermTrans ctx a

  -- | A conjuction of atomic permission translations
  PTrans_Conj :: [AtomicPermTrans ctx a] -> PermTrans ctx a

  -- | The translation of a defined permission is a wrapper around the
  -- translation of what it is defined as
  PTrans_Defined :: NamedPermName (DefinedSort b) args a ->
                    Mb ctx (PermExprs args) -> Mb ctx (PermOffset a) ->
                    PermTrans ctx a -> PermTrans ctx a

  -- | The translation for disjunctive, existential, and named permissions
  PTrans_Term :: Mb ctx (ValuePerm a) -> SpecTerm -> PermTrans ctx a


-- | The 'PermTrans' type for atomic permissions
data AtomicPermTrans ctx a where

  -- | The translation of an LLVM field permission is just the translation of
  -- its contents
  APTrans_LLVMField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                       Mb ctx (LLVMFieldPerm w sz) ->
                       PermTrans ctx (LLVMPointerType sz) ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM array permisions are translated to an 'LLVMArrayPermTrans'
  APTrans_LLVMArray :: (1 <= w, KnownNat w) =>
                       LLVMArrayPermTrans ctx w ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | The translation of an LLVM block permission is an element of the
  -- translation of its shape to a type
  APTrans_LLVMBlock :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMBlockPerm w) -> SpecTerm ->
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM free permissions have no computational content
  APTrans_LLVMFree :: (1 <= w, KnownNat w) =>
                      Mb ctx (PermExpr (BVType w)) ->
                      AtomicPermTrans ctx (LLVMPointerType w)

  -- | LLVM function pointer permissions have the same computational content as
  -- a function permission
  APTrans_LLVMFunPtr :: (1 <= w, KnownNat w) =>
                        TypeRepr (FunctionHandleType cargs ret) ->
                        PermTrans ctx (FunctionHandleType cargs ret) ->
                        AtomicPermTrans ctx (LLVMPointerType w)

  -- | IsLLVMPtr permissions have no computational content
  APTrans_IsLLVMPtr :: (1 <= w, KnownNat w) =>
                       AtomicPermTrans ctx (LLVMPointerType w)

  -- | The translation of an LLVMBlockShape permission is an element of the
  -- translation of its shape to a type
  APTrans_LLVMBlockShape :: (1 <= w, KnownNat w) =>
                            Mb ctx (PermExpr (LLVMShapeType w)) -> SpecTerm ->
                            AtomicPermTrans ctx (LLVMBlockType w)

  -- | Perm_NamedConj permissions are a permission + a term
  APTrans_NamedConj :: NameSortIsConj ns ~ 'True =>
                       NamedPermName ns args a -> Mb ctx (PermExprs args) ->
                       Mb ctx (PermOffset a) -> SpecTerm ->
                       AtomicPermTrans ctx a

  -- | Defined Perm_NamedConj permissions are just a wrapper around the
  -- translation of the permission definition
  APTrans_DefinedNamedConj :: NamedPermName (DefinedSort 'True) args a ->
                              Mb ctx (PermExprs args) ->
                              Mb ctx (PermOffset a) ->
                              PermTrans ctx a ->
                              AtomicPermTrans ctx a

  -- | LLVM frame permissions have no computational content
  APTrans_LLVMFrame :: (1 <= w, KnownNat w) =>
                       Mb ctx (LLVMFramePerm w) ->
                       AtomicPermTrans ctx (LLVMFrameType w)

  -- | @lowned@ permissions translate to a monadic function from (the
  -- translation of) the input permissions to the output permissions
  APTrans_LOwned ::
    Mb ctx [PermExpr LifetimeType] -> CruCtx ps_in -> CruCtx ps_out ->
    Mb ctx (ExprPerms ps_in) -> Mb ctx (ExprPerms ps_out) ->
    LOwnedTrans ctx ps_extra ps_in ps_out ->
    AtomicPermTrans ctx LifetimeType

  -- | Simple @lowned@ permissions have no translation, because they represent
  -- @lowned@ permissions whose translations are just the identity function
  APTrans_LOwnedSimple :: CruCtx ps -> Mb ctx (ExprPerms ps) ->
                          AtomicPermTrans ctx LifetimeType

  -- | LCurrent permissions have no computational content
  APTrans_LCurrent :: Mb ctx (PermExpr LifetimeType) ->
                      AtomicPermTrans ctx LifetimeType

  -- | LFinished permissions have no computational content
  APTrans_LFinished :: AtomicPermTrans ctx LifetimeType

  -- | The translation of a struct permission is sequence of the translations of
  -- the permissions in the struct permission
  APTrans_Struct :: PermTransCtx ctx (CtxToRList args) ->
                    AtomicPermTrans ctx (StructType args)

  -- | The translation of functional permission is a SAW term of closure type
  APTrans_Fun :: Mb ctx (FunPerm ghosts (CtxToRList cargs) gouts ret) ->
                 FunTransTerm ->
                 AtomicPermTrans ctx (FunctionHandleType cargs ret)

  -- | Propositional permissions are represented by a SAW term
  APTrans_BVProp :: (1 <= w, KnownNat w) => BVPropTrans ctx w ->
                    AtomicPermTrans ctx (LLVMPointerType w)

  -- | Any permissions have no SAW terms
  APTrans_Any :: AtomicPermTrans ctx a


-- | The translation of a proof of a 'BVProp'
data BVPropTrans ctx w = BVPropTrans (Mb ctx (BVProp w)) SpecTerm

-- | Build the translation of a 'BVProp' permission from a proof of it
bvPropPerm :: (1 <= w, KnownNat w) => BVPropTrans ctx w ->
              PermTrans ctx (LLVMPointerType w)
bvPropPerm prop = PTrans_Conj [APTrans_BVProp prop]

-- | The translation of a 'BVRange' is the translation of its two elements
data BVRangeTrans ctx w =
  BVRangeTrans (Mb ctx (BVRange w))
  (ExprTrans (BVType w)) (ExprTrans (BVType w))

-- | Extract the translation of the offset from the translation of a 'BVRange'
bvRangeTransOff :: BVRangeTrans ctx w -> ExprTrans (BVType w)
bvRangeTransOff (BVRangeTrans _ off _) = off

-- | Extract the translation of the length from the translation of a 'BVRange'
bvRangeTransLen :: BVRangeTrans ctx w -> ExprTrans (BVType w)
bvRangeTransLen (BVRangeTrans _ _ len) = len

-- | The translation of an LLVM array permission is a SAW term of @BVVec@ type,
-- along with a SAW term for its length as a bitvector and the type translation
-- for a @memblock@ permission to its head cell, which can be offset to get a
-- @memblock@ permission for any of its cells.
data LLVMArrayPermTrans ctx w = LLVMArrayPermTrans {
  llvmArrayTransPerm :: Mb ctx (LLVMArrayPerm w),
  llvmArrayTransLen :: OpenTerm,
  llvmArrayTransHeadCell ::
      TypeTrans 'False (AtomicPermTrans ctx (LLVMPointerType w)),
  -- llvmArrayTransBorrows :: [LLVMArrayBorrowTrans ctx w],
  llvmArrayTransTerm :: SpecTerm
  }

-- | Get the SAW type of the cells of the translation of an array permission
llvmArrayTransCellType :: LLVMArrayPermTrans ctx w -> SpecTerm
llvmArrayTransCellType = typeTransType1Imp . llvmArrayTransHeadCell


-- | The translation of an 'LLVMArrayBorrow' is an element / proof of the
-- translation of the the 'BVProp' returned by 'llvmArrayBorrowInArrayBase'
{-
data LLVMArrayBorrowTrans ctx w =
  LLVMArrayBorrowTrans
  { llvmArrayBorrowTransBorrow :: Mb ctx (LLVMArrayBorrow w),
    llvmArrayBorrowTransProps :: [BVPropTrans ctx w] }
-}

-- | FIXME HERE NOW: document all of this!
data LOwnedInfo ps ctx =
  LOwnedInfo { lownedInfoECtx :: ExprTransCtx ctx,
               lownedInfoPCtx :: PermTransCtx ctx ps,
               lownedInfoPVars :: RAssign (Member ctx) ps,
               lownedInfoRetType :: TypeDesc }

-- | Convert an 'ImpTransInfo' to an 'LOwnedInfo'
impInfoToLOwned :: ImpTransInfo ext blocks tops rets ps ctx -> LOwnedInfo ps ctx
impInfoToLOwned (ImpTransInfo {..}) =
  LOwnedInfo { lownedInfoECtx = itiExprCtx, lownedInfoPCtx = itiPermStack,
               lownedInfoPVars = itiPermStackVars,
               lownedInfoRetType = itiReturnType }

-- | Convert an 'LOwnedInfo' to an 'ImpTransInfo' using an existing 'ImpTransInfo'
lownedInfoToImp :: LOwnedInfo ps ctx ->
                   ImpTransInfo ext blocks tops rets ps' ctx' ->
                   ImpTransInfo ext blocks tops rets ps ctx
lownedInfoToImp (LOwnedInfo {..}) (ImpTransInfo {..}) =
  ImpTransInfo { itiExprCtx = lownedInfoECtx, itiPermStack = lownedInfoPCtx,
                 itiPermStackVars = lownedInfoPVars,
                 itiPermCtx = RL.map (const PTrans_True) lownedInfoECtx,
                 itiReturnType = lownedInfoRetType, .. }

loInfoSetPerms :: PermTransCtx ctx ps' -> RAssign (Member ctx) ps' ->
                  LOwnedInfo ps ctx -> LOwnedInfo ps' ctx
loInfoSetPerms ps' vars' (LOwnedInfo {..}) =
  LOwnedInfo { lownedInfoPCtx = ps', lownedInfoPVars = vars', ..}

loInfoSplit :: prx ps1 -> RAssign any ps2 ->
               LOwnedInfo (ps1 :++: ps2) ctx ->
               (LOwnedInfo ps1 ctx, LOwnedInfo ps2 ctx)
loInfoSplit (_ :: prx ps1) prx2 (LOwnedInfo {..}) =
  let prx1 :: Proxy ps1 = Proxy
      (ps1, ps2) = RL.split prx1 prx2 lownedInfoPCtx
      (vars1, vars2) = RL.split prx1 prx2 lownedInfoPVars in
  (LOwnedInfo { lownedInfoPCtx = ps1, lownedInfoPVars = vars1, .. },
   LOwnedInfo { lownedInfoPCtx = ps2, lownedInfoPVars = vars2, .. })

loInfoAppend :: LOwnedInfo ps1 ctx -> LOwnedInfo ps2 ctx ->
                LOwnedInfo (ps1 :++: ps2) ctx
loInfoAppend info1 info2 =
  LOwnedInfo { lownedInfoECtx = lownedInfoECtx info1
             , lownedInfoPCtx =
                 RL.append (lownedInfoPCtx info1) (lownedInfoPCtx info2)
             , lownedInfoPVars =
                 RL.append (lownedInfoPVars info1) (lownedInfoPVars info2)
             , lownedInfoRetType = lownedInfoRetType info1 }

-- | An extension of type context @ctx1@ to @ctx2@, which is
-- just an 'ExprTransCtx' for the suffix @ctx3@ such that @ctx1:++:ctx3 = ctx2@
data ExprCtxExt ctx1 ctx2 where
  ExprCtxExt :: ExprTransCtx ctx3 -> ExprCtxExt ctx1 (ctx1 :++: ctx3)

-- | The reflexive context extension, proving that any context extends itself
reflExprCtxExt :: ExprCtxExt ctx ctx
reflExprCtxExt = ExprCtxExt MNil

-- | Transitively combine two context extensions
transExprCtxExt :: ExprCtxExt ctx1 ctx2 -> ExprCtxExt ctx2 ctx3 ->
                   ExprCtxExt ctx1 ctx3
transExprCtxExt ((ExprCtxExt ectx2')
                 :: ExprCtxExt ctx1 ctx2) (ExprCtxExt ectx3')
  | Refl <- RL.appendAssoc (Proxy :: Proxy ctx1) ectx2' ectx3'
  = ExprCtxExt (RL.append ectx2' ectx3')

extMbExt :: ExprCtxExt ctx1 ctx2 -> Mb ctx1 a -> Mb ctx2 a
extMbExt (ExprCtxExt ctx2) = extMbAny ctx2

{- FIXME: keeping this in case we need it later
-- | Un-extend the left-hand context of an expression context extension
extExprCtxExt :: ExprTrans tp -> ExprCtxExt (ctx1 :> tp) ctx2 ->
                 ExprCtxExt ctx1 ctx2
extExprCtxExt etrans ((ExprCtxExt ctx3) :: ExprCtxExt (ctx1 :> tp) ctx2) =
  case RL.appendRNilConsEq (Proxy :: Proxy ctx1) etrans ctx3 of
    Refl -> ExprCtxExt (RL.append (MNil :>: etrans) ctx3)
-}

extExprTransCtx :: ExprCtxExt ctx1 ctx2 -> ExprTransCtx ctx1 ->
                   ExprTransCtx ctx2
extExprTransCtx (ExprCtxExt ectx2) ectx1 = RL.append ectx1 ectx2

unextExprTransCtx :: ExprCtxExt ctx1 ctx2 -> ExprTransCtx ctx2 ->
                     ExprTransCtx ctx1
unextExprTransCtx ((ExprCtxExt ectx3) :: ExprCtxExt ctx1 ctx2) ectx2 =
  fst $ RL.split (Proxy :: Proxy ctx1) ectx3 ectx2

-- | Extend the context of a permission translation using an 'ExprCtxExt'
extPermTransExt :: ExprCtxExt ctx1 ctx2 -> PermTrans ctx1 a ->
                   PermTrans ctx2 a
extPermTransExt (ExprCtxExt ectx) ptrans = extPermTransMulti ectx ptrans

-- | Extend the context of a permission translation context using an
-- 'ExprCtxExt'
extPermTransCtxExt :: ExprCtxExt ctx1 ctx2 -> PermTransCtx ctx1 ps ->
                      PermTransCtx ctx2 ps
extPermTransCtxExt cext = RL.map (extPermTransExt cext)

extLOwnedInfoExt :: ExprCtxExt ctx1 ctx2 -> LOwnedInfo ps ctx1 ->
                    LOwnedInfo ps ctx2
extLOwnedInfoExt cext@(ExprCtxExt ectx3) (LOwnedInfo {..}) =
  LOwnedInfo { lownedInfoECtx = extExprTransCtx cext lownedInfoECtx,
               lownedInfoPCtx = extPermTransCtxExt cext lownedInfoPCtx,
               lownedInfoPVars = RL.map (weakenMemberR ectx3) lownedInfoPVars,
               .. }


-- | FIXME HERE NOW: docs; explain that it's as if the input LOwnedInfo is
-- relative to ctx_in and the output is relative to ctx_out except this ensures
-- that those are extensions of what they are supposed to be
newtype LOwnedTransM ps_in ps_out ctx a =
  LOwnedTransM {
  runLOwnedTransM ::
      forall ctx_in. ExprCtxExt ctx ctx_in -> LOwnedInfo ps_in ctx_in ->
      (forall ctx_out. ExprCtxExt ctx_in ctx_out -> LOwnedInfo ps_out ctx_out ->
       a -> SpecTerm) ->
      SpecTerm }

(>>>=) :: LOwnedTransM ps_in ps' ctx a -> (a -> LOwnedTransM ps' ps_out ctx b) ->
          LOwnedTransM ps_in ps_out ctx b
m >>>= f = LOwnedTransM $ \cext s1 k ->
  runLOwnedTransM m cext s1 $ \cext' s2 x ->
  runLOwnedTransM (f x) (transExprCtxExt cext cext') s2 $ \cext'' ->
  k (transExprCtxExt cext' cext'')

(>>>) :: LOwnedTransM ps_in ps' ctx a -> LOwnedTransM ps' ps_out ctx b ->
         LOwnedTransM ps_in ps_out ctx b
m1 >>> m2 = m1 >>>= \_ -> m2

instance Functor (LOwnedTransM ps_in ps_out ctx) where
  fmap f m = m >>>= \x -> return (f x)

instance Applicative (LOwnedTransM ps ps ctx) where
  pure x = LOwnedTransM $ \_ s k -> k reflExprCtxExt s x
  (<*>) = Monad.ap

instance Monad (LOwnedTransM ps ps ctx) where
  (>>=) = (>>>=)

gput :: LOwnedInfo ps_out ctx -> LOwnedTransM ps_in ps_out ctx ()
gput loInfo =
  LOwnedTransM $ \cext _ k -> k reflExprCtxExt (extLOwnedInfoExt cext loInfo) ()

{-
data ExtLOwnedInfo ps ctx where
  ExtLOwnedInfo :: ExprCtxExt ctx ctx' -> LOwnedInfo ps ctx' ->
                   ExtLOwnedInfo ps ctx

instance ps_in ~ ps_out =>
         MonadState (ExtLOwnedInfo ps_in ctx) (LOwnedTransM ps_in ps_out ctx) where
  get = LOwnedTransM $ \cext s k -> k reflExprCtxExt s (ExtLOwnedInfo cext s)
  put = gput
-}

ggetting :: (forall ctx'. ExprCtxExt ctx ctx' ->
             LOwnedInfo ps_in ctx' -> LOwnedTransM ps_in ps_out ctx' a) ->
            LOwnedTransM ps_in ps_out ctx a
ggetting f =
  LOwnedTransM $ \cext s k ->
  runLOwnedTransM (f cext s) reflExprCtxExt s $ \cext' ->
  k cext'

gmodify :: (forall ctx'. ExprCtxExt ctx ctx' ->
            LOwnedInfo ps_in ctx' -> LOwnedInfo ps_out ctx') ->
           LOwnedTransM ps_in ps_out ctx ()
gmodify f = ggetting $ \cext loInfo -> gput (f cext loInfo)

extLOwnedTransM :: ExprCtxExt ctx ctx' -> LOwnedTransM ps_in ps_out ctx a ->
                   LOwnedTransM ps_in ps_out ctx' a
extLOwnedTransM cext m =
  LOwnedTransM $ \cext' -> runLOwnedTransM m (transExprCtxExt cext cext')

type LOwnedTransTerm ctx ps_in ps_out = LOwnedTransM ps_in ps_out ctx ()

mkLOwnedTransTermFromTerm :: ExprTransCtx ctx -> RelPermsTypeTrans ctx ps_in ->
                             RelPermsTypeTrans ctx ps_out ->
                             RAssign (Member ctx) ps_out -> SpecTerm ->
                             LOwnedTransTerm ctx ps_in ps_out
mkLOwnedTransTermFromTerm ectx ttr_inF ttr_outF vars_out t =
  LOwnedTransM $ \(ExprCtxExt ectx') loInfo k ->
  let lrt = piExprPermLRT (exprCtxType ectx) ttr_inF ttr_outF
      t_app = applyCallClosSpecTerm lrt t (transTerms $ lownedInfoPCtx loInfo)
      t_ret_trans = tupleTypeTrans $ ttr_outF ectx
      t_ret_tp = typeTransTupleType $ ttr_outF ectx in
  bindSpecTerm t_ret_tp (typeDescType $ lownedInfoRetType loInfo) t_app $
  lambdaTermLike "lowned_ret" t_ret_tp $ \lowned_ret ->
  let pctx_out' =
        extPermTransCtxMulti ectx' $ typeTransF t_ret_trans [lowned_ret]
      vars_out' = RL.map (weakenMemberR ectx') vars_out in
  k reflExprCtxExt (loInfoSetPerms pctx_out' vars_out' loInfo) ()

lownedTransTermTerm :: PureTypeTrans (ExprTransCtx ctx) ->
                       RAssign (Member ctx) ps_in ->
                       RelPermsTypeTrans ctx ps_in ->
                       RelPermsTypeTrans ctx ps_out ->
                       LOwnedTransTerm ctx ps_in ps_out -> SpecTerm
lownedTransTermTerm ectx vars_in ps_inF ps_outF t =
  lambdaTrans "e" ectx $ \exprs ->
  lambdaTrans "p" (ps_inF exprs) $ \ps_in ->
  let ret_tp = typeTransTupleDesc $ ps_outF exprs in
  let loInfo =
        LOwnedInfo { lownedInfoECtx = exprs, lownedInfoPCtx = ps_in,
                     lownedInfoPVars = vars_in, lownedInfoRetType = ret_tp } in
  runLOwnedTransM t reflExprCtxExt loInfo $ \_ loInfo_out () ->
  transTupleTerm (lownedInfoPCtx loInfo_out)

extLOwnedTransTerm :: ExprTransCtx ctx2 ->
                      LOwnedTransTerm ctx1 ps_in ps_out ->
                      LOwnedTransTerm (ctx1 :++: ctx2) ps_in ps_out
extLOwnedTransTerm ectx2 = extLOwnedTransM (ExprCtxExt ectx2)

-- | Build an 'LOwnedTransTerm' that acts as the identity function on the SAW
-- core terms in the permissions, using the supplied permission translation for
-- the output permissions, which must have the same SAW core terms as the input
-- permissions (or the identity translation would be ill-typed)
idLOwnedTransTerm :: RelPermsTypeTrans ctx ps_out ->
                     RAssign (Member ctx) ps_out ->
                     LOwnedTransTerm ctx ps_in ps_out
idLOwnedTransTerm ttr_outF vars_out =
  gmodify $ \(ExprCtxExt ectx') loInfo ->
  let ttr_out =
        extRelPermsTypeTransMulti ectx' ttr_outF $ lownedInfoECtx loInfo
      vars_out' = RL.map (weakenMemberR ectx') vars_out in
  loInfo { lownedInfoPVars = vars_out',
           lownedInfoPCtx =
             typeTransF ttr_out (transTerms (lownedInfoPCtx loInfo)) }

weakenLOwnedTransTerm :: ImpTypeTrans (PermTrans ctx tp) ->
                         LOwnedTransTerm ctx ps_in ps_out ->
                         LOwnedTransTerm ctx (ps_in :> tp) (ps_out :> tp)
weakenLOwnedTransTerm ttr_out t =
  ggetting $ \cext info_top ->
  let (info_ps_in, info_tp) = loInfoSplit Proxy (MNil :>: Proxy) info_top in
  gput info_ps_in >>>
  extLOwnedTransM cext t >>>
  gmodify (\cext' info' ->
            loInfoAppend info' $ extLOwnedInfoExt cext' $
            info_tp { lownedInfoPCtx =
                        (MNil :>:) $ extPermTransExt cext $ typeTransF ttr_out $
                        transTerms $ lownedInfoPCtx info_tp })

-- | Combine 'LOwnedTransTerm's for the 'SImpl_MapLifetime' rule
mapLtLOwnedTransTerm ::
  prx ps_extra1 -> RAssign any1 ps_extra2 -> RAssign any2 ps_in ->
  LOwnedTransTerm ctx (ps_extra1 :++: ps_in) ps_mid ->
  LOwnedTransTerm ctx (ps_extra2 :++: ps_mid) ps_out ->
  LOwnedTransTerm ctx ((ps_extra1 :++: ps_extra2) :++: ps_in) ps_out
mapLtLOwnedTransTerm prx_extra1 prx_extra2 prx_in t1 t2 =
  ggetting $ \cext info_extra_in ->
  let (info_extra, info_in) = loInfoSplit Proxy prx_in info_extra_in
      (info_extra1, info_extra2) =
        loInfoSplit prx_extra1 prx_extra2 info_extra in
  gput (loInfoAppend info_extra1 info_in) >>>
  extLOwnedTransM cext t1 >>>
  gmodify (\cext' info_out ->
            loInfoAppend (extLOwnedInfoExt cext' info_extra2) info_out) >>>
  extLOwnedTransM cext t2

-- | The translation of an @lowned@ permission
data LOwnedTrans ctx ps_extra ps_in ps_out =
  LOwnedTrans {
  lotrECtx :: ExprTransCtx ctx,
  lotrPsExtra :: PermTransCtx ctx ps_extra,
  lotrVarsExtra :: RAssign (Member ctx) ps_extra,
  lotrRelTransIn :: RelPermsTypeTrans ctx ps_in,
  lotrRelTransOut :: RelPermsTypeTrans ctx ps_out,
  lotrRelTransExtra :: RelPermsTypeTrans ctx ps_extra,
  lotrTerm :: LOwnedTransTerm ctx (ps_extra :++: ps_in) ps_out }

-- | Build an initial 'LOwnedTrans' with an empty @ps_extra@
mkLOwnedTrans :: ExprTransCtx ctx -> RelPermsTypeTrans ctx ps_in ->
                 RelPermsTypeTrans ctx ps_out -> RAssign (Member ctx) ps_out ->
                 SpecTerm -> LOwnedTrans ctx RNil ps_in ps_out
mkLOwnedTrans ectx ps_inF ps_outF vars_out t =
  LOwnedTrans ectx MNil MNil ps_inF ps_outF (const $ pure MNil)
  (mkLOwnedTransTermFromTerm ectx (preNilRelPermsTypeTrans ps_inF)
   ps_outF vars_out t)

-- | Build an initial 'LOwnedTrans' with an empty @ps_extra@ and an identity
-- function on SAW core terms
mkLOwnedTransId :: ExprTransCtx ctx -> RelPermsTypeTrans ctx ps ->
                   RelPermsTypeTrans ctx ps -> RAssign (Member ctx) ps ->
                   LOwnedTrans ctx RNil ps ps
mkLOwnedTransId ectx ps_inF ps_outF vars_out =
  LOwnedTrans ectx MNil MNil ps_inF ps_outF (const $ pure MNil)
  (idLOwnedTransTerm ps_outF vars_out)

-- | Extend the context of an 'LOwnedTrans'
extLOwnedTransMulti :: ExprTransCtx ctx2 ->
                       LOwnedTrans ctx1 ps_extra ps_in ps_out ->
                       LOwnedTrans (ctx1 :++: ctx2) ps_extra ps_in ps_out
extLOwnedTransMulti ectx2 (LOwnedTrans ectx1 ps_extra vars_extra ptrans_in
                           ptrans_out ptrans_extra t) =
  LOwnedTrans
  (RL.append ectx1 ectx2) (extPermTransCtxMulti ectx2 ps_extra)
  (RL.map (weakenMemberR ectx2) vars_extra)
  (extRelPermsTypeTransMulti ectx2 ptrans_in)
  (extRelPermsTypeTransMulti ectx2 ptrans_out)
  (extRelPermsTypeTransMulti ectx2 ptrans_extra)
  (extLOwnedTransTerm ectx2 t)

weakenLOwnedTrans ::
  Rel1PermTypeTrans ctx tp ->
  Rel1PermTypeTrans ctx tp ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  LOwnedTrans ctx ps_extra (ps_in :> tp) (ps_out :> tp)
weakenLOwnedTrans tp_in tp_out (LOwnedTrans {..}) =
  LOwnedTrans { lotrRelTransIn = app1RelPermsTypeTrans lotrRelTransIn tp_in,
                lotrRelTransOut = app1RelPermsTypeTrans lotrRelTransOut tp_out,
                lotrTerm = weakenLOwnedTransTerm (tp_out lotrECtx) lotrTerm, .. }

-- | Convert an 'LOwnedTrans' to a closure that gets added to the list of
-- closures for the current spec definition, and partially apply that closure to
-- the current expression context and its @ps_extra@ terms
lownedTransTerm :: Mb ctx (ExprPerms ps_in) ->
                   LOwnedTrans ctx ps_extra ps_in ps_out -> SpecTerm
lownedTransTerm (mbExprPermsMembers ->
                 Just vars_in) (LOwnedTrans
                                ectx ps_extra vars_extra
                                tps_in tps_out tps_extra lott) =
  let etps = exprCtxType ectx
      tps_extra_in = appRelPermsTypeTrans tps_extra tps_in
      vars_extra_in = RL.append vars_extra vars_in
      lrt = piExprPermLRT etps tps_extra_in tps_out
      fun_tm =
        lownedTransTermTerm etps vars_extra_in tps_extra_in tps_out lott in
  applyClosSpecTerm lrt (mkFreshClosSpecTerm lrt (const fun_tm))
  (transTerms ectx ++ transTerms ps_extra)
lownedTransTerm _ _ =
  failTermLike "FIXME HERE NOW: write this error message"

-- | Apply the 'SImpl_MapLifetime' rule to an 'LOwnedTrans'
mapLtLOwnedTrans ::
  PermTransCtx ctx ps1 -> RAssign (Member ctx) ps1 ->
  RelPermsTypeTrans ctx ps1 ->
  PermTransCtx ctx ps2 -> RAssign (Member ctx) ps2 ->
  RelPermsTypeTrans ctx ps2 ->
  RAssign any ps_in' -> RelPermsTypeTrans ctx ps_in' ->
  RelPermsTypeTrans ctx ps_out' ->
  LOwnedTransTerm ctx (ps1 :++: ps_in') ps_in ->
  LOwnedTransTerm ctx (ps2 :++: ps_out) ps_out' ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  LOwnedTrans ctx ((ps1 :++: ps_extra) :++: ps2) ps_in' ps_out'
mapLtLOwnedTrans pctx1 vars1 ttr1F pctx2 vars2 ttr2F
  prx_in' ttr_inF' ttr_outF' t1 t2
  (LOwnedTrans {..}) =
  LOwnedTrans
  { lotrECtx = lotrECtx
  , lotrPsExtra = RL.append (RL.append pctx1 lotrPsExtra) pctx2
  , lotrVarsExtra = RL.append (RL.append vars1 lotrVarsExtra) vars2
  , lotrRelTransIn = ttr_inF' , lotrRelTransOut = ttr_outF'
  , lotrRelTransExtra =
      appRelPermsTypeTrans (appRelPermsTypeTrans ttr1F lotrRelTransExtra) ttr2F
  , lotrTerm =
      mapLtLOwnedTransTerm (RL.append pctx1 lotrPsExtra) pctx2 prx_in'
      (mapLtLOwnedTransTerm pctx1 lotrPsExtra prx_in' t1 lotrTerm)
      t2
  }


-- | The translation of a function permission to a term
data FunTransTerm
     -- | A monadic function represented as a closure, i.e., a term of type
     -- @LRTClos stk lrt@, where @stk@ is the current stack and @lrt@ is the
     -- supplied 'OpenTerm'
  = FunTransClos OpenTerm SpecTerm
    -- | A monadic function represented as a monadic function, i.e., a term of
    -- type @SpecFun E stk lrt@, where @E@ is the current event type, @stk@ is
    -- the current stack, and @lrt@ is the supplied 'OpenTerm'
  | FunTransFun OpenTerm SpecTerm

-- | Convert a 'FunTransTerm' to a closure, i.e., term of type @LRTClos stk lrt@
funTransTermToClos :: FunTransTerm -> SpecTerm
funTransTermToClos (FunTransClos _ clos) = clos
funTransTermToClos (FunTransFun lrt f) = mkFreshClosSpecTerm lrt (const f)

-- | Apply a 'FunTransTerm' to a list of arguments
applyFunTransTerm :: FunTransTerm -> [SpecTerm] -> SpecTerm
applyFunTransTerm (FunTransClos lrt clos) = applyCallClosSpecTerm lrt clos
applyFunTransTerm (FunTransFun _ f) = applyTermLikeMulti f


-- | The translation of the vacuously true permission
pattern PTrans_True :: PermTrans ctx a
pattern PTrans_True = PTrans_Conj []

-- | A single @lowned@ permission translation
pattern PTrans_LOwned ::
  () => (a ~ LifetimeType) =>
  Mb ctx [PermExpr LifetimeType] -> CruCtx ps_in -> CruCtx ps_out ->
  Mb ctx (ExprPerms ps_in) -> Mb ctx (ExprPerms ps_out) ->
  LOwnedTrans ctx ps_extra ps_in ps_out ->
  PermTrans ctx a
pattern PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t =
  PTrans_Conj [APTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t]

-- | A single function permission
pattern PTrans_Fun :: () => (a ~ FunctionHandleType cargs ret) =>
                      Mb ctx (FunPerm ghosts (CtxToRList cargs) gouts ret) ->
                      FunTransTerm -> PermTrans ctx a
pattern PTrans_Fun mb_fun_perm tr = PTrans_Conj [APTrans_Fun mb_fun_perm tr]

-- | Build a type translation for a disjunctive, existential, or named
-- permission that uses the 'PTrans_Term' constructor
mkPermTypeTrans1 :: Mb ctx (ValuePerm a) -> TypeDesc ->
                    ImpTypeTrans (PermTrans ctx a)
mkPermTypeTrans1 mb_p tp = mkImpTypeTrans1 tp (PTrans_Term mb_p)

-- | Extract the body of a conjunction or raise an error
unPTransConj :: String -> PermTrans ctx a -> [AtomicPermTrans ctx a]
unPTransConj _ (PTrans_Conj ps) = ps
unPTransConj str _ = error (str ++ ": not a conjunction")

-- | Extract the body of a conjunction, which should have exactly one conjunct,
-- or raise an error
unPTransConj1 :: String -> PermTrans ctx a -> AtomicPermTrans ctx a
unPTransConj1 str ptrans =
  case unPTransConj str ptrans of
    [aptrans] -> aptrans
    _ -> error (str ++ ": not a single-element conjunction")

-- | Extract out a list of proofs of 'BVProp's from a proof of a conjunction
unPTransBVProps :: String -> PermTrans ctx (LLVMPointerType w) ->
                   [BVPropTrans ctx w]
unPTransBVProps _ ptrans
  | PTrans_Conj ps <- ptrans
  , Just transs <- mapM (\ap -> case ap of
                            APTrans_BVProp p -> Just p
                            _ -> Nothing) ps
  = transs
unPTransBVProps str _ = error (str ++ ": not a list of BVProp permissions")

-- | Extract the body of a conjunction of a single field permission
unPTransLLVMField :: String -> NatRepr sz ->
                     PermTrans ctx (LLVMPointerType w) ->
                     (Mb ctx (LLVMFieldPerm w sz),
                      PermTrans ctx (LLVMPointerType sz))
unPTransLLVMField _ sz (PTrans_Conj [APTrans_LLVMField mb_fp ptrans])
  | Just Refl <- testEquality sz (mbLift $ fmap llvmFieldSize mb_fp)
  = (mb_fp, ptrans)
unPTransLLVMField str _ _ =
  error (str ++ ": not an LLVM field permission of the required size")

-- | Extract the body of a conjunction of a single array permission
unPTransLLVMArray :: String -> PermTrans ctx (LLVMPointerType w) ->
                     LLVMArrayPermTrans ctx w
unPTransLLVMArray _ (PTrans_Conj [APTrans_LLVMArray aptrans]) = aptrans
unPTransLLVMArray str _ = error (str ++ ": not an LLVM array permission")

data SomeLOwnedTrans ctx ps_in ps_out =
  forall ps_extra. SomeLOwnedTrans (LOwnedTrans ctx ps_extra ps_in ps_out)

-- | Extract the 'LOwnedTrans' of a conjunction of a single @lowned@ permission
-- with the specified input and output types
unPTransLOwned :: String -> Mb ctx (CruCtx ps_in) -> Mb ctx (CruCtx ps_out) ->
                  PermTrans ctx LifetimeType ->
                  SomeLOwnedTrans ctx ps_in ps_out
unPTransLOwned _ tps_in tps_out
  (PTrans_LOwned _ (testEquality (mbLift tps_in) -> Just Refl)
   (testEquality (mbLift tps_out) -> Just Refl) _ _ lotr)
  = SomeLOwnedTrans lotr
unPTransLOwned fname _ _ _ =
  panic fname ["Expected lowned permission"]

-- | Add a borrow translation to the translation of an array permission

-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = RAssign (PermTrans ctx) ps

-- | A 'TypeTrans' for a 'PermTrans' that is relative to an expr context
type Rel1PermTypeTrans ctx a =
  ExprTransCtx ctx -> ImpTypeTrans (PermTrans ctx a)

-- | A 'TypeTrans' for a 'PermTransCtx' that is relative to an expr context
type RelPermsTypeTrans ctx ps =
  ExprTransCtx ctx -> ImpTypeTrans (PermTransCtx ctx ps)

-- | Append two 'RelPermsTypeTrans's
appRelPermsTypeTrans :: RelPermsTypeTrans ctx ps1 ->
                        RelPermsTypeTrans ctx ps2 ->
                        RelPermsTypeTrans ctx (ps1 :++: ps2)
appRelPermsTypeTrans tps1 tps2 = \ectx -> RL.append <$> tps1 ectx <*> tps2 ectx

app1RelPermsTypeTrans :: RelPermsTypeTrans ctx ps ->
                         Rel1PermTypeTrans ctx tp ->
                         RelPermsTypeTrans ctx (ps :> tp)
app1RelPermsTypeTrans tps1 tps2 = \ectx -> (:>:) <$> tps1 ectx <*> tps2 ectx

-- | Prepend an 'RNil' list of permissions to a 'RelPermsTypeTrans'
preNilRelPermsTypeTrans :: RelPermsTypeTrans ctx ps ->
                           RelPermsTypeTrans ctx (RNil :++: ps)
preNilRelPermsTypeTrans = appRelPermsTypeTrans (const $ pure MNil)

-- | Build a permission translation context with just @true@ permissions
truePermTransCtx :: CruCtx ps -> PermTransCtx ctx ps
truePermTransCtx CruCtxNil = MNil
truePermTransCtx (CruCtxCons ctx _) = truePermTransCtx ctx :>: PTrans_True

-- | Build a permission translation context with equality permissions
eqPermTransCtx :: forall (ctx :: RList CrucibleType) (ps :: RList CrucibleType) any.
                  RAssign any ctx -> RAssign (Member ctx) ps ->
                  PermTransCtx ctx ps
eqPermTransCtx ns =
  RL.map (\memb -> PTrans_Eq $ nuMulti (RL.map (\_-> Proxy) ns) (PExpr_Var . RL.get memb))


instance IsTermTrans (PermTrans ctx a) where
  transTerms (PTrans_Eq _) = []
  transTerms (PTrans_Conj aps) = transTerms aps
  transTerms (PTrans_Defined _ _ _ ptrans) = transTerms ptrans
  transTerms (PTrans_Term _ t) = [t]

instance IsTermTrans (PermTransCtx ctx ps) where
  transTerms MNil = []
  transTerms (ctx :>: ptrans) = transTerms ctx ++ transTerms ptrans

instance IsTermTrans (AtomicPermTrans ctx a) where
  transTerms (APTrans_LLVMField _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMArray arr_trans) = transTerms arr_trans
  transTerms (APTrans_LLVMBlock _ t) = [t]
  transTerms (APTrans_LLVMFree _) = []
  transTerms (APTrans_LLVMFunPtr _ trans) = transTerms trans
  transTerms APTrans_IsLLVMPtr = []
  transTerms (APTrans_LLVMBlockShape _ t) = [t]
  transTerms (APTrans_NamedConj _ _ _ t) = [t]
  transTerms (APTrans_DefinedNamedConj _ _ _ ptrans) = transTerms ptrans
  transTerms (APTrans_LLVMFrame _) = []
  transTerms (APTrans_LOwned _ _ _ eps_in _ lotr) =
    [lownedTransTerm eps_in lotr]
  transTerms (APTrans_LOwnedSimple _ _) = []
  transTerms (APTrans_LCurrent _) = []
  transTerms APTrans_LFinished = []
  transTerms (APTrans_Struct pctx) = transTerms pctx
  transTerms (APTrans_Fun _ t) = [funTransTermToClos t]
  transTerms (APTrans_BVProp prop) = transTerms prop
  transTerms APTrans_Any = []

instance IsTermTrans (BVPropTrans ctx w) where
  transTerms (BVPropTrans _ t) = [t]

instance IsTermTrans (BVRangeTrans ctx w) where
  transTerms (BVRangeTrans _ trans1 trans2) =
    transTerms trans1 ++ transTerms trans2

instance IsTermTrans (LLVMArrayPermTrans ctx a) where
  transTerms arr_trans =
    [llvmArrayTransTerm arr_trans] -- : transTerms (llvmArrayTransBorrows arr_trans)

{-
instance IsTermTrans (LLVMArrayBorrowTrans ctx w) where
  transTerms (LLVMArrayBorrowTrans _ prop_transs) = transTerms prop_transs
-}


-- | Map a context of perm translations to a list of 'SpecTerm's, dropping the
-- "invisible" ones whose permissions are translated to 'Nothing'
permCtxToTerms :: PermTransCtx ctx tps -> [SpecTerm]
permCtxToTerms = concat . RL.mapToList transTerms

-- | Extract out the permission of a permission translation result
permTransPerm :: RAssign Proxy ctx -> PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm _ (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm prxs (PTrans_Conj ts) =
  fmap ValPerm_Conj $ foldr (mbMap2 (:)) (nuMulti prxs $ const []) $
  map (atomicPermTransPerm prxs) ts
permTransPerm _ (PTrans_Defined npn mb_args mb_off _) =
  mbMap2 (ValPerm_Named npn) mb_args mb_off
permTransPerm _ (PTrans_Term p _) = p

-- | Extract out the atomic permission of an atomic permission translation result
atomicPermTransPerm :: RAssign Proxy ctx -> AtomicPermTrans ctx a ->
                       Mb ctx (AtomicPerm a)
atomicPermTransPerm _ (APTrans_LLVMField fld _) = fmap Perm_LLVMField fld
atomicPermTransPerm _ (APTrans_LLVMArray arr_trans) =
  fmap Perm_LLVMArray $ llvmArrayTransPerm arr_trans
atomicPermTransPerm _ (APTrans_LLVMBlock mb_bp _) = fmap Perm_LLVMBlock mb_bp
atomicPermTransPerm _ (APTrans_LLVMFree e) = fmap Perm_LLVMFree e
atomicPermTransPerm prxs (APTrans_LLVMFunPtr tp ptrans) =
  fmap (Perm_LLVMFunPtr tp) (permTransPerm prxs ptrans)
atomicPermTransPerm prxs APTrans_IsLLVMPtr = nuMulti prxs $ const Perm_IsLLVMPtr
atomicPermTransPerm _ (APTrans_LLVMBlockShape mb_sh _) =
  fmap Perm_LLVMBlockShape mb_sh
atomicPermTransPerm _ (APTrans_NamedConj npn args off _) =
  mbMap2 (Perm_NamedConj npn) args off
atomicPermTransPerm _ (APTrans_DefinedNamedConj npn args off _) =
  mbMap2 (Perm_NamedConj npn) args off
atomicPermTransPerm _ (APTrans_LLVMFrame fp) = fmap Perm_LLVMFrame fp
atomicPermTransPerm _ (APTrans_LOwned
                       mb_ls tps_in tps_out mb_ps_in mb_ps_out _) =
  mbMap3 (\ls -> Perm_LOwned ls tps_in tps_out) mb_ls mb_ps_in mb_ps_out
atomicPermTransPerm _ (APTrans_LOwnedSimple tps mb_lops) =
  fmap (Perm_LOwnedSimple tps) mb_lops
atomicPermTransPerm _ (APTrans_LCurrent l) = fmap Perm_LCurrent l
atomicPermTransPerm prxs APTrans_LFinished = nus prxs $ const Perm_LFinished
atomicPermTransPerm prxs (APTrans_Struct ps) =
  fmap Perm_Struct $ permTransCtxPerms prxs ps
atomicPermTransPerm _ (APTrans_Fun fp _) = fmap Perm_Fun fp
atomicPermTransPerm _ (APTrans_BVProp (BVPropTrans prop _)) =
  fmap Perm_BVProp prop
atomicPermTransPerm prxs APTrans_Any = nuMulti prxs $ const $ Perm_Any

-- | Extract out the permissions from a context of permission translations
permTransCtxPerms :: RAssign Proxy ctx -> PermTransCtx ctx ps ->
                     Mb ctx (ValuePerms ps)
permTransCtxPerms prxs MNil = nuMulti prxs $ const ValPerms_Nil
permTransCtxPerms prxs (ptranss :>: ptrans) =
  mbMap2 ValPerms_Cons (permTransCtxPerms prxs ptranss) (permTransPerm prxs ptrans)

-- | Extract out the LLVM borrow from its translation
{-
borrowTransMbBorrow :: LLVMArrayBorrowTrans ctx w -> Mb ctx (LLVMArrayBorrow w)
borrowTransMbBorrow (LLVMArrayBorrowTrans mb_b _) = mb_b
-}

-- | Test that a permission equals that of a permission translation
permTransPermEq :: PermTrans ctx a -> Mb ctx (ValuePerm a) -> Bool
permTransPermEq ptrans mb_p =
  permTransPerm (mbToProxy mb_p) ptrans == mb_p


extMbAny :: RAssign any ctx2 -> Mb ctx1 a -> Mb (ctx1 :++: ctx2) a
extMbAny ctx2 = extMbMulti (RL.map (const Proxy) ctx2)

extPermTrans :: ExtPermTrans f => ExprTrans tp -> f ctx a -> f (ctx :> tp) a
extPermTrans e = extPermTransMulti (MNil :>: e)

-- | Generic function to extend the context of the translation of a permission
class ExtPermTrans f where
  extPermTransMulti :: ExprTransCtx ctx2 -> f ctx1 a -> f (ctx1 :++: ctx2) a

instance ExtPermTrans PermTrans where
  extPermTransMulti ectx (PTrans_Eq e) =
    PTrans_Eq $ extMbAny ectx e
  extPermTransMulti ectx (PTrans_Conj aps) =
    PTrans_Conj (map (extPermTransMulti ectx) aps)
  extPermTransMulti ectx (PTrans_Defined n args a ptrans) =
    PTrans_Defined n (extMbAny ectx args) (extMbAny ectx a)
    (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (PTrans_Term p t) = PTrans_Term (extMbAny ectx p) t

instance ExtPermTrans AtomicPermTrans where
  extPermTransMulti ectx (APTrans_LLVMField fld ptrans) =
    APTrans_LLVMField (extMbAny ectx fld) (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (APTrans_LLVMArray arr_trans) =
    APTrans_LLVMArray $ extPermTransMulti ectx arr_trans
  extPermTransMulti ectx (APTrans_LLVMBlock mb_bp t) =
    APTrans_LLVMBlock (extMbAny ectx mb_bp) t
  extPermTransMulti ectx  (APTrans_LLVMFree e) =
    APTrans_LLVMFree $ extMbAny ectx e
  extPermTransMulti ectx (APTrans_LLVMFunPtr tp ptrans) =
    APTrans_LLVMFunPtr tp (extPermTransMulti ectx ptrans)
  extPermTransMulti _ APTrans_IsLLVMPtr = APTrans_IsLLVMPtr
  extPermTransMulti ectx (APTrans_LLVMBlockShape mb_sh t) =
    APTrans_LLVMBlockShape (extMbAny ectx mb_sh) t
  extPermTransMulti ectx (APTrans_NamedConj npn args off t) =
    APTrans_NamedConj npn (extMbAny ectx args) (extMbAny ectx off) t
  extPermTransMulti ectx (APTrans_DefinedNamedConj npn args off ptrans) =
    APTrans_DefinedNamedConj npn (extMbAny ectx args) (extMbAny ectx off)
    (extPermTransMulti ectx ptrans)
  extPermTransMulti ectx (APTrans_LLVMFrame fp) =
    APTrans_LLVMFrame $ extMbAny ectx fp
  extPermTransMulti ectx (APTrans_LOwned ls tps_in tps_out ps_in ps_out lotr) =
    APTrans_LOwned (extMbAny ectx ls) tps_in tps_out
    (extMbAny ectx ps_in) (extMbAny ectx ps_out)
    (extLOwnedTransMulti ectx lotr)
  extPermTransMulti ectx (APTrans_LOwnedSimple tps lops) =
    APTrans_LOwnedSimple tps (extMbAny ectx lops)
  extPermTransMulti ectx (APTrans_LCurrent p) =
    APTrans_LCurrent $ extMbAny ectx p
  extPermTransMulti _ APTrans_LFinished = APTrans_LFinished
  extPermTransMulti ectx (APTrans_Struct ps) =
    APTrans_Struct $ RL.map (extPermTransMulti ectx) ps
  extPermTransMulti ectx (APTrans_Fun fp trans) =
    APTrans_Fun (extMbAny ectx fp) trans
  extPermTransMulti ectx (APTrans_BVProp prop_trans) =
    APTrans_BVProp $ extPermTransMulti ectx prop_trans
  extPermTransMulti _ APTrans_Any = APTrans_Any

instance ExtPermTrans LLVMArrayPermTrans where
  extPermTransMulti ectx (LLVMArrayPermTrans ap len sh {- bs -} t) =
    LLVMArrayPermTrans (extMbAny ectx ap) len
    (fmap (extPermTransMulti ectx) sh) {- (map extPermTrans bs) -} t

{-
instance ExtPermTrans LLVMArrayBorrowTrans where
  extPermTrans (LLVMArrayBorrowTrans mb_b prop_transs) =
    LLVMArrayBorrowTrans (extMb mb_b) (map extPermTrans prop_transs)
-}

instance ExtPermTrans BVPropTrans where
  extPermTransMulti ectx (BVPropTrans prop t) =
    BVPropTrans (extMbAny ectx prop) t

instance ExtPermTrans BVRangeTrans where
  extPermTransMulti ectx (BVRangeTrans rng t1 t2) =
    BVRangeTrans (extMbAny ectx rng) t1 t2

-- | Extend the context of a permission translation context
extPermTransCtx :: ExprTrans tp -> PermTransCtx ctx ps ->
                   PermTransCtx (ctx :> tp) ps
extPermTransCtx e = RL.map (extPermTrans e)

-- | Extend the context of a permission translation context
extPermTransCtxMulti :: ExprTransCtx ctx2 -> PermTransCtx ctx1 ps ->
                        PermTransCtx (ctx1 :++: ctx2) ps
extPermTransCtxMulti ectx2 = RL.map (extPermTransMulti ectx2)

-- | Extend the context of a 'RelPermsTypeTrans'
extRelPermsTypeTransMulti :: ExprTransCtx ctx2 -> RelPermsTypeTrans ctx1 ps ->
                             RelPermsTypeTrans (ctx1 :++: ctx2) ps
extRelPermsTypeTransMulti ectx2 (rel_tp :: RelPermsTypeTrans ctx1 ps) =
  \ectx12 ->
  let (ectx1, _) = RL.split (Proxy :: Proxy ctx1) ectx2 ectx12 in
  fmap (extPermTransCtxMulti ectx2) $ rel_tp ectx1


-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)

-- | Apply 'offsetLLVMAtomicPerm' to the permissions associated with an atomic
-- permission translation, returning 'Nothing' if the offset does not exist
offsetLLVMAtomicPermTrans :: (1 <= w, KnownNat w) => Mb ctx (PermExpr (BVType w)) ->
                             AtomicPermTrans ctx (LLVMPointerType w) ->
                             Maybe (AtomicPermTrans ctx (LLVMPointerType w))
offsetLLVMAtomicPermTrans mb_off ptrans
  | [nuMP| Just 0 |] <- mbMatch $ fmap bvMatchConstInt mb_off = Just ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMField fld ptrans) =
  Just $ APTrans_LLVMField (mbMap2 offsetLLVMFieldPerm mb_off fld) ptrans
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMArray
                                  (LLVMArrayPermTrans ap len sh {- bs -} t)) =
  Just $ APTrans_LLVMArray $
  LLVMArrayPermTrans (mbMap2 offsetLLVMArrayPerm mb_off ap) len sh {- bs -} t
offsetLLVMAtomicPermTrans mb_off (APTrans_LLVMBlock mb_bp t) =
  Just $ APTrans_LLVMBlock
  (mbMap2 (\off bp ->
            bp { llvmBlockOffset =
                   bvAdd (llvmBlockOffset bp) off } ) mb_off mb_bp)
  t
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFree _) = Nothing
offsetLLVMAtomicPermTrans _ (APTrans_LLVMFunPtr _ _) = Nothing
offsetLLVMAtomicPermTrans _ p@APTrans_IsLLVMPtr = Just p
offsetLLVMAtomicPermTrans off (APTrans_NamedConj npn args off' t) =
  Just $ APTrans_NamedConj npn args (mbMap2 addPermOffsets off' $
                                     fmap mkLLVMPermOffset off) t
offsetLLVMAtomicPermTrans off (APTrans_DefinedNamedConj npn args off' ptrans) =
  Just $ APTrans_DefinedNamedConj npn args (mbMap2 addPermOffsets off' $
                                            fmap mkLLVMPermOffset off)
  (offsetLLVMPermTrans off ptrans)
offsetLLVMAtomicPermTrans _ _ = Nothing

-- | Apply 'offsetLLVMPerm' to the permissions associated with a permission
-- translation
offsetLLVMPermTrans :: (1 <= w, KnownNat w) => Mb ctx (PermExpr (BVType w)) ->
                       PermTrans ctx (LLVMPointerType w) ->
                       PermTrans ctx (LLVMPointerType w)
offsetLLVMPermTrans mb_off (PTrans_Eq mb_e) =
  PTrans_Eq $ mbMap2 (\off e -> addLLVMOffset e (bvNegate off)) mb_off mb_e
offsetLLVMPermTrans mb_off (PTrans_Conj ps) =
  PTrans_Conj $ mapMaybe (offsetLLVMAtomicPermTrans mb_off) ps
offsetLLVMPermTrans mb_off (PTrans_Defined n args off ptrans) =
  PTrans_Defined n args (mbMap2 addPermOffsets off
                         (fmap mkLLVMPermOffset mb_off)) $
  offsetLLVMPermTrans mb_off ptrans
offsetLLVMPermTrans mb_off (PTrans_Term mb_p t) =
  PTrans_Term (mbMap2 offsetLLVMPerm mb_off mb_p) t

-- | Apply 'offsetPerm' to the permissions associated with a permission
-- translation
offsetPermTrans :: Mb ctx (PermOffset a) -> PermTrans ctx a -> PermTrans ctx a
offsetPermTrans mb_off = case mbMatch mb_off of
  [nuMP| NoPermOffset |] -> id
  [nuMP| LLVMPermOffset off |] -> offsetLLVMPermTrans off

{-
-- | Add a borrow to an LLVM array permission translation
llvmArrayTransAddBorrow :: LLVMArrayBorrowTrans ctx w ->
                           LLVMArrayPermTrans ctx w ->
                           LLVMArrayPermTrans ctx w
llvmArrayTransAddBorrow b arr_trans =
  arr_trans { llvmArrayTransPerm =
                mbMap2 llvmArrayAddBorrow (llvmArrayBorrowTransBorrow b)
                (llvmArrayTransPerm arr_trans)
            , llvmArrayTransBorrows = b : llvmArrayTransBorrows arr_trans }

-- | Find the index in the list of borrows of a specific borrow
llvmArrayTransFindBorrowIx :: Mb ctx (LLVMArrayBorrow w) ->
                              LLVMArrayPermTrans ctx w -> Int
llvmArrayTransFindBorrowIx b arr_trans =
  mbLift $ mbMap2 llvmArrayFindBorrow b (llvmArrayTransPerm arr_trans)

-- | Find the index in the list of borrows of a specific borrow
llvmArrayTransFindBorrow :: Mb ctx (LLVMArrayBorrow w) ->
                            LLVMArrayPermTrans ctx w ->
                            LLVMArrayBorrowTrans ctx w
llvmArrayTransFindBorrow b arr_trans =
  llvmArrayTransBorrows arr_trans !! llvmArrayTransFindBorrowIx b arr_trans

-- | Remove a borrow from an LLVM array permission translation
llvmArrayTransRemBorrow :: LLVMArrayBorrowTrans ctx w ->
                           LLVMArrayPermTrans ctx w ->
                           LLVMArrayPermTrans ctx w
llvmArrayTransRemBorrow b_trans arr_trans =
  let b = llvmArrayBorrowTransBorrow b_trans in
  arr_trans { llvmArrayTransPerm =
                mbMap2 llvmArrayRemBorrow b (llvmArrayTransPerm arr_trans)
            , llvmArrayTransBorrows =
                deleteNth (llvmArrayTransFindBorrowIx b arr_trans)
                (llvmArrayTransBorrows arr_trans) }
-}

-- | Read an array cell of the translation of an LLVM array permission at a
-- given index, given proofs of the propositions that the index is in the array
-- as returned by 'llvmArrayIndexInArray'. Note that the first proposition
-- should always be that the cell number is <= the array length.
getLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         Mb ctx (PermExpr (BVType w)) -> SpecTerm ->
                         [BVPropTrans ctx w] ->
                         AtomicPermTrans ctx (LLVMPointerType w)
getLLVMArrayTransCell arr_trans mb_cell cell_tm (BVPropTrans _ in_rng_pf:_) =
  let w = fromInteger $ natVal arr_trans in
  fromJust $
  -- FIXME: remove offsetLLVMAtomicPermTrans, as it requires changing all
  -- name-bindings in the PermTrans it is applied to back to FreshFuns, i.e., it
  -- substitutes for all the names
  offsetLLVMAtomicPermTrans (mbMap2 llvmArrayCellToOffset
                             (llvmArrayTransPerm arr_trans) mb_cell) $
  typeTransF (llvmArrayTransHeadCell arr_trans)
  [applyGlobalTermLike "Prelude.atBVVec"
   [natTermLike w, openTermLike (llvmArrayTransLen arr_trans),
    llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
    cell_tm, in_rng_pf]]
getLLVMArrayTransCell _ _ _ _ =
  error "getLLVMArrayTransCell: malformed arguments"


-- | Write an array cell of the translation of an LLVM array permission at a
-- given index
setLLVMArrayTransCell :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                         SpecTerm -> AtomicPermTrans ctx (LLVMPointerType w) ->
                         LLVMArrayPermTrans ctx w
setLLVMArrayTransCell arr_trans cell_tm cell_value =
  let w = fromInteger $ natVal arr_trans in
  arr_trans {
    llvmArrayTransTerm =
        applyGlobalTermLike "Prelude.updBVVec"
        [natTermLike w, openTermLike (llvmArrayTransLen arr_trans),
         llvmArrayTransCellType arr_trans, llvmArrayTransTerm arr_trans,
         cell_tm, transTerm1 cell_value] }


-- | Read a slice (= a sub-array) of the translation of an LLVM array permission
-- for the supplied 'BVRange', given the translation of the sub-array permission
-- and proofs of the propositions that the 'BVRange' is in the array as returned
-- by 'llvmArrayCellsInArray'. Note that the first two of these propositions are
-- those returned by 'bvPropRangeSubset'.
getLLVMArrayTransSlice :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          ImpTypeTrans (LLVMArrayPermTrans ctx w) ->
                          BVRangeTrans ctx w -> [BVPropTrans ctx w] ->
                          LLVMArrayPermTrans ctx w
getLLVMArrayTransSlice arr_trans sub_arr_tp rng_trans prop_transs =
  let w = fromInteger $ natVal arr_trans
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = openTermLike $ llvmArrayTransLen arr_trans
      v_tm = llvmArrayTransTerm arr_trans
      off_tm = transTerm1 $ bvRangeTransOff rng_trans
      len'_tm = transTerm1 $ bvRangeTransLen rng_trans
      (p1_trans, p2_trans, _) = expectLengthAtLeastTwo prop_transs
      BVPropTrans _ p1_tm = p1_trans
      BVPropTrans _ p2_tm = p2_trans in
  typeTransF sub_arr_tp
  [applyGlobalTermLike "Prelude.sliceBVVec"
   [natTermLike w, len_tm, elem_tp, off_tm, len'_tm, p1_tm, p2_tm, v_tm]]

-- | Write a slice (= a sub-array) of the translation of an LLVM array
-- permission given the translation of the slice and of the offset of that slice
-- in the larger array
setLLVMArrayTransSlice :: (1 <= w, KnownNat w) => LLVMArrayPermTrans ctx w ->
                          LLVMArrayPermTrans ctx w -> SpecTerm ->
                          LLVMArrayPermTrans ctx w
setLLVMArrayTransSlice arr_trans sub_arr_trans off_tm =
  let w = fromInteger $ natVal arr_trans
      elem_tp = llvmArrayTransCellType arr_trans
      len_tm = openTermLike $ llvmArrayTransLen arr_trans
      arr_tm = llvmArrayTransTerm arr_trans
      len'_tm = openTermLike $ llvmArrayTransLen sub_arr_trans
      sub_arr_tm = llvmArrayTransTerm sub_arr_trans in
  arr_trans
  { llvmArrayTransTerm =
      applyGlobalTermLike "Prelude.updSliceBVVec"
      [natTermLike w, len_tm, elem_tp, arr_tm, off_tm, len'_tm, sub_arr_tm] }

{-
-- | Weaken a monadic function of type @(T1*...*Tn) -> SpecM(U1*...*Um)@ to one
-- of type @(V*T1*...*Tn) -> SpecM(V*U1*...*Um)@, @n@-ary tuple types are built
-- using 'tupleOfTypes'
weakenMonadicFun1 :: OpenTerm -> [OpenTerm] -> [OpenTerm] -> OpenTerm ->
                     ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenMonadicFun1 v ts us f =
  -- First form a term f1 of type V*(T1*...*Tn) -> SpecM(V*(U1*...*Um))
  do let t_tup = tupleOfTypes ts
         u_tup = tupleOfTypes us
     f1 <- applyNamedSpecOpEmptyM "Prelude.tupleSpecMFunBoth" [t_tup, u_tup, v, f]

     let f2 = case ts of
           -- If ts is empty, form the term \ (x:V) -> f1 (x, ()) to coerce f1
           -- from type V*#() -> SpecM(V*Us) to type V -> SpecM(V*Us)
           [] ->
             lambdaOpenTerm "x" v $ \x ->
             applyOpenTerm f1 (pairOpenTerm x unitOpenTerm)
           -- Otherwise, leave f1 unchanged
           _ -> f1

     case us of
       -- If us is empty, compose f2 with \ (x:V*#()) -> returnM V x.(1) to
       -- coerce from V*Us -> SpecM (V*#()) to V*Us -> SpecM V
       [] ->
         do fun_tm <-
              lambdaOpenTermTransM "x" (pairTypeOpenTerm v unitTypeOpenTerm)
              (\x -> applyNamedSpecOpEmptyM "Prelude.retS" [v, pairLeftOpenTerm x])
            applyNamedSpecOpEmptyM "Prelude.composeS"
              [tupleOfTypes (v:ts), pairTypeOpenTerm v unitTypeOpenTerm,
               v, f2, fun_tm]
       -- Otherwise, leave f2 unchanged
       _ -> return f2


-- | Weaken a monadic function of type
--
-- > (T1*...*Tn) -> SpecM e eTp emptyFunStack (U1*...*Um)
--
-- to one of type
--
-- > (V1*...*Vk*T1*...*Tn) -> SpecM e eTp emptyFunStack (V1*...*Vk*U1*...*Um)
--
-- where tuples of 2 or more types are right-nested and and in a unit type,
-- i.e., have the form @(T1 * (T2 * (... * (Tn * #()))))@
weakenMonadicFun :: [OpenTerm] -> [OpenTerm] -> [OpenTerm] -> OpenTerm ->
                    ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenMonadicFun vs ts_top us_top f_top =
  foldr (\v rest_m ->
          do (ts,us,f) <- rest_m
             f' <- weakenMonadicFun1 v ts us f
             return (v:ts, v:us, f'))
  (return (ts_top, us_top, f_top))
  vs
  >>= \(_,_,ret) -> return ret

-- | Weaken a monadic function which is the translation of an ownership
-- permission @lowned(ps_in -o ps_out)@ to @lowned(P * ps_in -o P * ps_out)@
weakenLifetimeFun :: TypeTrans (PermTrans ctx a) ->
                     TypeTrans (PermTransCtx ctx ps_in) ->
                     TypeTrans (PermTransCtx ctx ps_out) ->
                     OpenTerm ->
                     ImpTransM ext blocks tops rets ps ctx OpenTerm
weakenLifetimeFun tp_trans ps_in_trans ps_out_trans f =
  weakenMonadicFun (transTerms
                    tp_trans) (transTerms
                               ps_in_trans) (transTerms ps_out_trans) f
-}

-- | Make a type translation of a 'BVProp' from it and its pure type
mkBVPropTrans :: Mb ctx (BVProp w) -> OpenTerm ->
                 TypeTrans 'False (BVPropTrans ctx w)
mkBVPropTrans prop tp =
  mkImpTypeTrans1 (TypeDescPure tp) $ BVPropTrans prop

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVProp w) (ImpTypeTrans (BVPropTrans ctx w)) where
  translate prop = case mbMatch prop of
    [nuMP| BVProp_Eq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1Pure e1
         t2 <- translate1Pure e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [applyOpenTermMulti (globalOpenTerm "Prelude.Vec")
            [natOpenTerm w, globalOpenTerm "Prelude.Bool"],
            t1, t2]

    [nuMP| BVProp_Neq _ _ |] ->
      -- NOTE: we don't need a proof object for not equal proofs, because we don't
      -- actually use them for anything, but it is easier to just have all BVProps
      -- be represented as something, so we use the unit type
      return $ mkBVPropTrans prop unitTypeOpenTerm

    [nuMP| BVProp_ULt e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1Pure e1
         t2 <- translate1Pure e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvult")
            [natOpenTerm w, t1, t2], trueOpenTerm]

    [nuMP| BVProp_ULeq e1 e2 |] ->
      do let w = natVal4 e1
         t1 <- translate1Pure e1
         t2 <- translate1Pure e2
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
            [natOpenTerm w, t1, t2], trueOpenTerm]

    [nuMP| BVProp_ULeq_Diff e1 e2 e3 |] ->
      do let w = natVal4 e1
         t1 <- translate1Pure e1
         t2 <- translate1Pure e2
         t3 <- translate1Pure e3
         return $ mkBVPropTrans prop $
           dataTypeOpenTerm "Prelude.Eq"
           [globalOpenTerm "Prelude.Bool",
            applyOpenTermMulti (globalOpenTerm "Prelude.bvule")
            [natOpenTerm w, t1,
             applyOpenTermMulti (globalOpenTerm "Prelude.bvSub")
              [natOpenTerm w, t2, t3]],
            trueOpenTerm]

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (BVRange w) (BVRangeTrans ctx w) where
  translate rng@(mbMatch -> [nuMP| BVRange off len |]) =
    do off_tm <- translate off
       len_tm <- translate len
       return $ BVRangeTrans rng off_tm len_tm

-- [| p :: ValuePerm |] = type of the impl translation of reg with perms p
instance TransInfo info =>
         Translate info ctx (ValuePerm a) (ImpTypeTrans (PermTrans ctx a)) where
  translate p = case mbMatch p of
    [nuMP| ValPerm_Eq e |] -> return $ mkImpTypeTrans0 $ PTrans_Eq e
    [nuMP| ValPerm_Or p1 p2 |] ->
      do tp1 <- translate p1
         tp2 <- translate p2
         return $ mkPermTypeTrans1 p (eitherTypeTrans tp1 tp2)
    [nuMP| ValPerm_Exists p1 |] ->
      do let tp = mbBindingType p1
         tp_trans <- translateClosed tp
         mkPermTypeTrans1 p <$>
           sigmaTypePermTransM "x_ex" tp_trans (mbCombine RL.typeCtxProxies p1)
    [nuMP| ValPerm_Named npn args off |] ->
      do env <- infoEnv <$> ask
         case lookupNamedPerm env (mbLift npn) of
           Just (NamedPerm_Opaque op) ->
             exprCtxPureTypeTerms <$> translate args >>= \case
             Just args_exprs ->
               return $ mkPermTypeTrans1 p $ TypeDescPure $
               applyGlobalOpenTerm (opaquePermTrans op) args_exprs
             Nothing ->
               panic "translate"
               ["Heapster cannot yet handle opaque permissions over impure types"]
           Just (NamedPerm_Rec rp) ->
             exprCtxPureTypeTerms <$> translate args >>= \case
             Just args_exprs ->
               return $ mkPermTypeTrans1 p $ TypeDescPure $
               applyOpenTermMulti (globalOpenTerm $ recPermTransType rp) args_exprs
             Nothing ->
               panic "translate"
               ["Heapster cannot yet handle recursive permissions over impure types"]
           Just (NamedPerm_Defined dp) ->
             fmap (PTrans_Defined (mbLift npn) args off) <$>
             translate (mbMap2 (unfoldDefinedPerm dp) args off)
           Nothing -> error "Unknown permission name!"
    [nuMP| ValPerm_Conj ps |] ->
      fmap PTrans_Conj <$> listTypeTrans <$> translate ps
    [nuMP| ValPerm_Var x _ |] ->
      mkPermTypeTrans1 p <$> unETransPerm <$> translate x
    [nuMP| ValPerm_False |] ->
      return $ mkPermTypeTrans1 p $
      TypeDescPure $ globalOpenTerm "Prelude.FalseProp"

instance TransInfo info =>
         Translate info ctx (AtomicPerm a) (TypeTrans 'False
                                            (AtomicPermTrans ctx a)) where
  translate mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fld |] ->
      fmap (APTrans_LLVMField fld) <$> translate (fmap llvmFieldContents fld)

    [nuMP| Perm_LLVMArray ap |] ->
      fmap APTrans_LLVMArray <$> translate ap

    [nuMP| Perm_LLVMBlock bp |] ->
      do tp <- translateShape (fmap llvmBlockShape bp)
         return $ mkImpTypeTrans1 tp (APTrans_LLVMBlock bp)

    [nuMP| Perm_LLVMFree e |] ->
      return $ mkImpTypeTrans0 $ APTrans_LLVMFree e
    [nuMP| Perm_LLVMFunPtr tp p |] ->
      translate p >>= \tp_ptrans ->
      return $ fmap (APTrans_LLVMFunPtr $ mbLift tp) tp_ptrans
    [nuMP| Perm_IsLLVMPtr |] ->
      return $ mkImpTypeTrans0 APTrans_IsLLVMPtr
    [nuMP| Perm_LLVMBlockShape sh |] ->
      do tp <- translateShape sh
         return $ mkImpTypeTrans1 tp (APTrans_LLVMBlockShape sh)
    [nuMP| Perm_NamedConj npn args off |]
      | [nuMP| DefinedSortRepr _ |] <- mbMatch $ fmap namedPermNameSort npn ->
        -- To translate P<args>@off as an atomic permission, we translate it as a
        -- normal permission and map the resulting PermTrans to an AtomicPermTrans
        do tptrans <- translate $ mbMap2 (ValPerm_Named $ mbLift npn) args off
           return $ fmap (APTrans_DefinedNamedConj (mbLift npn) args off) tptrans
    [nuMP| Perm_NamedConj npn args off |] ->
      -- To translate P<args>@off as an atomic permission, we translate it as a
      -- normal permission and map the resulting PermTrans to an AtomicPermTrans
      do ptrans <- translate $ mbMap2 (ValPerm_Named $ mbLift npn) args off
         return $ fmap (\case
                           (PTrans_Term _ t) ->
                             APTrans_NamedConj (mbLift npn) args off t
                           _ -> error "translateSimplImpl: Perm_NamedConj") ptrans
    [nuMP| Perm_LLVMFrame fp |] ->
      return $ mkImpTypeTrans0 $ APTrans_LLVMFrame fp
    [nuMP| Perm_LOwned ls tps_in tps_out ps_in ps_out |] ->
      case mbExprPermsMembers ps_out of
        Just vars_out ->
          do ectx <- infoCtx <$> ask
             let etps = exprCtxType ectx
             ttr_inF <- tpTransM $ ctxFunTypeTransM $ translate ps_in
             ttr_outF <- tpTransM $ ctxFunTypeTransM $ translate ps_out
             let tp = typeDescFromLRT $ piExprPermLRT etps ttr_inF ttr_outF
             return $ mkImpTypeTrans1 tp $ \t ->
               (APTrans_LOwned ls (mbLift tps_in) (mbLift tps_out) ps_in ps_out $
                mkLOwnedTrans ectx ttr_inF ttr_outF vars_out t)
        Nothing ->
          error "FIXME HERE NOWNOW: handle this error!"
    [nuMP| Perm_LOwnedSimple tps lops |] ->
      return $ mkImpTypeTrans0 $ APTrans_LOwnedSimple (mbLift tps) lops
    [nuMP| Perm_LCurrent l |] ->
      return $ mkImpTypeTrans0 $ APTrans_LCurrent l
    [nuMP| Perm_LFinished |] ->
      return $ mkImpTypeTrans0 APTrans_LFinished
    [nuMP| Perm_Struct ps |] ->
      fmap APTrans_Struct <$> translate ps
    [nuMP| Perm_Fun fun_perm |] ->
      translate fun_perm >>= \tp_desc ->
      return $ mkImpTypeTrans1 tp_desc (APTrans_Fun fun_perm .
                                        FunTransClos (typeDescLRT tp_desc))
    [nuMP| Perm_BVProp prop |] ->
      fmap APTrans_BVProp <$> translate prop
    [nuMP| Perm_Any |] -> return $ mkImpTypeTrans0 APTrans_Any

-- | Translate an array permission to a 'TypeTrans' for an array permission
-- translation, also returning the translations of the bitvector width as a
-- natural, the length of the array as a bitvector, and the type of the elements
-- of the translation of the array
translateLLVMArrayPerm :: (1 <= w, KnownNat w, TransInfo info) =>
                          Mb ctx (LLVMArrayPerm w) ->
                          TransM info ctx (OpenTerm,OpenTerm,SpecTerm,
                                           ImpTypeTrans (LLVMArrayPermTrans ctx w))
translateLLVMArrayPerm mb_ap =
  do let w = natVal2 mb_ap
     let w_term = natOpenTerm w
     sh_trans <- translate $ mbMapCl $(mkClosed [| Perm_LLVMBlock .
                                                 llvmArrayPermHead |]) mb_ap
     let elem_tp = typeTransType1Imp sh_trans
     len_term <- translate1Pure $ mbLLVMArrayLen mb_ap
     {-
     bs_trans <-
       listTypeTrans <$> mapM (translateLLVMArrayBorrow ap) (mbList bs) -}
     let arr_tp = bvVecTypeDesc w_term len_term $ typeTransTupleDesc sh_trans
     return (w_term, len_term, elem_tp,
             mkImpTypeTrans1 arr_tp
             ({- flip $ -} LLVMArrayPermTrans mb_ap len_term sh_trans
                           {- <*> bs_trans -}))

instance (1 <= w, KnownNat w, TransInfo info) =>
         Translate info ctx (LLVMArrayPerm w) (ImpTypeTrans
                                               (LLVMArrayPermTrans ctx w)) where
  translate mb_ap =
    (\(_,_,_,tp_trans) -> tp_trans) <$> translateLLVMArrayPerm mb_ap

{-
-- | Translate an 'LLVMArrayBorrow' into an 'LLVMArrayBorrowTrans'. This
-- requires a special-purpose function, instead of the 'Translate' class,
-- because it requires the array permission.
translateLLVMArrayBorrow :: (1 <= w, KnownNat w, TransInfo info) =>
                            Mb ctx (LLVMArrayPerm w) ->
                            Mb ctx (LLVMArrayBorrow w) ->
                            TransM info ctx (TypeTrans
                                             (LLVMArrayBorrowTrans ctx w))
translateLLVMArrayBorrow mb_ap mb_b =
  do let mb_props = mbMap2 llvmArrayBorrowInArrayBase mb_ap mb_b
     prop_trans <- mapM translate $ mbList mb_props
     return (LLVMArrayBorrowTrans mb_b <$> listTypeTrans prop_trans)
-}

instance TransInfo info =>
         Translate info ctx (ValuePerms ps) (ImpTypeTrans
                                             (PermTransCtx ctx ps)) where
  translate mb_ps = case mbMatch mb_ps of
    [nuMP| ValPerms_Nil |] -> return $ mkImpTypeTrans0 MNil
    [nuMP| ValPerms_Cons ps p |] ->
      liftA2 (:>:) <$> translate ps <*> translate p

-- Translate a DistPerms by translating its corresponding ValuePerms
instance TransInfo info =>
         Translate info ctx (DistPerms ps) (ImpTypeTrans
                                            (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms

instance TransInfo info =>
         Translate info ctx (TypedDistPerms ps) (ImpTypeTrans
                                                 (PermTransCtx ctx ps)) where
  translate = translate . mbDistPermsToValuePerms . fmap unTypeDistPerms

instance TransInfo info =>
         Translate info ctx (ExprPerms ps) (ImpTypeTrans
                                            (PermTransCtx ctx ps)) where
  translate mb_eps
    | Just mb_ps <- mbExprPermsToValuePerms mb_eps = translate mb_ps
  translate mb_ps =
    error ("Translating expression permissions that could not be converted " ++
           "to variable permissions:" ++ permPrettyString emptyPPInfo mb_ps)


instance HasPureTrans (ValuePerm a) where
  hasPureTrans p = case mbMatch p of
    [nuMP| ValPerm_Eq _ |] -> True
    [nuMP| ValPerm_Or p1 p2 |] -> hasPureTrans p1 && hasPureTrans p2
    [nuMP| ValPerm_Exists mb_p |] ->
      hasPureTrans (mbCombine RL.typeCtxProxies mb_p)
    [nuMP| ValPerm_Named _ args _ |] ->
      -- FIXME: this is technically incorrect, since a defined permission could
      -- unfold to an impure permission
      hasPureTrans args
    [nuMP| ValPerm_Conj ps |] -> hasPureTrans ps
    [nuMP| ValPerm_Var _ _ |] -> False
    [nuMP| ValPerm_False |] -> True

instance HasPureTrans (AtomicPerm a) where
  hasPureTrans mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fld |] -> hasPureTrans fld
    [nuMP| Perm_LLVMArray ap |] -> hasPureTrans $ mbLLVMArrayCellShape ap
    [nuMP| Perm_LLVMBlock bp |] -> hasPureTrans $ mbLLVMBlockShape bp
    [nuMP| Perm_LLVMFree _ |] -> True
    [nuMP| Perm_LLVMFunPtr _ _ |] -> False
    [nuMP| Perm_IsLLVMPtr |] -> True
    [nuMP| Perm_LLVMBlockShape sh |] -> hasPureTrans sh
    [nuMP| Perm_NamedConj _ args _ |] ->
      -- FIXME: this is technically incorrect, since a defined permission could
      -- unfold to an impure permission
      hasPureTrans args
    [nuMP| Perm_LLVMFrame _ |] -> True
    [nuMP| Perm_LOwned _ _ _ _ _ |] -> False
    [nuMP| Perm_LOwnedSimple _ _ |] -> True
    [nuMP| Perm_LCurrent _ |] -> True
    [nuMP| Perm_LFinished |] -> True
    [nuMP| Perm_Struct ps |] -> hasPureTrans ps
    [nuMP| Perm_Fun _ |] -> False
    [nuMP| Perm_BVProp _ |] -> True
    [nuMP| Perm_Any |] -> True

instance HasPureTrans (ValuePerms ps) where
  hasPureTrans p = case mbMatch p of
    [nuMP| MNil |] -> True
    [nuMP| ps :>: p' |] -> hasPureTrans ps && hasPureTrans p'

instance HasPureTrans (DistPerms ps) where
  hasPureTrans p = case mbMatch p of
    [nuMP| MNil |] -> True
    [nuMP| ps :>: VarAndPerm _ p' |] -> hasPureTrans ps && hasPureTrans p'

instance HasPureTrans (LLVMFieldPerm w sz) where
  hasPureTrans (mbMatch -> [nuMP| LLVMFieldPerm { llvmFieldContents = p } |]) =
    hasPureTrans p

emptyStackOpenTerm :: OpenTerm
emptyStackOpenTerm = globalOpenTerm "Prelude.emptyFunStack"

-- Translate a FunPerm to a pi-abstraction (FIXME HERE NOW: document translation)
instance TransInfo info =>
         Translate info ctx (FunPerm ghosts args gouts ret) TypeDesc where
  translate (mbMatch ->
             [nuMP| FunPerm ghosts args gouts ret perms_in perms_out |]) =
    let tops = appendCruCtx (mbLift ghosts) (mbLift args)
        tops_prxs = cruCtxProxies tops
        rets = CruCtxCons (mbLift gouts) (mbLift ret)
        rets_prxs = cruCtxProxies rets in
    (infoCtx <$> ask) >>= \ctx ->
    case RL.appendAssoc ctx tops_prxs rets_prxs of
      Refl ->
        fmap typeDescFromLRT $ piLRTExprCtxApp tops $
        arrowLRTPermCtx (mbCombine tops_prxs perms_in) $
        fmap typeDescLRT $
        translateRetType rets (mbCombine
                               (RL.append tops_prxs rets_prxs) perms_out)

-- | Lambda-abstraction over a permission
lambdaPermTrans :: TransInfo info => String -> Mb ctx (ValuePerm a) ->
                   (PermTrans ctx a -> TransM info ctx SpecTerm) ->
                   TransM info ctx SpecTerm
lambdaPermTrans str p f =
  translate p >>= \tptrans -> lambdaTransM str tptrans f

-- | Lambda-abstraction over a sequence of permissions
lambdaPermCtx :: TransInfo info => Mb ctx (ValuePerms ps) ->
                 (PermTransCtx ctx ps -> TransM info ctx SpecTerm) ->
                 TransM info ctx SpecTerm
lambdaPermCtx ps f =
  translate ps >>= \tptrans -> lambdaTransM "p" tptrans f

-- | Build a @LetRecType@ that abstracts the SAW terms for a sequence of value
-- permissions
arrowLRTPermCtx :: TransInfo info => Mb ctx (ValuePerms ps) ->
                   TransM info ctx OpenTerm ->
                   TransM info ctx OpenTerm
arrowLRTPermCtx ps body =
  translate ps >>= \tptrans -> arrowLRTTransM tptrans body

-- | Build a @LetRecType@ describing a monadic SAW core function that takes in:
-- values for all the expression types in an 'ExprTransCtx' as dependent
-- arguments using @LRT_FunDep@; and values for all the permissions described by
-- a 'PermTransCtx' relative to the expressions using @LRT_FunClos@. The return
-- type is described by a 'PermTransCtx' as well.
piExprPermLRT :: PureTypeTrans (ExprTransCtx ctx) ->
                 RelPermsTypeTrans ctx ps_in -> RelPermsTypeTrans ctx ps_out ->
                 OpenTerm
piExprPermLRT etps ptps_in_F ptps_out_F =
  piLRTTrans "e" etps $ \ectx ->
  arrowLRTTrans (ptps_in_F ectx) $
  typeDescLRT $ typeTransTupleDesc (ptps_out_F ectx)

-- | Build the return type for a function; FIXME: documentation
translateRetType :: TransInfo info => CruCtx rets ->
                    Mb (ctx :++: rets) (ValuePerms ps) ->
                    TransM info ctx TypeDesc
translateRetType rets ret_perms =
  do tptrans <- translateClosed rets
     sigmaTypeTransM "ret" tptrans (hasPureTrans ret_perms)
       (\ectx -> inExtMultiTransM ectx (typeTransTupleDesc <$>
                                        translate ret_perms))

-- | Build the return type for the function resulting from an entrypoint
translateEntryRetType :: TransInfo info =>
                         TypedEntry phase ext blocks tops rets args ghosts ->
                         TransM info ((tops :++: args) :++: ghosts) TypeDesc
translateEntryRetType (TypedEntry {..}
                       :: TypedEntry phase ext blocks tops rets args ghosts) =
  let mb_perms_out =
        mbCombine (cruCtxProxies typedEntryRets) $
        extMbMulti (cruCtxProxies typedEntryGhosts) $
        extMbMulti (cruCtxProxies typedEntryArgs) $
        mbSeparate @_ @tops (cruCtxProxies typedEntryRets) typedEntryPermsOut in
  translateRetType typedEntryRets mb_perms_out


----------------------------------------------------------------------
-- * The Implication Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to a corresponding SAW closure that is
-- bound to its translation if it has one: only those entrypoints marked as the
-- heads of strongly-connect components have translations as closures
data TypedEntryTrans ext blocks tops rets args ghosts =
  TypedEntryTrans { typedEntryTransEntry ::
                      TypedEntry TransPhase ext blocks tops rets args ghosts,
                    typedEntryTransClos :: Maybe (OpenTerm, SpecTerm) }

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks tops rets args =
  TypedBlockTrans { typedBlockTransEntries ::
                      [Some (TypedEntryTrans ext blocks tops rets args)] }

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks tops rets =
  RAssign (TypedBlockTrans ext blocks tops rets) blocks

-- | A dummy 'TypedBlockMapTrans' with no blocks
emptyTypedBlockMapTrans :: TypedBlockMapTrans () RNil RNil RNil
emptyTypedBlockMapTrans = MNil

-- | Look up the translation of an entry by entry ID
lookupEntryTrans :: TypedEntryID blocks args ->
                    TypedBlockMapTrans ext blocks tops rets ->
                    Some (TypedEntryTrans ext blocks tops rets args)
lookupEntryTrans entryID blkMap =
  maybe (error "lookupEntryTrans") id $
  find (\(Some entryTrans) ->
         entryID == typedEntryID (typedEntryTransEntry entryTrans)) $
  typedBlockTransEntries (RL.get (entryBlockMember entryID) blkMap)

-- | Look up the translation of an entry by entry ID and make sure that it has
-- the supplied ghost arguments
lookupEntryTransCast :: TypedEntryID blocks args -> CruCtx ghosts ->
                        TypedBlockMapTrans ext blocks tops rets ->
                        TypedEntryTrans ext blocks tops rets args ghosts
lookupEntryTransCast entryID ghosts blkMap
  | Some entry_trans <- lookupEntryTrans entryID blkMap
  , Just Refl <- testEquality ghosts (typedEntryGhosts $
                                      typedEntryTransEntry entry_trans)
  = entry_trans
lookupEntryTransCast _ _ _ =
  error "lookupEntryTransCast: incorrect ghosts argument"

-- | A 'TypedCallSite' with existentially quantified ghost variables
data SomeTypedCallSite blocks tops args vars =
  forall ghosts.
  SomeTypedCallSite (TypedCallSite TransPhase blocks tops args ghosts vars)

-- | Look up a call site by id in a 'TypedBlockMapTrans'
lookupCallSite :: TypedCallSiteID blocks args vars ->
                  TypedBlockMapTrans ext blocks tops rets ->
                  SomeTypedCallSite blocks tops args vars
lookupCallSite siteID blkMap
  | Some entry_trans <- lookupEntryTrans (callSiteDest siteID) blkMap
  , Just site <- typedEntryCallerSite siteID (typedEntryTransEntry entry_trans)
  = SomeTypedCallSite site
lookupCallSite siteID blkMap
  | Some entry_trans <- lookupEntryTrans (callSiteDest siteID) blkMap =
    error ("lookupCallSite: no call site for site ID: " ++ show siteID ++
           "\n" ++ "call sites for entrypoint: " ++
           show (map (\(Some site) -> show $ typedCallSiteID site)
                 (typedEntryCallers $ typedEntryTransEntry entry_trans)))


-- | Contextual info for an implication translation
data ImpTransInfo ext blocks tops rets ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiPermStackVars :: RAssign (Member ctx) ps,
    itiPermEnv :: PermEnv,
    itiBlockMapTrans :: TypedBlockMapTrans ext blocks tops rets,
    itiReturnType :: TypeDesc,
    itiChecksFlag :: ChecksFlag
  }

instance TransInfo (ImpTransInfo ext blocks tops rets ps) where
  infoCtx = itiExprCtx
  infoEnv = itiPermEnv
  infoChecksFlag = itiChecksFlag
  extTransInfo etrans (ImpTransInfo {..}) =
    ImpTransInfo
    { itiExprCtx = itiExprCtx :>: etrans
    , itiPermCtx = consPermTransCtx (extPermTransCtx etrans itiPermCtx) PTrans_True
    , itiPermStack = extPermTransCtx etrans itiPermStack
    , itiPermStackVars = RL.map Member_Step itiPermStackVars
    , .. }


-- | The monad for impure translations
type ImpTransM ext blocks tops rets ps =
  TransM (ImpTransInfo ext blocks tops rets ps)

-- | Run an 'ImpTransM' computation in a 'TypeTransM' context (FIXME: better
-- documentation; e.g., the pctx starts on top of the stack)
impTransM :: forall ctx ps ext blocks tops rets a.
             RAssign (Member ctx) ps -> PermTransCtx ctx ps ->
             TypedBlockMapTrans ext blocks tops rets -> TypeDesc ->
             ImpTransM ext blocks tops rets ps ctx a ->
             TypeTransM ctx a
impTransM pvars pctx mapTrans retType =
  withInfoM $ \(TypeTransInfo ectx penv pflag) ->
  ImpTransInfo { itiExprCtx = ectx,
                 itiPermCtx = RL.map (const $ PTrans_True) ectx,
                 itiPermStack = pctx,
                 itiPermStackVars = pvars,
                 itiPermEnv = penv,
                 itiBlockMapTrans = mapTrans,
                 itiReturnType = retType,
                 itiChecksFlag = pflag
               }

-- | Run an inner 'ImpTransM' computation that does not use the block map
emptyBlocksImpTransM :: ImpTransM () RNil RNil RNil ps ctx a ->
                        ImpTransM ext blocks tops rets ps ctx a
emptyBlocksImpTransM =
  withInfoM (\(ImpTransInfo {..}) ->
              ImpTransInfo { itiBlockMapTrans = emptyTypedBlockMapTrans, .. })

-- | Run an implication translation computation in an "empty" environment, where
-- there are no variables in scope and no permissions held anywhere
inEmptyEnvImpTransM :: ImpTransM ext blocks tops rets RNil RNil a ->
                       ImpTransM ext blocks tops rets ps ctx a
inEmptyEnvImpTransM =
  withInfoM (\(ImpTransInfo {..}) ->
              ImpTransInfo { itiExprCtx = MNil, itiPermCtx = MNil,
                             itiPermStack = MNil, itiPermStackVars = MNil, .. })

-- | Get most recently bound variable
getTopVarM :: ImpTransM ext blocks tops rets ps (ctx :> tp) (ExprTrans tp)
getTopVarM = (\(_ :>: p) -> p) <$> itiExprCtx <$> ask

-- | Get the top permission on the stack
getTopPermM :: ImpTransM ext blocks tops rets (ps :> tp) ctx (PermTrans ctx tp)
getTopPermM = (\(_ :>: p) -> p) <$> itiPermStack <$> ask

-- | Helper to disambiguate the @ext@ type variable
getExtReprM :: PermCheckExtC ext exprExt =>
               ImpTransM ext blocks tops rets ps ctx (ExtRepr ext)
getExtReprM = return knownRepr

-- | Apply a transformation to the (translation of the) current perm stack
withPermStackM :: (RAssign (Member ctx) ps_in -> RAssign (Member ctx) ps_out) ->
                  (PermTransCtx ctx ps_in -> PermTransCtx ctx ps_out) ->
                  ImpTransM ext blocks tops rets ps_out ctx a ->
                  ImpTransM ext blocks tops rets ps_in ctx a
withPermStackM f_vars f_p =
  withInfoM $ \info ->
  info { itiPermStack = f_p (itiPermStack info),
         itiPermStackVars = f_vars (itiPermStackVars info) }

-- | Get the current permission stack as a 'DistPerms' in context
getPermStackDistPerms :: ImpTransM ext blocks tops rets ps ctx
                         (Mb ctx (DistPerms ps))
getPermStackDistPerms =
  do stack <- itiPermStack <$> ask
     stack_vars <- itiPermStackVars <$> ask
     prxs <- RL.map (const Proxy) <$> itiPermCtx <$> ask
     return $
       (nuMulti prxs $ \ns ->
         valuePermsToDistPerms (RL.map (flip RL.get ns) stack_vars))
       `mbApply`
       permTransCtxPerms prxs stack

-- | Run a computation if the current 'ChecksFlag' is set
ifChecksFlagM :: ImpTransM ext blocks tops rets ps ctx () ->
                 ImpTransM ext blocks tops rets ps ctx ()
ifChecksFlagM m =
  (itiChecksFlag <$> ask) >>= \checks ->
  if checksFlagSet checks then m else return ()

-- | Assert a property of the current permission stack, raising an 'error' if it
-- fails to hold. The 'String' names the construct being translated.
assertPermStackM :: HasCallStack => String ->
                    (RAssign (Member ctx) ps -> PermTransCtx ctx ps -> Bool) ->
                    ImpTransM ext blocks tops rets ps ctx ()
assertPermStackM nm f =
  ifChecksFlagM
  (ask >>= \info ->
   if f (itiPermStackVars info) (itiPermStack info) then return () else
     error ("translate: " ++ nm ++ nlPrettyCallStack callStack))

-- | Assert that the top portion of the current permission stack equals the
-- given 'DistPerms'
assertPermStackTopEqM :: HasCallStack => ps ~ (ps1 :++: ps2) =>
                         String -> f ps1 -> Mb ctx (DistPerms ps2) ->
                         ImpTransM ext blocks tops rets ps ctx ()
assertPermStackTopEqM nm prx expected =
  ifChecksFlagM
  (getPermStackDistPerms >>= \perms ->
   let actuals =
         fmap (snd . splitDistPerms prx (mbDistPermsToProxies expected)) perms in
   if expected == actuals then return () else
     error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
            permPrettyString emptyPPInfo expected ++
            "\nFound permission stack:\n" ++
            permPrettyString emptyPPInfo actuals ++
            nlPrettyCallStack callStack))

-- | Assert that the current permission stack equals the given 'DistPerms'
assertPermStackEqM :: HasCallStack => String -> Mb ctx (DistPerms ps) ->
                      ImpTransM ext blocks tops rets ps ctx ()
assertPermStackEqM nm perms =
  -- FIXME: unify this function with assertPermStackTopEqM
  ifChecksFlagM
  (getPermStackDistPerms >>= \stack_perms ->
   if perms == stack_perms then return () else
     error ("assertPermStackEqM (" ++ nm ++ "): expected permission stack:\n" ++
            permPrettyString emptyPPInfo perms ++
            "\nFound permission stack:\n" ++
            permPrettyString emptyPPInfo stack_perms ++
            nlPrettyCallStack callStack))

-- | Assert that the top permission is as given by the arguments
assertTopPermM :: HasCallStack => String -> Mb ctx (ExprVar a) ->
                  Mb ctx (ValuePerm a) ->
                  ImpTransM ext blocks tops rets (ps :> a) ctx ()
assertTopPermM nm x p =
  ifChecksFlagM
  (getPermStackDistPerms >>= \stack_perms ->
   case mbMatch stack_perms of
     [nuMP| DistPermsCons _ x' p' |] | x == x' && p == p' -> return ()
     [nuMP| DistPermsCons _ x' p' |] ->
       error ("assertTopPermM (" ++ nm ++ "): expected top permissions:\n" ++
              permPrettyString emptyPPInfo (mbMap2 distPerms1 x p) ++
              "\nFound top permissions:\n" ++
              permPrettyString emptyPPInfo (mbMap2 distPerms1 x' p') ++
              nlPrettyCallStack callStack ++
              "\nCurrent perm stack:\n" ++
              permPrettyString emptyPPInfo stack_perms))

-- | Get the (translation of the) perms for a variable
getVarPermM :: Mb ctx (ExprVar tp) ->
               ImpTransM ext blocks tops rets ps ctx (PermTrans ctx tp)
getVarPermM x = RL.get (translateVar x) <$> itiPermCtx <$> ask

-- | Assert that a variable has a given permission
assertVarPermM :: HasCallStack => String -> Mb ctx (ExprVar tp) ->
                  Mb ctx (ValuePerm tp) ->
                  ImpTransM ext blocks tops rets ps ctx ()
assertVarPermM nm x p =
  do x_p <- permTransPerm (mbToProxy p) <$> getVarPermM x
     if x_p == p then return () else
       error ("assertVarPermM (" ++ nm ++ "):\n" ++
              "expected: " ++ permPrettyString emptyPPInfo p ++ "\n" ++
              "found:" ++ permPrettyString emptyPPInfo x_p ++
              nlPrettyCallStack callStack)

-- | Set the (translation of the) perms for a variable in a computation
setVarPermM :: Mb ctx (ExprVar tp) -> PermTrans ctx tp ->
               ImpTransM ext blocks tops rets ps ctx a ->
               ImpTransM ext blocks tops rets ps ctx a
setVarPermM x p =
  local $ \info -> info { itiPermCtx =
                            RL.set (translateVar x) p $ itiPermCtx info }

-- | Clear all permissions in the permission variable map in a sub-computation,
-- leaving only those permissions on the top of the stack
clearVarPermsM :: ImpTransM ext blocks tops rets ps ctx a ->
                  ImpTransM ext blocks tops rets ps ctx a
clearVarPermsM =
  local $ \info -> info { itiPermCtx =
                            RL.map (const PTrans_True) $ itiPermCtx info }


-- | Build a term @bindS m k@ with the given @m@ of type @m_tp@ and where @k@
-- is build as a lambda with the given variable name and body
bindSpecMTransM :: SpecTerm -> ImpTypeTrans tr -> String ->
                   (tr -> ImpTransM ext blocks tops rets ps ctx SpecTerm) ->
                   ImpTransM ext blocks tops rets ps ctx SpecTerm
bindSpecMTransM m m_tp str f =
  do ret_tp <- returnTypeM
     k_tm <- lambdaTransM str m_tp f
     return $ bindSpecTerm (typeTransType1Imp m_tp) ret_tp m k_tm

-- | The current non-monadic return type as a type description
returnTypeDescM :: ImpTransM ext blocks tops rets ps_out ctx TypeDesc
returnTypeDescM = itiReturnType <$> ask

-- | The current non-monadic return type as a term
returnTypeM :: ImpTransM ext blocks tops rets ps_out ctx SpecTerm
returnTypeM = typeDescType <$> returnTypeDescM

-- | Build the monadic return type @SpecM E evRetType stack ret@ as a type
-- description, where @ret@ is the current return type in 'itiReturnType'
compReturnTypeDescM :: ImpTransM ext blocks tops rets ps_out ctx TypeDesc
compReturnTypeDescM = specMTypeDesc <$> returnTypeDescM

-- | Build the monadic return type @SpecM E evRetType stack ret@, where @ret@ is
-- the current return type in 'itiReturnType'
compReturnTypeM :: ImpTransM ext blocks tops rets ps_out ctx SpecTerm
compReturnTypeM = typeDescType <$> compReturnTypeDescM

-- | Like 'compReturnTypeM' but build a 'TypeTrans'
compReturnTypeTransM ::
  ImpTransM ext blocks tops rets ps_out ctx (ImpTypeTrans SpecTerm)
compReturnTypeTransM = mkTermImpTypeTrans <$> compReturnTypeDescM

-- | Build an @errorS@ computation with the given error message
mkErrorComp :: String -> ImpTransM ext blocks tops rets ps_out ctx SpecTerm
mkErrorComp msg =
  do ret_tp <- returnTypeM
     return $ errorSpecTerm ret_tp (pack msg)

-- | The typeclass for the implication translation of a functor at any
-- permission set inside any binding to an 'OpenTerm'
class NuMatchingAny1 f => ImplTranslateF f ext blocks tops rets where
  translateF :: Mb ctx (f ps) -> ImpTransM ext blocks tops rets ps ctx SpecTerm


----------------------------------------------------------------------
-- * Translating Permission Implication Constructs
----------------------------------------------------------------------

-- | A failure continuation represents any catch that is around the current
-- 'PermImpl', and can either be a term to jump to / call (meaning that there is
-- a catch) or an error message (meaning there is not)
data ImplFailCont
     -- | A continuation that calls a term on failure
  = ImplFailContTerm SpecTerm
    -- | An error message to print on failure
  | ImplFailContMsg String

-- | Convert an 'ImplFailCont' to an error, which should have the given type
implFailContTerm :: SpecTerm -> ImplFailCont -> SpecTerm
implFailContTerm _ (ImplFailContTerm t) = t
implFailContTerm tp (ImplFailContMsg msg) = errorSpecTerm tp (pack msg)

-- | Convert an 'ImplFailCont' to an error as in 'implFailContTerm', but use an
-- alternate error message in the case of 'ImplFailContMsg'
implFailAltContTerm :: SpecTerm -> String -> ImplFailCont -> SpecTerm
implFailAltContTerm _ _ (ImplFailContTerm t) = t
implFailAltContTerm tp msg (ImplFailContMsg _) = errorSpecTerm tp (pack msg)

-- | The type of terms use to translation permission implications, which can
-- contain calls to the current failure continuation
newtype PImplTerm ext blocks tops rets ps ctx =
  PImplTerm { popPImplTerm ::
                ImplFailCont -> ImpTransM ext blocks tops rets ps ctx SpecTerm }
  deriving OpenTermLike

-- | Build a 'PImplTerm' from the first 'PImplTerm' that uses the second as the
-- failure continuation
catchPImplTerm :: PImplTerm ext blocks tops rets ps ctx ->
                  PImplTerm ext blocks tops rets ps ctx ->
                  PImplTerm ext blocks tops rets ps ctx
catchPImplTerm t t_catch =
  PImplTerm $ \k ->
  compReturnTypeM >>= \tp ->
  letTransM "catchpoint" tp (popPImplTerm t_catch k) $ \k_tm ->
  popPImplTerm t $ ImplFailContTerm k_tm

-- | The failure 'PImplTerm', which immediately calls its failure continuation
failPImplTerm :: PImplTerm ext blocks tops rets ps ctx
failPImplTerm =
  PImplTerm $ \k -> compReturnTypeM >>= \tp -> return (implFailContTerm tp k)

-- | Return the failure 'PImplTerm' like 'failPImplTerm' but use an alternate
-- error message in the case that the failure continuation is an error message
failPImplTermAlt :: String -> PImplTerm ext blocks tops rets ps ctx
failPImplTermAlt msg = PImplTerm $ \k ->
  compReturnTypeM >>= \tp ->
  return (implFailContTerm tp (case k of
                                  ImplFailContMsg _ -> ImplFailContMsg msg
                                  _ -> k))

-- | "Force" an optional 'PImplTerm' to a 'PImplTerm' by converting a 'Nothing'
-- to the 'failPImplTerm'
forcePImplTerm :: Maybe (PImplTerm ext blocks tops rets ps ctx) ->
                  PImplTerm ext blocks tops rets ps ctx
forcePImplTerm (Just t) = t
forcePImplTerm Nothing = failPImplTerm


-- | A flag to indicate whether a 'PImplTerm' calls its failure continuation
data HasFailures = HasFailures | NoFailures deriving Eq

instance Semigroup HasFailures where
  HasFailures <> _ = HasFailures
  _ <> HasFailures = HasFailures
  NoFailures <> NoFailures = NoFailures

instance Monoid HasFailures where
  mempty = NoFailures

-- | FIXME HERE NOW: docs!
data CtxExt ctx1 ctx2 where
  CtxExt :: RAssign Proxy ctx3 -> CtxExt ctx1 (ctx1 :++: ctx3)

reflCtxExt :: CtxExt ctx ctx
reflCtxExt = CtxExt MNil

extCtxExt :: Proxy ctx1 -> RAssign Proxy ctx2 -> CtxExt (ctx1 :++: ctx2) ctx3 ->
             CtxExt ctx1 ctx3
extCtxExt ctx1 ctx2 (CtxExt ctx4)
  | Refl <- RL.appendAssoc ctx1 ctx2 ctx4
  = CtxExt (RL.append ctx2 ctx4)

ctxExtToExprExt :: CtxExt ctx1 ctx2 -> ExprTransCtx ctx2 ->
                   ExprCtxExt ctx1 ctx2
ctxExtToExprExt ((CtxExt ctx3) :: CtxExt ctx1 ctx2) ectx =
  ExprCtxExt $ snd $ RL.split (Proxy :: Proxy ctx1) ctx3 ectx

-- | A function for translating an @r@
newtype ImpRTransFun r ext blocks tops rets ctx =
  ImpRTransFun { appImpTransFun ::
                   forall ps ctx'. CtxExt ctx ctx' -> Mb ctx' (r ps) ->
                   ImpTransM ext blocks tops rets ps ctx' SpecTerm }

extImpRTransFun :: RAssign Proxy ctx' ->
                   ImpRTransFun r ext blocks tops rets ctx ->
                   ImpRTransFun r ext blocks tops rets (ctx :++: ctx')
extImpRTransFun ctx' f =
  ImpRTransFun $ \cext mb_r ->
  appImpTransFun f (extCtxExt Proxy ctx' cext) mb_r


-- | A monad transformer that adds an 'ImpRTransFun' translation function
newtype ImpRTransFunT r ext blocks tops rets ctx m a =
  ImpRTransFunT { unImpRTransFunT ::
                    ReaderT (ImpRTransFun r ext blocks tops rets ctx) m a }
  deriving (Functor, Applicative, Monad, MonadTrans)

-- | Run an 'ImpRTransFunT' computation to get an underlying computation in @m@
runImpRTransFunT :: ImpRTransFunT r ext blocks tops rets ctx m a ->
                    ImpRTransFun r ext blocks tops rets ctx -> m a
runImpRTransFunT m = runReaderT (unImpRTransFunT m)

-- | Map the underlying computation type of an 'ImpRTransFunT'
mapImpRTransFunT :: (m a -> n b) ->
                    ImpRTransFunT r ext blocks tops rets ctx m a ->
                    ImpRTransFunT r ext blocks tops rets ctx n b
mapImpRTransFunT f = ImpRTransFunT . mapReaderT f . unImpRTransFunT

-- | The computation type for translation permission implications, which
-- includes the following effects: a 'MaybeT' for representing terms that
-- translate to errors using 'Nothing'; a 'WriterT' that tracks all the error
-- messages used in translating a term along with a 'HasFailures' flag that
-- indicates whether the returned 'PImplTerm' uses its failure continuation; and
-- an 'ImpRTransFunT' to pass along a function for translating the final @r@
-- result inside the current 'PermImpl'
type PImplTransM r ext blocks tops rets ctx =
  MaybeT (WriterT ([String], HasFailures)
          (ImpRTransFunT r ext blocks tops rets ctx Identity))

-- | Run a 'PermImplTransM' computation
runPermImplTransM ::
  PImplTransM r ext blocks tops rets ctx a ->
  ImpRTransFun r ext blocks tops rets ctx ->
  (Maybe a, ([String], HasFailures))
runPermImplTransM m rTransFun =
  runIdentity $ runImpRTransFunT (runWriterT $ runMaybeT m) rTransFun

extPermImplTransM :: RAssign Proxy ctx' ->
                     PImplTransM r ext blocks tops rets (ctx :++: ctx') a ->
                     PImplTransM r ext blocks tops rets ctx a
extPermImplTransM ctx' m =
  pimplRTransFunM >>= \rtransFun ->
  MaybeT $ WriterT $ return $ runPermImplTransM m $ extImpRTransFun ctx' rtransFun

{-
extPermImplTransM :: ExprTransCtx ctx' ->
                     PImplTransM r ext blocks tops rets ps (ctx :++: ctx') a ->
                     PImplTransM r ext blocks tops rets ps ctx a
extPermImplTransM ctx' m =
  pimplRTransFunM >>= \rtransFun ->
  MaybeT $ WriterT $ return $ runPermImplTransM m $ extImpRTransFun ctx' rtransFun

extPermImplTransMTerm :: CruCtx ctx' ->
                         PImplTransMTerm r ext blocks tops rets ps (ctx :++: ctx') ->
                         PImplTransMTerm r ext blocks tops rets ps ctx
extPermImplTransMTerm ctx' m =
  MaybeT $ WriterT $ ImpRTransFun $ reader $ \rtransFun -> PImplTerm $ \k ->
  TransM $ reader $ \info ->
  let ectx' = runTransM (translateClosed ctx') info in
  return $ runPermImplTransM m $ extImpRTransFun ectx' rtransFun
-}

-- | Look up the @r@ translation function
pimplRTransFunM :: PImplTransM r ext blocks tops rets ctx
                   (ImpRTransFun r ext blocks tops rets ctx)
pimplRTransFunM = lift $ lift $ ImpRTransFunT ask

-- | Build an error term by recording the error message and returning 'Nothing'
pimplFailM :: String -> PImplTransM r ext blocks tops rets ctx a
pimplFailM msg = tell ([msg],HasFailures) >> mzero

-- | Catch a potential 'Nothing' return value in a 'PImplTransM' computation
pimplCatchM :: PImplTransM r ext blocks tops rets ctx a ->
               PImplTransM r ext blocks tops rets ctx (Maybe a)
pimplCatchM m = lift $ runMaybeT m

-- | Prepend a 'String' to all error messages generated in a computation
pimplPrependMsgM :: String -> PImplTransM r ext blocks tops rets ctx a ->
                    PImplTransM r ext blocks tops rets ctx a
pimplPrependMsgM str m =
  pass ((, (\(msgs, hasfs) -> (map (str++) msgs, hasfs))) <$> m)

type PImplTransMTerm r ext blocks tops rets ps ctx =
  PImplTransM r ext blocks tops rets ctx
  (PImplTerm ext blocks tops rets ps ctx)

-- | Run the first 'PImplTransM' computation to produce a 'PImplTerm' and use
-- the second computation to generate the failure continuation of that first
-- 'PImplTerm', using optimizations to omit the first or second term when it is
-- not needed.
pimplHandleFailM :: PImplTransMTerm r ext blocks tops rets ps ctx ->
                    PImplTransMTerm r ext blocks tops rets ps ctx ->
                    PImplTransMTerm r ext blocks tops rets ps ctx
pimplHandleFailM m m_catch =
  do
    -- Run the default computation m, exposing whether it returned a term or not
    -- and whether it calls the failure continuation or not
     (maybe_t, (fails,hasf)) <- lift $ lift $ runWriterT $ runMaybeT m
     -- We want to retain all failure messages from m, but we are handling any
     -- calls to the failure continuation, so we are NoFailures for now
     tell (fails, NoFailures)
     case (maybe_t, hasf) of
       (Just t, NoFailures) ->
         -- If t does not call the failure continuation, then we have no need to
         -- use m_catch, and we just return t
         return t
       (Just t, HasFailures) ->
         -- If t does potentially call the failure continuation, then let-bind
         -- the result of m_catch as its failure continuation; note that we
         -- preserve any MaybeT and WriterT effects of m_catch, meaning that its
         -- failure messages and HasFailures flag are preserved, and if it
         -- returns Nothing then so will this entire computation
         do maybe_t_catch <- lift $ runMaybeT m_catch
            case maybe_t_catch of
              Just t_catch -> return $ catchPImplTerm t t_catch
              Nothing -> return t
       (Nothing, _) ->
         -- If t definitely fails, then just use m_catch
         m_catch


-- | Translate the output permissions of a 'SimplImpl'
translateSimplImplOut :: Mb ctx (SimplImpl ps_in ps_out) ->
                         ImpTransM ext blocks tops rets ps ctx
                         (ImpTypeTrans (PermTransCtx ctx ps_out))
translateSimplImplOut = translate . mbSimplImplOut

-- | Translate the head output permission of a 'SimplImpl'
translateSimplImplOutHead :: Mb ctx (SimplImpl ps_in (ps_out :> a)) ->
                             ImpTransM ext blocks tops rets ps ctx
                             (ImpTypeTrans (PermTrans ctx a))
translateSimplImplOutHead =
  translate . mbMapCl $(mkClosed [| varAndPermPerm . RL.head |]) . mbSimplImplOut

-- | Translate the head of the tail of the output permission of a 'SimplImpl'
translateSimplImplOutTailHead :: Mb ctx (SimplImpl ps_in (ps_out :> a :> b)) ->
                                 ImpTransM ext blocks tops rets ps ctx
                                 (ImpTypeTrans (PermTrans ctx a))
translateSimplImplOutTailHead =
  translate . mbMapCl $(mkClosed [| varAndPermPerm . RL.head . RL.tail |])
  . mbSimplImplOut

-- | Translate a 'SimplImpl' to a function on translation computations
translateSimplImpl ::
  Proxy ps -> Mb ctx (SimplImpl ps_in ps_out) ->
  ImpTransM ext blocks tops rets (ps :++: ps_out) ctx SpecTerm ->
  ImpTransM ext blocks tops rets (ps :++: ps_in) ctx SpecTerm
translateSimplImpl (ps0 :: Proxy ps0) mb_simpl m = case mbMatch mb_simpl of
  [nuMP| SImpl_Drop _ _ |] ->
    withPermStackM (\(xs :>: _) -> xs) (\(ps :>: _) -> ps) m

  [nuMP| SImpl_Copy x _ |] ->
    withPermStackM (:>: translateVar x) (\(ps :>: p) -> ps :>: p :>: p) m

  [nuMP| SImpl_Swap _ _ _ _ |] ->
    withPermStackM (\(xs :>: x :>: y) -> xs :>: y :>: x)
    (\(pctx :>: px :>: py) -> pctx :>: py :>: px)
    m

  [nuMP| SImpl_MoveUp (mb_ps1 :: DistPerms ps1) (_mb_x :: ExprVar a) _
                      (mb_ps2 :: DistPerms ps2) |] ->
    let ps1 = mbRAssignProxies mb_ps1
        ps2 = mbRAssignProxies mb_ps2
        prxa = Proxy :: Proxy a
        prx0a = Proxy :: Proxy (ps0 :> a) in
    case (RL.appendRNilConsEq ps0 prxa (RL.append ps1 ps2)) of
      Refl ->
        withPermStackM
        (\xs ->
          let ((xs0 :>: x), xs12) = RL.split prx0a (RL.append ps1 ps2) xs
              (xs1, xs2) = RL.split ps1 ps2 xs12 in
          RL.append xs0 $ RL.append (xs1 :>: x) xs2)
        (\pctx ->
          let ((pctx0 :>: ptrans), pctx12) =
                RL.split prx0a (RL.append ps1 ps2) pctx
              (pctx1, pctx2) = RL.split ps1 ps2 pctx12 in
          RL.append pctx0 $ RL.append (pctx1 :>: ptrans) pctx2)
        m

  [nuMP| SImpl_MoveDown mb_ps1 (mb_x :: ExprVar a) _ mb_ps2 |]
    | prx_a <- mbLift $ fmap (const (Proxy :: Proxy a)) mb_x
    , ps1 <- mbRAssignProxies mb_ps1
    , ps1a <- ps1 :>: prx_a
    , ps2 <- mbRAssignProxies mb_ps2
    , Refl <- RL.appendRNilConsEq ps0 prx_a (RL.append ps1 ps2) ->
      withPermStackM
      (\xs ->
        let (xs0, xs1a2) = RL.split ps0 (RL.append ps1a ps2) xs
            ((xs1 :>: x), xs2) = RL.split ps1a ps2 xs1a2 in
        RL.append xs0 (RL.append (MNil :>: x) $ RL.append xs1 xs2))
      (\pctx ->
        let (pctx0, pctx1a2) = RL.split ps0 (RL.append ps1a ps2) pctx
            ((pctx1 :>: ptrans), pctx2) = RL.split ps1a ps2 pctx1a2 in
        RL.append pctx0 (RL.append (MNil :>: ptrans) $ RL.append pctx1 pctx2))
      m

  [nuMP| SImpl_IntroOrL _ p1 p2 |] ->
    do tp1 <- translate p1
       tp2 <- translate p2
       tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: typeTransF tptrans [leftTrans tp1 tp2 p_top])
         m

  [nuMP| SImpl_IntroOrR _ p1 p2 |] ->
    do tp1 <- translate p1
       tp2 <- translate p2
       tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(ps :>: p_top) ->
           ps :>: typeTransF tptrans [rightTrans tp1 tp2 p_top])
         m

  [nuMP| SImpl_IntroExists _ e p |] ->
    do let tp = mbExprType e
       tp_trans <- translateClosed tp
       out_trans <- translateSimplImplOutHead mb_simpl
       etrans <- translate e
       trm <- sigmaPermTransM "x_ex" tp_trans (mbCombine RL.typeCtxProxies p)
                              etrans getTopPermM
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF out_trans [trm])
         m

  [nuMP| SImpl_Cast _ _ _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: _ :>: ptrans) -> pctx :>: ptrans)
    m

  [nuMP| SImpl_CastPerm (_::ExprVar a) eqp |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       let prxs_a = MNil :>: (Proxy :: Proxy a)
       let prxs1 = mbLift $ mbMapCl $(mkClosed [| distPermsToProxies
                                                . eqProofPerms |]) eqp
       let prxs = RL.append prxs_a prxs1
       withPermStackM id
         (\pctx ->
           let (pctx1, pctx2) = RL.split ps0 prxs pctx in
           RL.append pctx1 (typeTransF ttrans (transTerms pctx2)))
         m

  [nuMP| SImpl_IntroEqRefl x |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_InvertEq _ y |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM ((:>: translateVar y) . RL.tail)
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_InvTransEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_UnitEq x _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m


  [nuMP| SImpl_CopyEq _ _ |] ->
    withPermStackM
    (\(vars :>: var) -> (vars :>: var :>: var))
    (\(pctx :>: ptrans) -> (pctx :>: ptrans :>: ptrans))
    m

  [nuMP| SImpl_LLVMWordEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_LLVMOffsetZeroEq x |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans []) m

  [nuMP| SImpl_IntroConj x |] ->
    withPermStackM (:>: translateVar x) (:>: PTrans_True) m

  [nuMP| SImpl_ExtractConj x _ mb_i |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_ExtractConj" ptrans
          i = mbLift mb_i in
      if i < length ps then
        pctx :>: PTrans_Conj [ps !! i]
        :>: PTrans_Conj (deleteNth i ps)
      else
        error "translateSimplImpl: SImpl_ExtractConj: index out of bounds")
    m

  [nuMP| SImpl_CopyConj x _ mb_i |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_CopyConj" ptrans
          i = mbLift mb_i in
      if i < length ps then pctx :>: PTrans_Conj [ps !! i] :>: ptrans else
        error "translateSimplImpl: SImpl_CopyConj: index out of bounds")
    m

  [nuMP| SImpl_InsertConj _ _ _ i |] ->
    withPermStackM RL.tail
    (\(pctx :>: ptransi :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_InsertConj" ptrans
          pi = unPTransConj1 "translateSimplImpl: SImpl_InsertConj" ptransi in
      pctx :>: PTrans_Conj (take (mbLift i) ps ++ pi : drop (mbLift i) ps))
    m

  [nuMP| SImpl_AppendConjs _ _ _ |] ->
    withPermStackM RL.tail
    (\(pctx :>: ptrans1 :>: ptrans2) ->
      let ps1 = unPTransConj "translateSimplImpl: SImpl_AppendConjs" ptrans1
          ps2 = unPTransConj "translateSimplImpl: SImpl_AppendConjs" ptrans2 in
      pctx :>: PTrans_Conj (ps1 ++ ps2))
    m

  [nuMP| SImpl_SplitConjs x _ mb_i |] ->
    let i = mbLift mb_i in
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      let ps = unPTransConj "translateSimplImpl: SImpl_SplitConjs" ptrans in
      pctx :>: PTrans_Conj (take i ps) :>: PTrans_Conj (drop i ps))
    m

  [nuMP| SImpl_IntroStructTrue x _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_StructEqToPerm _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_StructPermToEq _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_IntroStructField _ _ memb _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\case
             (pctx :>: PTrans_Conj [APTrans_Struct pctx_str] :>: ptrans) ->
               pctx :>: typeTransF tptrans (transTerms $
                                            RL.set (mbLift memb) ptrans pctx_str)
             _ -> error "translateSimplImpl: SImpl_IntroStructField")
         m

  [nuMP| SImpl_ConstFunPerm _ _ _ ident |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tptrans [globalTermLike $ mbLift ident])
         m

  [nuMP| SImpl_CastLLVMWord _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_InvertLLVMOffsetEq _ _ mb_y |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM
         (\(vars :>: _) -> (vars :>: translateVar mb_y))
         (\(pctx :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_OffsetLLVMWord _ _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM
         (\(vars :>: _ :>: x_var) -> vars :>: x_var)
         (\(pctx :>: _ :>: _) -> pctx :>: typeTransF tptrans [])
         m

  [nuMP| SImpl_CastLLVMPtr _ _ _ _ |] ->
    -- FIXME: offsetLLVMPerm can throw away conjuncts, like free and llvmfunptr
    -- permissions, that change the type of the translation
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: ptrans) ->
           pctx :>: typeTransF tptrans (transTerms ptrans))
         m

  [nuMP| SImpl_CastLLVMFree _ _ e2 |] ->
    withPermStackM RL.tail
    ((:>: PTrans_Conj [APTrans_LLVMFree e2]) . RL.tail . RL.tail)
    m

  [nuMP| SImpl_CastLLVMFieldOffset _ _ _ |] ->
    do tptrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans :>: _) ->
           pctx :>: typeTransF tptrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMFieldContents x _ mb_fld |] ->
    withPermStackM ((:>: translateVar x) . RL.tail . RL.tail)
    (\(pctx :>: _ :>: ptrans) ->
      pctx :>: PTrans_Conj [APTrans_LLVMField mb_fld ptrans])
    m

  [nuMP| SImpl_DemoteLLVMFieldRW _ mb_fld |] ->
    withPermStackM id
    (\(pctx :>: ptrans) ->
      let (_,ptrans') =
            unPTransLLVMField
            "translateSimplImpl: SImpl_DemoteLLVMFieldRW"
            knownNat ptrans in
      pctx :>: PTrans_Conj [
        APTrans_LLVMField
        (mbMapCl $(mkClosed [| \fld -> fld { llvmFieldRW = PExpr_Read } |]) mb_fld)
        ptrans'])
    m

  [nuMP| SImpl_SplitLLVMTrueField x _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM (:>: translateVar x)
         (\(pctx :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_TruncateLLVMTrueField _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_ConcatLLVMTrueFields _ _ _ |] ->
    do ttrans <- translateSimplImplOut mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) -> RL.append pctx $ typeTransF ttrans [])
         m

  [nuMP| SImpl_DemoteLLVMArrayRW _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_LLVMArrayCopy _ mb_ap _ _ |] ->
    do let mb_sub_ap =
             case mbSimplImplOut mb_simpl of
               [nuP| _ :>: VarAndPerm _ (ValPerm_LLVMArray sub_ap) :>: _ |] ->
                 sub_ap
               _ -> error "translateSimplImpl: SImpl_LLVMArrayCopy: unexpected perms"
       sub_ap_tp_trans <- translate mb_sub_ap
       rng_trans <- translate $ mbMap2 llvmSubArrayRange mb_ap mb_sub_ap
       -- let mb_sub_borrows = fmap llvmArrayBorrows mb_sub_ap
       withPermStackM id
         (\(pctx :>: ptrans_array :>: ptrans_props) ->
           let array_trans =
                 unPTransLLVMArray
                 "translateSimplImpl: SImpl_LLVMArrayCopy" ptrans_array
               prop_transs =
                 unPTransBVProps
                 "translateSimplImpl: SImpl_LLVMArrayCopy" ptrans_props in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $
                        getLLVMArrayTransSlice array_trans sub_ap_tp_trans
                        rng_trans {- mb_sub_borrows -} prop_transs]
           :>: ptrans_array)
         m

  [nuMP| SImpl_LLVMArrayBorrow _ mb_ap _ _ |] ->
    do let mb_sub_ap =
             case mbSimplImplOut mb_simpl of
               [nuP| _ :>: VarAndPerm _ (ValPerm_LLVMArray sub_ap) :>: _ |] ->
                 sub_ap
               _ -> error "translateSimplImpl: SImpl_LLVMArrayCopy: unexpected perms"
       sub_ap_tp_trans <- translate mb_sub_ap
       let mb_rng = mbMap2 llvmSubArrayRange mb_ap mb_sub_ap
       rng_trans <- translate mb_rng
       -- let mb_sub_borrows = fmap llvmArrayBorrows mb_sub_ap
       withPermStackM id
         (\(pctx :>: ptrans_array :>: ptrans_props) ->
           let array_trans =
                 unPTransLLVMArray
                 "translateSimplImpl: SImpl_LLVMArrayBorrow" ptrans_array
               prop_transs =
                 unPTransBVProps
                 "translateSimplImpl: SImpl_LLVMArrayBorrow" ptrans_props
               {- borrow_trans =
                 LLVMArrayBorrowTrans (fmap RangeBorrow mb_rng) prop_transs -}
               sub_array_trans =
                 APTrans_LLVMArray $
                 getLLVMArrayTransSlice array_trans sub_ap_tp_trans rng_trans
                 {- mb_sub_borrows -} prop_transs
               array_trans' =
                 array_trans {
                 llvmArrayTransPerm =
                     mbMap2 (\ap sub_ap ->
                              llvmArrayAddBorrow (llvmSubArrayBorrow ap sub_ap) $
                              llvmArrayRemArrayBorrows ap sub_ap)
                     mb_ap mb_sub_ap } in
           pctx :>:
           PTrans_Conj [sub_array_trans]
           :>: PTrans_Conj [APTrans_LLVMArray array_trans'])
         m

  [nuMP| SImpl_LLVMArrayReturn _ mb_ap mb_ret_ap |] ->
    do (_ :>: ptrans_sub_array :>: ptrans_array) <- itiPermStack <$> ask
       let mb_cell =
             fmap fromJust $ mbMap2 llvmArrayIsOffsetArray mb_ap mb_ret_ap
       cell_tm <- translate1 mb_cell
       let array_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayReturn" ptrans_array
       let sub_array_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayReturn" ptrans_sub_array
           {- borrow_i =
             mbLift $ mbMap2 llvmArrayFindBorrow (fmap
                                                  RangeBorrow mb_rng) mb_ap
           borrow_trans = llvmArrayTransBorrows array_trans !! borrow_i -}
       let array_trans' =
             (setLLVMArrayTransSlice array_trans sub_array_trans cell_tm)
             { llvmArrayTransPerm =
                 mbMap2 (\ap ret_ap ->
                          llvmArrayRemBorrow (llvmSubArrayBorrow ap ret_ap) $
                          llvmArrayAddArrayBorrows ap ret_ap) mb_ap mb_ret_ap }
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [APTrans_LLVMArray array_trans'])
         m

  [nuMP| SImpl_LLVMArrayAppend _ mb_ap1 mb_ap2 |] ->
    do (w_term, len1_tm, elem_tp, _) <- translateLLVMArrayPerm mb_ap1
       (_, len2_tm, _, _) <- translateLLVMArrayPerm mb_ap2
       tp_trans <- translateSimplImplOutHead mb_simpl
       len3_tm <-
         translate1 $
         fmap (\case
                  (ValPerm_LLVMArray ap) -> llvmArrayLen ap
                  _ -> error "translateSimplImpl: SImpl_LLVMArrayAppend") $
         fmap distPermsHeadPerm $ mbSimplImplOut mb_simpl
       (_ :>: ptrans1 :>: ptrans2) <- itiPermStack <$> ask
       let arr_out_comp_tm =
             applyTermLikeMulti (monadicSpecOp "Prelude.appendCastBVVecS")
             [openTermLike w_term, openTermLike len1_tm,
              openTermLike len2_tm, len3_tm, elem_tp,
              transTerm1 ptrans1, transTerm1 ptrans2]
       bindSpecMTransM arr_out_comp_tm tp_trans "appended_array" $ \ptrans_arr' ->
         withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                  pctx :>: ptrans_arr') m


  [nuMP| SImpl_LLVMArrayRearrange _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_LLVMArrayToField _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [])
         m

  [nuMP| SImpl_LLVMArrayEmpty x mb_ap |] ->
    do (w_tm, _, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       -- First we build a term of type Vec 0 elem_tp using EmptyVec
       let vec_tm = applyGlobalTermLike "Prelude.EmptyVec" [elem_tp]
       -- Next, we build a computation that casts it to BVVec w 0x0 elem_tp
       let w = fromIntegral $ natVal2 mb_ap
       let bvZero_nat_tm =
             openTermLike $
             applyGlobalOpenTerm "Prelude.bvToNat"
             [w_tm, bvLitOpenTerm (replicate w False)]
       let vec_cast_m =
             applyTermLikeMulti (monadicSpecOp "Prelude.castVecS")
             [elem_tp, natTermLike 0, bvZero_nat_tm, vec_tm]
       bindSpecMTransM vec_cast_m ap_tp_trans "empty_vec" $ \ptrans_arr ->
         withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: PTrans_Conj [APTrans_LLVMArray ptrans_arr])
         m

-- translate1/translateClosed ( zeroOfType <- get the default element )
  [nuMP| SImpl_LLVMArrayBorrowed x _ mb_ap |] ->
    do (w_tm, len_tm, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       withPermStackM (:>: translateVar x)
         (\(pctx :>: ptrans_block) ->
           let arr_term =
                 applyGlobalTermLike "Prelude.repeatBVVec"
                 [openTermLike w_tm, openTermLike len_tm,
                  elem_tp, transTerm1 ptrans_block] in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]] :>:
           ptrans_block)
         m

  [nuMP| SImpl_LLVMArrayFromBlock _ _ |] ->
    do mb_ap <-
         case mbSimplImplOut mb_simpl of
           [nuP| DistPermsCons _ _ (ValPerm_LLVMArray mb_ap) |] -> return mb_ap
           _ -> error ("translateSimplImpl: SImpl_LLVMArrayFromBlock: "
                       ++ "unexpected form of output permission")
       (w_tm, len_tm, elem_tp, ap_tp_trans) <- translateLLVMArrayPerm mb_ap
       withPermStackM id
         (\(pctx :>: ptrans_cell) ->
           let arr_term =
                 -- FIXME: this generates a BVVec of length (bvNat n 1), whereas
                 -- what we need is a BVVec of length [0,0,...,1]; the two are
                 -- provably equal but not convertible in SAW core
                 {-
                 applyOpenTermMulti (globalOpenTerm "Prelude.singletonBVVec")
                 [w_tm, elem_tp, transTerm1 ptrans_cell]
                 -}
                 applyGlobalTermLike "Prelude.repeatBVVec"
                 [openTermLike w_tm, openTermLike len_tm,
                  elem_tp, transTerm1 ptrans_cell] in
           pctx :>:
           PTrans_Conj [APTrans_LLVMArray $ typeTransF ap_tp_trans [arr_term]])
         m


  [nuMP| SImpl_LLVMArrayCellCopy _ _ mb_cell |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_props
       cell_tm <- translate1 mb_cell
       let cell_ptrans =
             getLLVMArrayTransCell arr_trans mb_cell cell_tm prop_transs
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [cell_ptrans] :>: ptrans_array)
         m

  [nuMP| SImpl_LLVMArrayCellBorrow _ mb_ap mb_cell |] ->
    do (_ :>: ptrans_array :>: ptrans_props) <- itiPermStack <$> ask
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellBorrow" ptrans_array
       let prop_transs =
             unPTransBVProps
             "translateSimplImpl: SImpl_LLVMArrayCellBorrow" ptrans_props
       cell_tm <- translate1 mb_cell
       let cell_ptrans =
             getLLVMArrayTransCell arr_trans mb_cell cell_tm prop_transs
       {- let b = LLVMArrayBorrowTrans (fmap FieldBorrow ix) prop_transs -}
       let arr_trans' =
             arr_trans { llvmArrayTransPerm =
                           mbMap2 (\ap cell ->
                                    llvmArrayAddBorrow (FieldBorrow cell) ap)
                           mb_ap mb_cell }
       withPermStackM id
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [cell_ptrans] :>:
           PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m

  [nuMP| SImpl_LLVMArrayCellReturn _ mb_ap mb_cell |] ->
    do (_ :>: ptrans_cell :>: ptrans_array) <- itiPermStack <$> ask
       let aptrans_cell = case ptrans_cell of
             PTrans_Conj [aptrans] -> aptrans
             _ -> error ("translateSimplImpl: SImpl_LLVMArrayCellReturn: "
                         ++ "found non-field perm where field perm was expected")
       let arr_trans =
             unPTransLLVMArray
             "translateSimplImpl: SImpl_LLVMArrayCellCopy" ptrans_array
       {- let b_trans = llvmArrayTransFindBorrow (fmap FieldBorrow cell) arr_trans -}
       cell_tm <- translate1 mb_cell
       let arr_trans' =
             (setLLVMArrayTransCell arr_trans cell_tm
              {- (llvmArrayBorrowTransProps b_trans) -} aptrans_cell)
             { llvmArrayTransPerm =
                 mbMap2 (\ap cell ->
                          llvmArrayRemBorrow (FieldBorrow cell) ap) mb_ap mb_cell }
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: PTrans_Conj [APTrans_LLVMArray arr_trans'])
         m

  [nuMP| SImpl_LLVMArrayContents _ mb_ap mb_sh impl |] ->
    do p_out_trans <- translateSimplImplOutHead mb_simpl
       (w_term, len_term, elem_tp, _) <- translateLLVMArrayPerm mb_ap
       cell_in_trans <-
         translate $ mbMapCl $(mkClosed [| ValPerm_LLVMBlock .
                                         llvmArrayPermHead |]) mb_ap
       cell_out_trans <-
         translate $ mbMap2 (\ap sh -> ValPerm_LLVMBlock $ llvmArrayPermHead $
                                       ap { llvmArrayCellShape = sh })
         mb_ap mb_sh
       impl_tm <-
         -- FIXME: this code just fabricates a pretend LLVM value for the
         -- arbitrary cell of the array that is used to substitute for the
         -- variable bound by the LocalPermImpl, which seems like a hack...
         inExtTransM ETrans_LLVM $
         translateCurryLocalPermImpl "Error mapping array cell permissions:"
         (mbCombine RL.typeCtxProxies impl) MNil MNil
         (fmap ((MNil :>:) . extPermTrans ETrans_LLVM) cell_in_trans)
         (MNil :>: Member_Base)
         (fmap ((MNil :>:) . extPermTrans ETrans_LLVM) cell_out_trans)
       -- Build the computation that maps impl_tm over the input array using the
       -- mapBVVecM monadic combinator
       ptrans_arr <- getTopPermM
       let arr_out_comp_tm =
             applyTermLikeMulti (monadicSpecOp "Prelude.mapBVVecS")
             [elem_tp, typeTransType1Imp cell_out_trans, impl_tm,
              openTermLike w_term, openTermLike len_term,
              transTerm1 ptrans_arr]
       -- Now use bindS to bind the result of arr_out_comp_tm in the remaining
       -- computation
       bindSpecMTransM arr_out_comp_tm p_out_trans "mapped_array" $ \ptrans_arr' ->
         withPermStackM id (\(pctx :>: _) -> pctx :>: ptrans_arr') m

  [nuMP| SImpl_LLVMFieldIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans_fld) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_fld)
    m

  [nuMP| SImpl_LLVMArrayIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans_array) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans_array)
    m

  [nuMP| SImpl_LLVMBlockIsPtr x _ |] ->
    withPermStackM (:>: translateVar x)
    (\(pctx :>: ptrans) ->
      pctx :>: PTrans_Conj [APTrans_IsLLVMPtr] :>: ptrans)
    m

  [nuMP| SImpl_SplitLifetime mb_x f args l mb_l2 _ _ _ _ _ |] ->
    -- FIXME HERE: get rid of the mbMaps!
    do let l2_e = fmap PExpr_Var mb_l2
       let f_l_args = mbMap3 ltFuncApply f args l
       let f_l2_min = mbMap2 ltFuncMinApply f l2_e
       let x_tp = mbVarType mb_x
       f_l2_args_trans <- translateSimplImplOutTailHead mb_simpl
       f_l_args_trans <- tpTransM $ ctxFunTypeTransM $ translate f_l_args
       f_l2_min_trans <- tpTransM $ ctxFunTypeTransM $ translate f_l2_min
       withPermStackM
         (\(ns :>: x :>: _ :>: l2) -> ns :>: x :>: l2)
         (\case
             (pctx :>: ptrans_x :>: _ :>:
              PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t)
               ->
               pctx :>: typeTransF f_l2_args_trans (transTerms ptrans_x) :>:
               PTrans_LOwned mb_ls (CruCtxCons tps_in x_tp)
               (CruCtxCons tps_out x_tp)
               (mbMap3 (\ps x p -> ps :>: ExprAndPerm (PExpr_Var x) p)
                mb_ps_in mb_x f_l2_min)
               (mbMap3 (\ps x p -> ps :>: ExprAndPerm (PExpr_Var x) p)
                mb_ps_out mb_x f_l_args)
               (weakenLOwnedTrans f_l2_min_trans f_l_args_trans t)
             _ ->
               panic "translateSimplImpl"
               ["In SImpl_SplitLifetime rule: expected an lowned permission"])
         m

  [nuMP| SImpl_SubsumeLifetime _ _ _ _ _ _ mb_l2 |] ->
    flip (withPermStackM id) m $ \case
    (pctx :>: PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t) ->
      pctx :>:
      PTrans_LOwned (mbMap2 (:) mb_l2 mb_ls) tps_in tps_out mb_ps_in mb_ps_out t
    _ ->
      panic "translateSimplImpl"
      ["In SImpl_SubsumeLifetime rule: expected an lowned permission"]

  [nuMP| SImpl_ContainedLifetimeCurrent _ _ _ _ _ _ _ |] ->
    do ttr_lcur <- translateSimplImplOutTailHead mb_simpl
       withPermStackM
         (\(ns :>: l1) -> ns :>: l1 :>: l1)
         (\(pctx :>: ptrans_l) ->
           pctx :>: typeTransF ttr_lcur [] :>: ptrans_l)
         m

  [nuMP| SImpl_RemoveContainedLifetime _ _ _ _ _ _ mb_l2 |] ->
    withPermStackM
    (\(ns :>: l :>: _) -> ns :>: l)
    (\case
        (pctx :>:
         PTrans_LOwned mb_ls tps_in tps_out mb_ps_in mb_ps_out t :>: _) ->
          let mb_ls' = mbMap2 (\l2 ls ->
                                delete (PExpr_Var l2) ls) mb_l2 mb_ls in
          pctx :>: PTrans_LOwned mb_ls' tps_in tps_out mb_ps_in mb_ps_out t
        _ ->
          panic "translateSimplImpl"
          ["In SImpl_RemoveContainedLifetime rule: expected an lowned permission"])
    m

  [nuMP| SImpl_WeakenLifetime _ _ _ _ _ |] ->
    do pctx_out_trans <- translateSimplImplOut mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: _) ->
           -- NOTE: lcurrent permissions have no term translations, so we can
           -- construct the output PermTransCtx by just passing the terms in
           -- ptrans_x to pctx_out_trans
           RL.append pctx (typeTransF pctx_out_trans $ transTerms ptrans_x))
         m

  [nuMP| SImpl_MapLifetime _ mb_ls tps_in tps_out _ _ tps_in' tps_out'
                           ps_in' ps_out' ps1 ps2 impl_in impl_out |] ->
    -- First, translate the various permissions and implications
    do ttr_inF' <- tpTransM $ ctxFunTypeTransM $ translate ps_in'
       ttr_outF' <- tpTransM $ ctxFunTypeTransM $ translate ps_out'
       ttr1F <- tpTransM $ ctxFunTypeTransM $ translate ps1
       ttr2F <- tpTransM $ ctxFunTypeTransM $ translate ps2
       t1 <-
         translateLOwnedPermImpl "Error mapping lowned input perms:" impl_in
       t2 <-
         translateLOwnedPermImpl "Error mapping lowned output perms:" impl_out

       -- Next, split out the various input permissions from the rest of the pctx
       let prxs1 = mbRAssignProxies ps1
       let prxs2 = mbRAssignProxies ps2
       let prxs_in = RL.append prxs1 prxs2 :>: Proxy
       let prxs_in' = cruCtxProxies $ mbLift tps_in'
       pctx <- itiPermStack <$> ask
       let (pctx0, pctx12 :>: ptrans_l) = RL.split ps0 prxs_in pctx
       let (pctx1, pctx2) = RL.split prxs1 prxs2 pctx12
       let some_lotr =
             unPTransLOwned "translateSimplImpl" tps_in tps_out ptrans_l

       -- Also split out the input variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (vars_ps, vars12 :>: _) = RL.split ps0 prxs_in pctx_vars
       let (vars1, vars2) = RL.split prxs1 prxs2 vars12

       -- Finally, modify the PTrans_LOwned on top of the stack using
       -- mapLtLOwnedTrans
       withPermStackM
         (\(_ :>: l) -> vars_ps :>: l)
         (\_ ->
           case some_lotr of
             SomeLOwnedTrans lotr ->
               pctx0 :>:
               PTrans_LOwned mb_ls (mbLift tps_in') (mbLift tps_out') ps_in' ps_out'
               (mapLtLOwnedTrans pctx1 vars1 ttr1F pctx2 vars2 ttr2F
                prxs_in' ttr_inF' ttr_outF' t1 t2 lotr))
         m

  [nuMP| SImpl_EndLifetime _ tps_in tps_out ps_in ps_out |] ->
    -- First, translate the in and out permissions of the lowned permission
    do ps_in_trans <- translate ps_in
       ps_out_trans <- tupleTypeTrans <$> translate ps_out
       let prxs_in = mbRAssignProxies ps_in :>: Proxy
       let lrt_out = typeDescLRT $ typeTransTupleDesc ps_out_trans
       let lrt = arrowLRTTrans ps_in_trans lrt_out

       -- Next, split out the ps_in permissions from the rest of the pctx
       pctx <- itiPermStack <$> ask
       let (pctx_ps, pctx_in :>: ptrans_l) = RL.split ps0 prxs_in pctx
       let some_lotr =
             unPTransLOwned "translateSimplImpl" tps_in tps_out ptrans_l

       -- Also split out the ps_in variables and replace them with the ps_out vars
       pctx_vars <- itiPermStackVars <$> ask
       let (ps_vars, _ :>: _) = RL.split ps0 prxs_in pctx_vars
       let vars_out = case mbExprPermsMembers ps_out of
             Just x -> x
             Nothing -> panic "translateSimplImpl"
               ["In SImpl_EndLifetime rule: malformed ps_out"]

       -- Now we apply the lifetime ownerhip function to ps_in and bind its output
       -- in the rest of the computation
       case some_lotr of
         SomeLOwnedTrans lotr ->
           bindSpecMTransM
           (applyCallClosSpecTerm
            lrt (lownedTransTerm ps_in lotr) (transTerms pctx_in))
           ps_out_trans
           "endl_ps"
           (\pctx_out ->
             withPermStackM
             (\(_ :>: l) -> RL.append ps_vars vars_out :>: l)
             (\_ -> RL.append pctx_ps pctx_out :>:
                    PTrans_Conj [APTrans_LFinished])
             m)

  [nuMP| SImpl_IntroLOwnedSimple _ _ _ |] ->
    do let prx_ps_l = mbRAssignProxies $ mbSimplImplIn mb_simpl
       ttrans <- translateSimplImplOut mb_simpl
       withPermStackM id
         (\pctx ->
           let (pctx0, pctx_ps :>: _) = RL.split ps0 prx_ps_l pctx in
           RL.append pctx0 $ typeTransF ttrans (transTerms pctx_ps))
         m

  [nuMP| SImpl_ElimLOwnedSimple mb_l mb_tps mb_ps |] ->
    case (mbExprPermsMembers mb_ps, mbMaybe (mbMap2 lownedPermsSimpleIn mb_l mb_ps)) of
      (Just vars, Just mb_ps') ->
        do ectx <- infoCtx <$> ask
           ttr_inF <- tpTransM $ ctxFunTypeTransM $ translate mb_ps'
           ttr_outF <- tpTransM $ ctxFunTypeTransM $ translate mb_ps
           withPermStackM id
             (\(pctx :>: _) ->
               pctx :>:
               PTrans_LOwned (fmap (const []) mb_l)
               (mbLift mb_tps) (mbLift mb_tps) mb_ps' mb_ps
               (mkLOwnedTransId ectx ttr_inF ttr_outF vars))
             m
      _ ->
        panic "translateSimplImpl"
        ["In SImpl_ElimLOwnedSimple rule: malformed permissions argument"]

  [nuMP| SImpl_LCurrentRefl l |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar l) (:>: typeTransF ttrans []) m

  [nuMP| SImpl_LCurrentTrans _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail (\(pctx :>: _ :>: _) ->
                                (pctx :>: typeTransF ttrans [])) m

  [nuMP| SImpl_DemoteLLVMBlockRW _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockEmpty x _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM (:>: translateVar x)
         (\pctx -> pctx :>: typeTransF ttrans [unitTermLike])
         m

  [nuMP| SImpl_CoerceLLVMBlockEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) -> pctx :>: typeTransF ttrans [unitTermLike])
         m

  [nuMP| SImpl_ElimLLVMBlockToBytes _ mb_bp |] ->
    do let w = natVal2 mb_bp
       let w_term = natTermLike w
       len_term <- translate1 $ fmap llvmBlockLen mb_bp
       ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           let arr_term =
                 applyGlobalTermLike "Prelude.repeatBVVec"
                 [w_term, len_term, unitTypeTermLike, unitTermLike] in
           pctx :>: typeTransF ttrans [arr_term])
         m

  [nuMP| SImpl_IntroLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairTermLike (transTerm1 ptrans)
                                       unitTermLike])
         m

  [nuMP| SImpl_ElimLLVMBlockSeqEmpty _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftTermLike (transTerm1 ptrans)])
         m

  [nuMP| SImpl_SplitLLVMBlockEmpty _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF ttrans [unitTermLike, unitTermLike])
         m

  -- Intro for a recursive named shape applies the fold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_IntroLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ fold_ids |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         fold_id <-
           case fold_ids of
             [nuP| Just (fold_id,_) |] -> return fold_id
             _ -> error "Folding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyGlobalTermLike (mbLift fold_id)
                                         (transTerms args_trans ++
                                          transTerms ptrans_x)])
           m

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: SImpl_IntroLLVMBlockNamed, unknown named shape"
  -- Elim for a recursive named shape applies the unfold function to the
  -- translations of the arguments plus the translations of the proofs of the
  -- permissions
  [nuMP| SImpl_ElimLLVMBlockNamed _ bp nmsh |]
    | [nuMP| RecShapeBody _ _ fold_ids |] <- mbMatch $ fmap namedShapeBody nmsh
    , [nuMP| PExpr_NamedShape _ _ _ args |] <- mbMatch $ fmap llvmBlockShape bp ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         args_trans <- translate args
         unfold_id <-
           case fold_ids of
             [nuP| Just (_,unfold_id) |] -> return unfold_id
             _ -> error "Unfolding recursive shape before it is defined!"
         withPermStackM id
           (\(pctx :>: ptrans_x) ->
             pctx :>: typeTransF ttrans [applyGlobalTermLike (mbLift unfold_id)
                                         (transTerms args_trans ++
                                          transTerms ptrans_x)])
           m

  -- Intro for a defined named shape (the other case) is a no-op
    | [nuMP| DefinedShapeBody _ |] <- mbMatch $ fmap namedShapeBody nmsh ->
      do ttrans <- translateSimplImplOutHead mb_simpl
         withPermStackM id
           (\(pctx :>: ptrans) ->
             pctx :>: typeTransF ttrans [transTerm1 ptrans])
           m

    | otherwise -> fail "translateSimplImpl: ElimLLVMBlockNamed, unknown named shape"

  [nuMP| SImpl_IntroLLVMBlockNamedMods _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockNamedMods _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockFromEq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockPtr _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_ElimLLVMBlockPtr _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_IntroLLVMBlockField _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTupleTerm ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockField _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF (tupleTypeTrans ttrans) [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockArray _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockArray _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockSeq _ _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans1 :>: ptrans2) ->
           let pair_term =
                 pairTermLike (transTerm1 ptrans1) (transTerm1 ptrans2) in
           pctx :>: typeTransF ttrans [pair_term])
         m

  [nuMP| SImpl_ElimLLVMBlockSeq _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans [pairLeftTermLike (transTerm1 ptrans),
                                       pairRightTermLike (transTerm1 ptrans)])
         m

  [nuMP| SImpl_IntroLLVMBlockOr _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockOr _ _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_IntroLLVMBlockEx _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockEx _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_ElimLLVMBlockFalse _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) -> pctx :>: typeTransF ttrans [transTerm1 ptrans])
         m

  [nuMP| SImpl_FoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    do args_trans <- translate args
       ttrans <- translateSimplImplOutHead mb_simpl
       let fold_ident = mbLift $ fmap recPermFoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>: typeTransF ttrans [applyGlobalTermLike fold_ident
                                       (transTerms args_trans
                                        ++ transTerms ptrans_x)])
         m

  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Rec rp) args _ |] ->
    do args_trans <- translate args
       ttrans <- translateSimplImplOutHead mb_simpl
       let unfold_ident = mbLift $ fmap recPermUnfoldFun rp
       withPermStackM id
         (\(pctx :>: ptrans_x) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyGlobalTermLike unfold_ident
                                               (transTerms args_trans
                                                ++ [transTerm1 ptrans_x])])
         m

  [nuMP| SImpl_FoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  [nuMP| SImpl_UnfoldNamed _ (NamedPerm_Defined _) _ _ |] ->
    do ttrans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF ttrans (transTerms ptrans))
         m

  {-
  [nuMP| SImpl_Mu _ _ _ _ |] ->
    error "FIXME HERE: SImpl_Mu: translation not yet implemented"
  -}

  [nuMP| SImpl_NamedToConj _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedFromConj _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgAlways _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgCurrent _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: ptrans :>: _) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgWrite _ _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_NamedArgRead _ _ _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans (transTerms ptrans)) m

  [nuMP| SImpl_ReachabilityTrans _ rp args _ y e |] ->
    do args_trans <- translate args
       e_trans <- translate e
       y_trans <- translate y
       ttrans <- translateSimplImplOutHead mb_simpl
       let trans_ident = mbLift $ fmap recPermTransMethod rp
       withPermStackM RL.tail
         (\(pctx :>: ptrans_x :>: ptrans_y) ->
           pctx :>:
           typeTransF (tupleTypeTrans ttrans) [applyGlobalTermLike trans_ident
                                               (transTerms args_trans
                                                ++ transTerms e_trans
                                                ++ transTerms y_trans
                                                ++ transTerms e_trans
                                                ++ [transTerm1 ptrans_x,
                                                    transTerm1 ptrans_y])])
         m

  [nuMP| SImpl_IntroAnyEqEq _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_IntroAnyWordPtr _ _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM RL.tail
         (\(pctx :>: _ :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_ElimAnyToEq _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tp_trans []) m

  [nuMP| SImpl_ElimAnyToPtr _ _ |] ->
    do tp_trans <- translateSimplImplOutHead mb_simpl
       withPermStackM id
         (\(pctx :>: _) ->
           pctx :>: typeTransF tp_trans []) m


-- | Translate a normal unary 'PermImpl1' rule that succeeds and applies the
-- translation function if the argument succeeds and fails if the translation of
-- the argument fails
translatePermImplUnary ::
  NuMatchingAny1 r => RL.TypeCtx bs =>
  Mb ctx (MbPermImpls r (RNil :> '(bs,ps_out))) ->
  (ImpTransM ext blocks tops rets ps_out (ctx :++: bs) SpecTerm ->
   ImpTransM ext blocks tops rets ps ctx SpecTerm) ->
  PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImplUnary (mbMatch -> [nuMP| MbPermImpls_Cons _ _ mb_impl |]) f =
  let bs = RL.typeCtxProxies in
  PImplTerm <$> fmap f <$> popPImplTerm <$>
  extPermImplTransM bs (translatePermImpl (mbCombine bs mb_impl))

-- | Translate a 'PermImpl1' to a function on translation computations
translatePermImpl1 :: NuMatchingAny1 r =>
                      Mb ctx (PermImpl1 ps ps_outs) ->
                      Mb ctx (MbPermImpls r ps_outs) ->
                      PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImpl1 mb_impl mb_impls = case (mbMatch mb_impl, mbMatch mb_impls) of
  -- A failure translates to a call to the catch handler, which is the most recent
  -- Impl1_Catch, if one exists, or the SAW errorM function otherwise
  ([nuMP| Impl1_Fail err |], _) ->
    pimplFailM (mbLift (fmap ppError err))

  ([nuMP| Impl1_Catch dbg_str |],
   [nuMP| (MbPermImpls_Cons _ (MbPermImpls_Cons _ _ mb_impl1) mb_impl2) |]) ->
    pimplHandleFailM
    (pimplPrependMsgM ("Case 1 of " ++ mbLift dbg_str) $
     translatePermImpl $ mbCombine RL.typeCtxProxies mb_impl1)
    (pimplPrependMsgM ("Case 2 of " ++ mbLift dbg_str) $
     translatePermImpl $ mbCombine RL.typeCtxProxies mb_impl2)

  -- A push moves the given permission from x to the top of the perm stack
  ([nuMP| Impl1_Push x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertVarPermM "Impl1_Push" x p
       ptrans <- getVarPermM x
       setVarPermM x (PTrans_True)
         (withPermStackM (:>: translateVar x) (:>: ptrans) m)

  -- A pop moves the given permission from the top of the perm stack to x
  ([nuMP| Impl1_Pop x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do () <- assertTopPermM "Impl1_Pop 1" x p
       () <- assertVarPermM "Impl1_Pop 2" x (nuMulti (mbToProxy p) $
                                             const ValPerm_True)
       ptrans <- getTopPermM
       setVarPermM x ptrans (withPermStackM RL.tail RL.tail m)

  -- If all branches of an or elimination fail, the whole thing fails; otherwise,
  -- an or elimination performs a multi way Eithers elimination
  ([nuMP| Impl1_ElimOrs dbg_str x mb_or_list |], _) ->
    -- First, translate all the PermImpls in mb_impls, using pitmCatching to
    -- isolate failures to each particular branch, but still reporting failures
    -- in any branch
    zipWithM (\mb_impl' (i::Int) ->
               pimplPrependMsgM ("Case " ++ show i ++
                                 " of " ++ mbLift dbg_str) $
               pimplCatchM $ translatePermImpl mb_impl')
    (mbOrListPermImpls mb_or_list mb_impls) [1..] >>= \maybe_transs ->
    -- As a special case, if all branches fail (representing as translating to
    -- Nothing), then the entire or elimination fails
    if all isNothing maybe_transs then mzero else
      return $ PImplTerm $ \k ->
      do let mb_or_p = mbOrListPerm mb_or_list
         () <- assertTopPermM "Impl1_ElimOrs" x mb_or_p
         tps <- mapM translate $ mbOrListDisjs mb_or_list
         tp_ret <- compReturnTypeTransM
         top_ptrans <- getTopPermM
         eithersElimTransM tps tp_ret
           (flip map maybe_transs $ \maybe_trans ptrans ->
             withPermStackM id ((:>: ptrans) . RL.tail) $
             popPImplTerm (forcePImplTerm maybe_trans) k)
           (transTupleTerm top_ptrans)

  -- An existential elimination performs a pattern-match on a Sigma
  ([nuMP| Impl1_ElimExists x p |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let tp = mbBindingType p
       () <- assertTopPermM "Impl1_ElimExists" x (fmap ValPerm_Exists p)
       top_ptrans <- getTopPermM
       tp_trans <- translateClosed tp
       sigmaElimPermTransM "x_elimEx" tp_trans
         (mbCombine RL.typeCtxProxies p)
         compReturnTypeTransM
         (\etrans ptrans ->
           inExtTransM etrans $
           withPermStackM id ((:>: ptrans) . RL.tail) m)
         (transTerm1 top_ptrans)

  -- A false elimination becomes a call to efq
  ([nuMP| Impl1_ElimFalse mb_x |], _) ->
    return $ PImplTerm $ const $
    do mb_false <- nuMultiTransM $ const ValPerm_False
       () <- assertTopPermM "Impl1_ElimFalse" mb_x mb_false
       top_ptrans <- getTopPermM
       applyGlobalImpTransM "Prelude.efq"
         [compReturnTypeM, return $ transTerm1 top_ptrans]

  -- A SimplImpl is translated using translateSimplImpl
  ([nuMP| Impl1_Simpl simpl mb_prx |], _) ->
    let prx' = mbLift mb_prx in
    translatePermImplUnary mb_impls $ \m ->
    assertPermStackTopEqM "SimplImpl in" prx' (fmap simplImplIn simpl) >>= \() ->
    translateSimplImpl prx' simpl $
    do () <- assertPermStackTopEqM "SimplImpl out" prx' (fmap simplImplOut simpl)
       m

  -- A let binding becomes a let binding
  ([nuMP| Impl1_LetBind _ e |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do etrans <- translate e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: PTrans_Eq (extMb e)) m

  ([nuMP| Impl1_ElimStructField x _ _ memb |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do etrans_x <- translate x
       let etrans_y = case etrans_x of
             ETrans_Struct flds -> RL.get (mbLift memb) flds
             _ -> error "translatePermImpl1: Impl1_ElimStructField"
       let mb_y = mbCombine RL.typeCtxProxies $ fmap (const $ nu $ \y ->
                                                       PExpr_Var y) x
       inExtTransM etrans_y $
         withPermStackM (:>: Member_Base)
         (\case
             (pctx :>: PTrans_Conj [APTrans_Struct pctx_str]) ->
               pctx :>: PTrans_Conj [APTrans_Struct $
                                     RL.set (mbLift memb) (PTrans_Eq mb_y) pctx_str]
               :>: RL.get (mbLift memb) pctx_str
             _ ->
               error "translatePermImpl1: Impl1_ElimStructField")
         m

  ([nuMP| Impl1_ElimLLVMFieldContents _ mb_fld |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base)
    (\(pctx :>: ptrans_x) ->
      let (_,ptrans') =
            unPTransLLVMField "translatePermImpl1: Impl1_ElimLLVMFieldContents"
            knownNat ptrans_x in
      pctx :>: PTrans_Conj [
        APTrans_LLVMField
        (mbCombine RL.typeCtxProxies $
         mbMapCl $(mkClosed [| \fld -> nu $ \y ->
                              llvmFieldSetEqVar fld y |]) mb_fld) $
        PTrans_Eq (mbCombine RL.typeCtxProxies $
                   fmap (const $ nu PExpr_Var) mb_fld)]
      :>: ptrans')
    m

  ([nuMP| Impl1_ElimLLVMBlockToEq _ mb_bp |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_LLVMBlock $
    do let mb_p_out1 =
             mbCombine RL.typeCtxProxies $
             mbMapCl $(mkClosed
                       [| \bp -> nu $ \y ->
                         let len = llvmBlockLen bp in
                         ValPerm_Conj1 $ Perm_LLVMBlock $
                         bp { llvmBlockShape =
                                PExpr_EqShape len $ PExpr_Var y } |])
             mb_bp
       tp_trans1 <- translate mb_p_out1
       let mb_p_out2 =
             mbMapCl $(mkClosed
                       [| ValPerm_Conj1
                        . Perm_LLVMBlockShape . modalizeBlockShape |]) $
             extMb mb_bp
       tp_trans2 <- translate mb_p_out2
       withPermStackM (:>: Member_Base)
         (\(pctx :>: ptrans) ->
           pctx :>: typeTransF tp_trans1 [unitTermLike] :>:
           typeTransF tp_trans2 [transTerm1 ptrans])
         m

  ([nuMP| Impl1_SplitLLVMWordField _ mb_fp mb_sz1 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e = case mbLLVMFieldContents mb_fp of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e) |] -> e
             _ -> error "translatePermImpl1: Impl1_SplitLLVMWordField"
       e_tm <- translate1Pure mb_e
       sz1_tm <- translate mb_sz1
       sz2_tm <- translateClosed $ mbLLVMFieldSize mb_fp
       let sz2m1_tm = applyGlobalOpenTerm "Prelude.subNat" [sz2_tm, sz1_tm]
       let (e1_tm,e2_tm) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term e1_tm) $ inExtTransM (ETrans_Term e2_tm) $
         translate
         (mbCombine RL.typeCtxProxies $ flip mbMapCl mb_fp
          ($(mkClosed
             [| \sz1 endianness fp ->
               impl1SplitLLVMWordFieldOutPerms fp sz1 endianness |])
           `clApply` toClosed (mbLift mb_sz1)
           `clApply` toClosed (mbLift mb_endianness))) >>= \pctx_out ->
         withPermStackM
         (\(vars :>: x) -> vars :>: x :>: x :>:
                           Member_Step Member_Base :>: Member_Base)
         (\(pctx :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_TruncateLLVMWordField _ mb_fp mb_sz1 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e = case mbLLVMFieldContents mb_fp of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e) |] -> e
             _ -> error "translatePermImpl1: Impl1_TruncateLLVMWordField"
       e_tm <- translate1Pure mb_e
       sz1_tm <- translate mb_sz1
       sz2_tm <- translateClosed $ mbLLVMFieldSize mb_fp
       let sz2m1_tm = applyGlobalOpenTerm "Prelude.subNat" [sz2_tm, sz1_tm]
       let (e1_tm,_) =
             bvSplitOpenTerm (mbLift mb_endianness) sz1_tm sz2m1_tm e_tm
       inExtTransM (ETrans_Term e1_tm) $
         translate
         (mbCombine RL.typeCtxProxies $ flip mbMapCl mb_fp
          ($(mkClosed
             [| \sz1 endianness fp ->
               impl1TruncateLLVMWordFieldOutPerms fp sz1 endianness |])
           `clApply` toClosed (mbLift mb_sz1)
           `clApply` toClosed (mbLift mb_endianness))) >>= \pctx_out ->
         withPermStackM (:>: Member_Base)
         (\(pctx :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_ConcatLLVMWordFields _ mb_fp1 mb_e2 mb_endianness |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    do let mb_e1 = case mbLLVMFieldContents mb_fp1 of
             [nuP| ValPerm_Eq (PExpr_LLVMWord e1) |] -> e1
             _ -> error "translatePermImpl1: Impl1_ConcatLLVMWordFields"
       e1_tm <- translate1Pure mb_e1
       e2_tm <- translate1Pure mb_e2
       sz1_tm <- translateClosed $ mbLLVMFieldSize mb_fp1
       sz2_tm <- translateClosed $ mbExprBVTypeWidth mb_e2
       let endianness = mbLift mb_endianness
       let e_tm = bvConcatOpenTerm endianness sz1_tm sz2_tm e1_tm e2_tm
       inExtTransM (ETrans_Term e_tm) $
         translate (mbCombine RL.typeCtxProxies $
                    mbMap2 (\fp1 e2 ->
                             impl1ConcatLLVMWordFieldsOutPerms fp1 e2 endianness)
                    mb_fp1 mb_e2) >>= \pctx_out ->
         withPermStackM
         (\(vars :>: x :>: _) -> (vars :>: x :>: Member_Base))
         (\(pctx :>: _ :>: _) ->
           -- NOTE: all output perms are eq or ptr to eq perms, so contain no
           -- SAW core terms
           pctx `RL.append` typeTransF pctx_out [])
         m

  ([nuMP| Impl1_BeginLifetime |], _) ->
    translatePermImplUnary mb_impls $ \m ->
    inExtTransM ETrans_Lifetime $
    do ectx <- itiExprCtx <$> ask
       let prxs = RL.map (const Proxy) ectx
       let mb_ps = (nuMulti prxs (const MNil))
       let ttr = const $ pure MNil
       withPermStackM (:>: Member_Base)
         (:>:
          PTrans_LOwned
          (nuMulti prxs (const [])) CruCtxNil CruCtxNil mb_ps mb_ps
          (mkLOwnedTransId ectx ttr ttr MNil))
         m

  -- If e1 and e2 are already equal, short-circuit the proof construction and then
  -- elimination
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) _ |], _)
    | mbLift (mbMap2 bvEq e1 e2) ->
      translatePermImplUnary mb_impls $ \m ->
      do bv_tp <- typeTransType1Imp <$> translateClosed (mbExprType e1)
         e1_trans <- translate1 e1
         let pf = ctorTermLike "Prelude.Refl" [bv_tp, e1_trans]
         withPermStackM (:>: translateVar x)
           (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop pf)])
           m

  -- If e1 and e2 are definitely not equal, treat this as a fail
  ([nuMP| Impl1_TryProveBVProp _ (BVProp_Eq e1 e2) prop_str |], _)
    | not $ mbLift (mbMap2 bvCouldEqual e1 e2) ->
      pimplFailM (mbLift prop_str)

  -- Otherwise, insert an equality test with proof construction. Note that, as
  -- with all TryProveBVProps, if the test fails and there is no failure
  -- continuation, we insert just the proposition failure string using
  -- implTransAltErr, not the entire type-checking error message, because this is
  -- considered just an assertion and not a failure
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Eq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalImpTransM "Prelude.maybe"
         [ return (typeTransType1Imp prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "eq_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalImpTransM "Prelude.bvEqWithProof"
           [ return (natTermLike $ natVal2 prop) , translate1 e1, translate1 e2]]

  -- If e1 and e2 are already unequal, short-circuit and do nothing
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Neq e1 e2) _ |], _)
    | not $ mbLift (mbMap2 bvCouldEqual e1 e2) ->
      translatePermImplUnary mb_impls $
        withPermStackM (:>: translateVar x)
          (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitTermLike)])

  -- For an inequality test, we don't need a proof, so just insert an if
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_Neq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    let w = natVal2 prop in
    applyGlobalImpTransM "Prelude.ite"
    [ compReturnTypeM
    , applyGlobalImpTransM "Prelude.bvEq"
      [ return (natTermLike w), translate1 e1, translate1 e2 ]
    , (\ret_tp ->
        implFailAltContTerm ret_tp (mbLift prop_str) k) <$> compReturnTypeM
    , withPermStackM (:>: translateVar x)
      (:>: PTrans_Conj [APTrans_BVProp (BVPropTrans prop unitTermLike)]) $
      popPImplTerm trans k]

  -- If we know e1 < e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyGlobalTermLike "Prelude.unsafeAssertBVULt"
               [natTermLike w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 < e2 statically, translate to bvultWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULt e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalImpTransM "Prelude.maybe"
         [ return (typeTransType1Imp prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ult_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalImpTransM "Prelude.bvultWithProof"
           [ return (natTermLike $ natVal2 prop), translate1 e1, translate1 e2]
         ]

  -- If we know e1 <= e2 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         let pf_tm =
               applyGlobalTermLike "Prelude.unsafeAssertBVULe"
               [natTermLike w, t1, t2]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 <= e2 statically, translate to bvuleWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq e1 e2) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalImpTransM "Prelude.maybe"
         [ return (typeTransType1Imp prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ule_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalImpTransM "Prelude.bvuleWithProof"
           [ return (natTermLike $ natVal2 prop), translate1 e1, translate1 e2]
         ]

  -- If we know e1 <= e2-e3 statically, translate to unsafeAssert
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) _ |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |])
    | mbLift (fmap bvPropHolds prop) ->
      translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
      return $ PImplTerm $ \k ->
      do let w = natVal4 e1
         t1 <- translate1 e1
         t2 <- translate1 e2
         t3 <- translate1 e3
         let pf_tm =
               applyGlobalTermLike "Prelude.unsafeAssertBVULe"
               [natTermLike w, t1,
                applyGlobalTermLike "Prelude.bvSub" [natTermLike w, t2, t3]]
         withPermStackM (:>: translateVar x)
           (:>: bvPropPerm (BVPropTrans prop pf_tm))
           (popPImplTerm trans k)

  -- If we don't know e1 <= e2-e3 statically, translate to bvuleWithProof
  ([nuMP| Impl1_TryProveBVProp x prop@(BVProp_ULeq_Diff e1 e2 e3) prop_str |],
   [nuMP| MbPermImpls_Cons _ _ mb_impl' |]) ->
    translatePermImpl (mbCombine RL.typeCtxProxies mb_impl') >>= \trans ->
    return $ PImplTerm $ \k ->
    do prop_tp_trans <- translate prop
       ret_tp <- compReturnTypeM
       applyGlobalImpTransM "Prelude.maybe"
         [ return (typeTransType1Imp prop_tp_trans), return ret_tp
         , return (implFailAltContTerm ret_tp (mbLift prop_str) k)
         , lambdaTransM "ule_diff_pf" prop_tp_trans
           (\prop_trans ->
             withPermStackM (:>: translateVar x) (:>: bvPropPerm prop_trans) $
             popPImplTerm trans k)
         , applyGlobalImpTransM "Prelude.bvuleWithProof"
           [ return (natTermLike $ natVal2 prop), translate1 e1,
             applyGlobalImpTransM "Prelude.bvSub"
             [return (natTermLike $ natVal2 prop), translate1 e2, translate1 e3]]
         ]

  ([nuMP| Impl1_TryProveBVProp _ _ _ |], _) ->
    pimplFailM ("translatePermImpl1: Unhandled BVProp case")

-- | Translate a 'PermImpl' in the 'PermImplTransM' monad to a function that
-- takes a failure continuation and returns a monadic computation to generate
-- the translation as a term
translatePermImpl :: NuMatchingAny1 r => Mb ctx (PermImpl r ps) ->
                     PImplTransMTerm r ext blocks tops rets ps ctx
translatePermImpl mb_impl = case mbMatch mb_impl of
  [nuMP| PermImpl_Done r |] ->
    do f <- pimplRTransFunM
       return $ PImplTerm $ const $ appImpTransFun f reflCtxExt r
  [nuMP| PermImpl_Step impl1 mb_impls |] ->
    translatePermImpl1 impl1 mb_impls

translatePermImplToTerm :: NuMatchingAny1 r => String ->
                           Mb ctx (PermImpl r ps) ->
                           ImpRTransFun r ext blocks tops rets ctx ->
                           ImpTransM ext blocks tops rets ps ctx SpecTerm
translatePermImplToTerm err mb_impl k =
  let (maybe_ptm, (errs,_)) =
        runPermImplTransM (translatePermImpl mb_impl) k in
  popPImplTerm (forcePImplTerm maybe_ptm) $
  ImplFailContMsg (err ++ "\n\n"
                   ++ concat (intersperse
                              "\n\n--------------------\n\n" errs))

instance ImplTranslateF r ext blocks tops rets =>
         Translate (ImpTransInfo ext blocks tops rets ps)
                   ctx (AnnotPermImpl r ps) SpecTerm where
  translate (mbMatch -> [nuMP| AnnotPermImpl err mb_impl |]) =
    translatePermImplToTerm (mbLift err) mb_impl (ImpRTransFun $
                                                  const translateF)

-- We translate a LocalImplRet to a term that returns all current permissions
instance ImplTranslateF (LocalImplRet ps) ext blocks ps_in rets where
  translateF _ =
    do pctx <- itiPermStack <$> ask
       ret_tp <- returnTypeM
       return $ returnSpecTerm ret_tp (transTupleTerm pctx)

-- | Translate a local implication to its output, adding an error message
translateLocalPermImpl :: String -> Mb ctx (LocalPermImpl ps_in ps_out) ->
                          ImpTransM ext blocks tops rets ps_in ctx SpecTerm
translateLocalPermImpl err (mbMatch -> [nuMP| LocalPermImpl impl |]) =
  clearVarPermsM $ translate $ fmap (AnnotPermImpl err) impl

-- | Translate a local implication over two sequences of permissions (already
-- translated to types) to a monadic function with the first sequence of
-- permissions as free variables and that takes in the second permissions as
-- arguments. This monadic function is relative to the empty function stack.
-- Note that the translations of the second input permissions and the output
-- permissions must have exactly one type, i.e., already be tupled.
translateCurryLocalPermImpl ::
  String -> Mb ctx (LocalPermImpl (ps1 :++: ps2) ps_out) ->
  PermTransCtx ctx ps1 -> RAssign (Member ctx) ps1 ->
  ImpTypeTrans (PermTransCtx ctx ps2) -> RAssign (Member ctx) ps2 ->
  ImpTypeTrans (PermTransCtx ctx ps_out) ->
  ImpTransM ext blocks tops rets ps ctx SpecTerm
translateCurryLocalPermImpl err impl pctx1 vars1 tp_trans2 vars2 tp_trans_out =
  lambdaTransM "x_local" tp_trans2 $ \pctx2 ->
  local (\info -> info { itiReturnType = typeTransTupleDesc tp_trans_out }) $
  withPermStackM
    (const (RL.append vars1 vars2))
    (const (RL.append pctx1 pctx2))
    (translateLocalPermImpl err impl)

-- | Translate a 'LocalPermImpl' to an 'LOwnedTransTerm'
translateLOwnedPermImpl :: String -> Mb ctx (LocalPermImpl ps_in ps_out) ->
                           ImpTransM ext blocks tops rets ps ctx
                           (LOwnedTransTerm ctx ps_in ps_out)
translateLOwnedPermImpl err (mbMatch -> [nuMP| LocalPermImpl mb_impl |]) =
  ask >>= \info_top ->
  return $ LOwnedTransM $ \e_ext loinfo_in k ->
  flip runTransM (lownedInfoToImp loinfo_in info_top) $
  translatePermImplToTerm err (extMbExt e_ext mb_impl) $
  ImpRTransFun $ \cext' r ->
  case mbMatch r of
    [nuMP| LocalImplRet Refl |] ->
      do info_out <- ask
         let e_ext' = ctxExtToExprExt cext' $ itiExprCtx info_out
         return $ k e_ext' (impInfoToLOwned info_out) ()


----------------------------------------------------------------------
-- * Translating Typed Crucible Expressions
----------------------------------------------------------------------

-- translate for a TypedReg yields an ExprTrans
instance TransInfo info =>
         Translate info ctx (TypedReg tp) (ExprTrans tp) where
  translate (mbMatch -> [nuMP| TypedReg x |]) = translate x

instance TransInfo info =>
         Translate info ctx (TypedRegs tps) (ExprTransCtx tps) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedRegsNil |] -> return MNil
    [nuMP| TypedRegsCons rs r |] ->
      (:>:) <$> translate rs <*> translate r

instance TransInfo info =>
         Translate info ctx (RegWithVal tp) (ExprTrans tp) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| RegWithVal _ e |] -> translate e
    [nuMP| RegNoVal x |] -> translate x

-- | Translate a 'RegWithVal' to exactly one SAW term via 'transPureTerm1'
translateRWV :: TransInfo info => Mb ctx (RegWithVal a) ->
                TransM info ctx OpenTerm
translateRWV mb_rwv = transPureTerm1 <$> translate mb_rwv

-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext exprExt, TransInfo info) =>
         Translate info ctx (App ext RegWithVal tp) (ExprTrans tp) where
  translate mb_e = case mbMatch mb_e of
    [nuMP| BaseIsEq BaseBoolRepr e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.boolEq")
      [translateRWV e1, translateRWV e2]
  --  [nuMP| BaseIsEq BaseNatRepr e1 e2 |] ->
  --    ETrans_Term <$>
  --    applyMultiPureTransM (return $ globalOpenTerm "Prelude.equalNat")
  --    [translateRWV e1, translateRWV e2]
    [nuMP| BaseIsEq (BaseBVRepr w) e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvEq")
      [translate w, translateRWV e1, translateRWV e2]

    [nuMP| EmptyApp |] -> return ETrans_Unit

    -- Booleans
    [nuMP| BoolLit True |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.True"
    [nuMP| BoolLit False |] ->
      return $ ETrans_Term $ globalOpenTerm "Prelude.False"
    [nuMP| Not e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.not")
      [translateRWV e]
    [nuMP| And e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.and")
      [translateRWV e1, translateRWV e2]
    [nuMP| Or e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.or")
      [translateRWV e1, translateRWV e2]
    [nuMP| BoolXor e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.xor")
      [translateRWV e1, translateRWV e2]

    -- Natural numbers
    [nuMP| Expr.NatLit n |] ->
      return $ ETrans_Term $ natOpenTerm $ mbLift n
    [nuMP| NatLt e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.ltNat")
      [translateRWV e1, translateRWV e2]
    -- [nuMP| NatLe _ _ |] ->
    [nuMP| NatEq e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.equalNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatAdd e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.addNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatSub e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.subNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMul e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.mulNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatDiv e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.divNat")
      [translateRWV e1, translateRWV e2]
    [nuMP| NatMod e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.modNat")
      [translateRWV e1, translateRWV e2]

    -- Function handles: the expression part of a function handle has no
    -- computational content
    [nuMP| HandleLit _ |] -> return ETrans_Fun

    -- Bitvectors
    [nuMP| BVUndef w |] ->
      -- FIXME: we should really handle poison values; this translation just
      -- treats them as if there were the bitvector 0 value
      return $ ETrans_Term $ bvBVOpenTerm (mbLift w) $ BV.zero (mbLift w)
    [nuMP| BVLit w mb_bv |] ->
      return $ ETrans_Term $ bvBVOpenTerm (mbLift w) $ mbLift mb_bv
    [nuMP| BVConcat w1 w2 e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.join")
      [translate w1, translate w2, translateRWV e1, translateRWV e2]
    [nuMP| BVTrunc w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvTrunc")
      [return (natOpenTerm (natValue (mbLift w2) - natValue (mbLift w1))),
       translate w1,
       translateRWV e]
    [nuMP| BVZext w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvUExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       translate w2, translateRWV e]
    [nuMP| BVSext w1 w2 e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSExt")
      [return (natOpenTerm (natValue (mbLift w1) - natValue (mbLift w2))),
       -- NOTE: bvSExt adds 1 to the 2nd arg
       return (natOpenTerm (natValue (mbLift w2) - 1)),
       translateRWV e]
    [nuMP| BVNot w e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvNot")
      [translate w, translateRWV e]
    [nuMP| BVAnd w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvAnd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVOr w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvOr")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVXor w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvXor")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVNeg w e |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvNeg")
      [translate w, translateRWV e]
    [nuMP| BVAdd w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvAdd")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSub w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSub")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVMul w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvMul")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUdiv w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvUDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSdiv w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSDiv")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUrem w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvURem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSrem w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSRem")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUle w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvule")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVUlt w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvult")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSle w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvsle")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSlt w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvslt")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVCarry w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvCarry")
      [translate w, translateRWV e1, translateRWV e2]
    [nuMP| BVSCarry w e1 e2 |] ->
      -- NOTE: bvSCarry adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSCarry")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVSBorrow w e1 e2 |] ->
      -- NOTE: bvSBorrow adds 1 to the bitvector length
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSBorrow")
      [return w_minus_1, translateRWV e1, translateRWV e2]
    [nuMP| BVShl w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvShiftL")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVLshr w e1 e2 |] ->
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvShiftR")
      [translate w, return (globalOpenTerm "Prelude.Bool"), translate w,
       return (globalOpenTerm "Prelude.False"), translateRWV e1, translateRWV e2]
    [nuMP| BVAshr w e1 e2 |] ->
      let w_minus_1 = natOpenTerm (natValue (mbLift w) - 1) in
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvSShiftR")
      [return w_minus_1, return (globalOpenTerm "Prelude.Bool"), translate w,
       translateRWV e1, translateRWV e2]
    [nuMP| BoolToBV mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term <$>
      applyMultiPureTransM (return $ globalOpenTerm "Prelude.ite")
      [bitvectorTransM (translate mb_w),
       translateRWV e,
       return (bvBVOpenTerm w (BV.one w)),
       return (bvBVOpenTerm w (BV.zero w))]
    [nuMP| BVNonzero mb_w e |] ->
      let w = mbLift mb_w in
      ETrans_Term <$>
      applyPureTransM (return $ globalOpenTerm "Prelude.not")
      (applyMultiPureTransM (return $ globalOpenTerm "Prelude.bvEq")
       [translate mb_w, translateRWV e,
        return (bvBVOpenTerm w (BV.zero w))])

    -- Strings
    [nuMP| Expr.StringLit (UnicodeLiteral text) |] ->
      return $ ETrans_Term $ stringLitOpenTerm $
      mbLift text

    -- Everything else is an error
    _ ->
      error ("Unhandled expression form: " ++
              (renderString (layoutSmart opts (mbLift $ fmap (ppApp (const $ pretty ("_" :: String))) mb_e))))
        where opts = PP.LayoutOptions (PP.AvailablePerLine 80 0.8)


-- translate for a TypedExpr yields an ExprTrans
instance (PermCheckExtC ext exprExt, TransInfo info) =>
         Translate info ctx (TypedExpr ext tp) (ExprTrans tp) where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedExpr _ (Just e) |] -> translate e
    [nuMP| TypedExpr app Nothing |] -> translate app

-- | Get the output permission on the return value of a 'TypedExpr'
exprOutPerm :: PermCheckExtC ext exprExt => Mb ctx (TypedExpr ext tp) ->
               PermTrans ctx tp
exprOutPerm mb_x = case mbMatch mb_x of
  [nuMP| TypedExpr _ (Just e) |] -> PTrans_Eq e
  [nuMP| TypedExpr _ Nothing |] -> PTrans_True


----------------------------------------------------------------------
-- * Translating Typed Crucible Jump Targets
----------------------------------------------------------------------

{-
debugPrettyPermCtx :: RAssign Proxy ctx -> PermTransCtx ctx ps -> [Doc]
debugPrettyPermCtx _ MNil = []
debugPrettyPermCtx prxs (ptranss :>: ptrans) =
  debugPrettyPermCtx prxs ptranss ++
  [permPretty emptyPPInfo (permTransPerm prxs ptrans) <+>
   string ("(" ++ show (length $ transTerms ptrans) ++ " terms)")]
-}

{-
-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments, given as 'DistPerms', which should match the current
-- stack. The 'String' argument is the name of the construct being applied, for
-- use in error reporting.
translateApply :: String -> OpenTerm -> Mb ctx (DistPerms ps) ->
                  ImpTransM ext blocks tops rets ps ctx OpenTerm
translateApply nm f perms =
  do assertPermStackEqM nm perms
     expr_ctx <- itiExprCtx <$> ask
     arg_membs <- itiPermStackVars <$> ask
     let e_args = RL.map (flip RL.get expr_ctx) arg_membs
     i_args <- itiPermStack <$> ask
     return $
       {-
       trace ("translateApply for " ++ nm ++ " with perm arguments:\n" ++
              -- renderDoc (list $ debugPrettyPermCtx (mbToProxy perms) i_args)
              -- permPrettyString emptyPPInfo (permTransCtxPerms (mbToProxy perms) i_args)
              permPrettyString emptyPPInfo perms
             ) $ -}
       applyOpenTermMulti f (exprCtxToTerms e_args ++ permCtxToTerms i_args)
-}

-- | Translate a call to (the translation of) an entrypoint, by either calling
-- the letrec-bound variable for the entrypoint, if it has one, or by just
-- translating the body of the entrypoint if it does not.
translateCallEntry :: forall ext exprExt tops args ghosts blocks ctx rets.
                      PermCheckExtC ext exprExt => String ->
                      TypedEntryTrans ext blocks tops rets args ghosts ->
                      Mb ctx (RAssign ExprVar (tops :++: args)) ->
                      Mb ctx (RAssign ExprVar ghosts) ->
                      ImpTransM ext blocks tops rets
                      ((tops :++: args) :++: ghosts) ctx SpecTerm
translateCallEntry nm entry_trans mb_tops_args mb_ghosts =
  -- First test that the stack == the required perms for entryID
  do let entry = typedEntryTransEntry entry_trans
     ectx <- translate $ mbMap2 RL.append mb_tops_args mb_ghosts
     stack <- itiPermStack <$> ask
     let mb_s =
           mbMap2 (\tops_args ghosts ->
                    permVarSubstOfNames $ RL.append tops_args ghosts)
           mb_tops_args mb_ghosts
     let mb_perms = fmap (\s -> varSubst s $ mbValuePermsToDistPerms $
                                typedEntryPermsIn entry) mb_s
     () <- assertPermStackEqM nm mb_perms

     -- Now check if entryID has an associated recursive closure
     case typedEntryTransClos entry_trans of
       Just (lrt, clos_tm) ->
         -- If so, build the associated CallS term, which applies the closure to
         -- the expressions with permissions on the stack followed by the proofs
         -- objects for those permissions
         do expr_ctx <- itiExprCtx <$> ask
            arg_membs <- itiPermStackVars <$> ask
            let e_args = RL.map (flip RL.get expr_ctx) arg_membs
            i_args <- itiPermStack <$> ask
            return (applyCallClosSpecTerm lrt clos_tm
                    (exprCtxToTerms e_args ++ permCtxToTerms i_args))
       Nothing ->
         -- Otherwise, continue translating with the target entrypoint, with all
         -- the current expressions free but with only those permissions on top
         -- of the stack
         inEmptyEnvImpTransM $ inCtxTransM ectx $
         do perms_trans <- translate $ typedEntryPermsIn entry
            withPermStackM
              (const $ RL.members ectx)
              (const $ typeTransF perms_trans $ transTerms stack)
              (translate $ _mbBinding $ typedEntryBody entry)

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (CallSiteImplRet blocks tops args ghosts ps) SpecTerm where
  translate (mbMatch ->
             [nuMP| CallSiteImplRet entryID ghosts Refl mb_tavars mb_gvars |]) =
    do entry_trans <-
         lookupEntryTransCast (mbLift entryID) (mbLift ghosts) <$>
         itiBlockMapTrans <$> ask
       translateCallEntry "CallSiteImplRet" entry_trans mb_tavars mb_gvars

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (CallSiteImplRet blocks tops args ghosts)
         ext blocks tops rets where
  translateF mb_tgt = translate mb_tgt


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedJumpTarget blocks tops ps) SpecTerm where
  translate (mbMatch -> [nuMP| TypedJumpTarget siteID _ _ mb_perms_in |]) =
    do SomeTypedCallSite site <-
         lookupCallSite (mbLift siteID) <$> itiBlockMapTrans <$> ask
       let CallSiteImpl mb_impl = typedCallSiteImpl site
       translate $ flip fmap mb_perms_in $ \perms_in ->
         varSubst (permVarSubstOfNames $ distPermsVars perms_in) mb_impl

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedJumpTarget blocks tops) ext blocks tops rets where
  translateF mb_tgt = translate mb_tgt


----------------------------------------------------------------------
-- * Translating Typed Crucible Statements
----------------------------------------------------------------------

-- | Translate a 'TypedStmt' to a function on translation computations
translateStmt ::
  PermCheckExtC ext exprExt => ProgramLoc ->
  Mb ctx (TypedStmt ext stmt_rets ps_in ps_out) ->
  ImpTransM ext blocks tops rets ps_out (ctx :++: stmt_rets) SpecTerm ->
  ImpTransM ext blocks tops rets ps_in ctx SpecTerm
translateStmt loc mb_stmt m = case mbMatch mb_stmt of
  [nuMP| TypedSetReg tp e |] ->
    do tp_trans <- translate tp
       tp_ret <- compReturnTypeM
       etrans <- tpTransM $ translate e
       let ptrans = exprOutPerm e
       inExtTransSAWLetBindM tp_trans tp_ret etrans $
         withPermStackM (:>: Member_Base) (:>: extPermTrans etrans ptrans) m

  [nuMP| TypedSetRegPermExpr _ e |] ->
    do etrans <- tpTransM $ translate e
       inExtTransM etrans $
         withPermStackM (:>: Member_Base) (:>: PTrans_Eq (extMb e)) m

  -- FIXME HERE: document this!
  [nuMP| TypedCall _freg fun_perm _ gexprs args |] ->
    do f_trans <- getTopPermM
       ectx_outer <- itiExprCtx <$> ask
       let rets = mbLift $ mbMapCl $(mkClosed [| funPermRets |]) fun_perm
       let rets_prxs = cruCtxProxies rets
       rets_trans <- translateClosed rets
       let perms_out =
             mbCombine rets_prxs $ flip mbMapCl mb_stmt
             ($(mkClosed [| \prxs stmt -> nuMulti prxs (typedStmtOut stmt) |])
              `clApply` toClosed rets_prxs)
       ectx_gexprs <- translate gexprs
       ectx_args <- translate args
       pctx_in <- RL.tail <$> itiPermStack <$> ask
       let (pctx_ghosts_args, _) =
             RL.split (RL.append ectx_gexprs ectx_args) ectx_gexprs pctx_in
       fret_tp <-
         mkTermImpTypeTrans <$>
         sigmaTypeTransM "ret" rets_trans (hasPureTrans perms_out)
         (\ectx -> inExtMultiTransM ectx (typeTransTupleDesc <$>
                                          translate perms_out))
       let all_args =
             exprCtxToTerms ectx_gexprs ++ exprCtxToTerms ectx_args ++
             permCtxToTerms pctx_ghosts_args
       let fapp_trm = case f_trans of
             PTrans_Fun _ f_trm -> applyFunTransTerm f_trm all_args
             _ ->
               panic "translateStmt"
               ["TypedCall: unexpected function permission"]
       bindSpecMTransM
         fapp_trm fret_tp "call_ret_val" $ \ret_val ->
         sigmaElimTransM "elim_call_ret_val" rets_trans
           (flip inExtMultiTransM (translate perms_out)) compReturnTypeTransM
           (\rets_ectx pctx ->
             inExtMultiTransM rets_ectx $
             withPermStackM
             (\(vars :>: _) ->
               RL.append
               (fst (RL.split
                     (RL.append ectx_gexprs ectx_args) ectx_gexprs vars)) $
               suffixMembers ectx_outer rets_prxs)
             (const pctx)
             m)
           ret_val

  -- FIXME HERE: figure out why these asserts always translate to ite True
  [nuMP| TypedAssert e _ |] ->
    applyGlobalImpTransM "Prelude.ite"
    [compReturnTypeM, translate1 e, m,
     mkErrorComp ("Failed Assert at " ++
                  renderDoc (ppShortFileName (plSourceLoc loc)))]

  [nuMP| TypedLLVMStmt stmt |] -> translateLLVMStmt stmt m


-- | Translate a 'TypedStmt' to a function on translation computations
translateLLVMStmt ::
  Mb ctx (TypedLLVMStmt r ps_in ps_out) ->
  ImpTransM ext blocks tops rets ps_out (ctx :> r) SpecTerm ->
  ImpTransM ext blocks tops rets ps_in ctx SpecTerm
translateLLVMStmt mb_stmt m = case mbMatch mb_stmt of
  [nuMP| ConstructLLVMWord (TypedReg x) |] ->
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $
                                           fmap (PExpr_LLVMWord . PExpr_Var) x)) m

  [nuMP| AssertLLVMWord reg _ |] ->
    inExtTransM (ETrans_Term $ natOpenTerm 0) $
    withPermStackM ((:>: Member_Base) . RL.tail)
    ((:>: (PTrans_Eq $ fmap (const $ PExpr_Nat 0) $ extMb reg)) . RL.tail)
    m

  [nuMP| AssertLLVMPtr _ |] ->
    inExtTransM ETrans_Unit $
    withPermStackM RL.tail RL.tail m

  [nuMP| DestructLLVMWord _ e |] ->
    translate e >>= \etrans ->
    inExtTransM etrans $
    withPermStackM ((:>: Member_Base) . RL.tail)
    ((:>: (PTrans_Eq $ extMb e)) . RL.tail)
    m

  [nuMP| OffsetLLVMValue _ _ |] ->
    let mb_x_off =
          mbMapCl $(mkClosed [| \(OffsetLLVMValue x off) ->
                               PExpr_LLVMOffset (typedRegVar x) off |])
          mb_stmt in
    inExtTransM ETrans_LLVM $
    withPermStackM (:>: Member_Base) (:>: (PTrans_Eq $ extMb $ mb_x_off))
    m

  [nuMP| TypedLLVMLoad _ (mb_fp :: LLVMFieldPerm w sz)
                       (_ :: DistPerms ps) cur_perms |] ->
    let prx_l = mbLifetimeCurrentPermsProxies cur_perms
        prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
    inExtTransM ETrans_LLVM $
    withPermStackM
    (\(RL.split prx_ps prx_l -> (vars, vars_l)) ->
      RL.append (vars :>: Member_Base) vars_l)
    (\(RL.split prx_ps prx_l -> (pctx :>: p_ptr, pctx_l)) ->
      let (_, p_ret) =
            unPTransLLVMField "translateLLVMStmt: TypedLLVMLoad: expected field perm"
            (knownNat @sz) p_ptr in
      withKnownNat ?ptrWidth $
      RL.append
      (pctx :>: PTrans_Conj [APTrans_LLVMField
                             (mbCombine RL.typeCtxProxies $
                              mbMapCl $(mkClosed
                                        [| \fp -> nu $ \ret ->
                                          llvmFieldSetEqVar fp ret |]) mb_fp)
                             (PTrans_Eq $ mbCombine RL.typeCtxProxies $
                              fmap (const $ nu $ \ret -> PExpr_Var ret) mb_fp)]
       :>: p_ret) pctx_l)
    m

  [nuMP| TypedLLVMStore _ (mb_fp :: LLVMFieldPerm w sz) mb_e
                        (_ :: DistPerms ps) cur_perms |] ->
    let prx_l = mbLifetimeCurrentPermsProxies cur_perms
        prx_ps :: Proxy (ps :> LLVMPointerType w) = Proxy in
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_Unit $
    withPermStackM id
    (\(RL.split prx_ps prx_l -> (pctx :>: _p_ptr, pctx_l)) ->
      RL.append
      (pctx :>: PTrans_Conj [APTrans_LLVMField
                             (extMb $ mbMap2 (\fp e ->
                                               fp { llvmFieldContents =
                                                      ValPerm_Eq e })
                              mb_fp mb_e)
                             (PTrans_Eq $ extMb mb_e)])
      pctx_l)
    m

  [nuMP| TypedLLVMAlloca _ (mb_fperm :: LLVMFramePerm w) mb_sz |] ->
    let sz = mbLift mb_sz
        w :: Proxy w = Proxy in
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVM $
    translateClosed (llvmEmptyBlockPermOfSize w sz) >>= \ptrans_tp ->
    withPermStackM (:>: Member_Base)
    (\(pctx :>: _) ->
      pctx
      :>: PTrans_Conj [APTrans_LLVMFrame $
                       flip nuMultiWithElim1 (extMb mb_fperm) $
                       \(_ :>: ret) fperm -> (PExpr_Var ret, sz):fperm]
      -- the unitTermLike argument is because ptrans_tp is a memblock permission
      -- with an empty shape; the empty shape expects a unit argument
      :>: typeTransF ptrans_tp [unitTermLike])
    m

  [nuMP| TypedLLVMCreateFrame |] ->
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVMFrame $
    withPermStackM (:>: Member_Base)
    (:>: PTrans_Conj [APTrans_LLVMFrame $ fmap (const []) (extMb mb_stmt)])
    m

  [nuMP| TypedLLVMDeleteFrame _ _ _ |] ->
    inExtTransM ETrans_Unit $
    withPermStackM (const MNil) (const MNil) m

  [nuMP| TypedLLVMLoadHandle _ tp _ |] ->
    inExtTransM ETrans_Fun $
    withPermStackM ((:>: Member_Base) . RL.tail)
    (\case
        (pctx :>: PTrans_Conj [APTrans_LLVMFunPtr tp' ptrans])
          | Just Refl <- testEquality (mbLift tp) tp' ->
            pctx :>: ptrans
        _ -> error ("translateLLVMStmt: TypedLLVMLoadHandle: "
                    ++ "unexpected permission stack"))
    m

  [nuMP| TypedLLVMResolveGlobal gsym (p :: ValuePerm (LLVMPointerType w))|] ->
    withKnownNat ?ptrWidth $
    inExtTransM ETrans_LLVM $
    do env <- infoEnv <$> ask
       let w :: NatRepr w = knownRepr
       case lookupGlobalSymbol env (mbLift gsym) w of
         Nothing -> error ("translateLLVMStmt: TypedLLVMResolveGlobal: "
                           ++ " no translation of symbol "
                           ++ globalSymbolName (mbLift gsym))
         Just (_, GlobalTransDef spec_def)
           | [nuP| ValPerm_LLVMFunPtr fun_tp (ValPerm_Fun fun_perm) |] <- p ->
             do lrt <- typeDescLRT <$> translate (extMb fun_perm)
                let ptrans =
                      PTrans_Conj [APTrans_LLVMFunPtr (mbLift fun_tp) $
                                   PTrans_Fun fun_perm $ FunTransFun lrt $
                                   importDefSpecTerm spec_def]
                withPermStackM (:>: Member_Base)
                  (:>: extPermTrans ETrans_LLVM ptrans) m
         Just (_, GlobalTransDef _) ->
           panic "translateLLVMStmt"
           ["TypedLLVMResolveGlobal: "
            ++ " unexpected recursive function translation for symbol "
            ++ globalSymbolName (mbLift gsym)]
         Just (_, GlobalTransClos clos)
           | [nuP| ValPerm_LLVMFunPtr fun_tp (ValPerm_Fun fun_perm) |] <- p ->
             do lrt <- typeDescLRT <$> translate (extMb fun_perm)
                let ptrans =
                      PTrans_Conj [APTrans_LLVMFunPtr (mbLift fun_tp) $
                                   PTrans_Fun fun_perm $ FunTransClos lrt clos]
                withPermStackM (:>: Member_Base)
                  (:>: extPermTrans ETrans_LLVM ptrans) m
         Just (_, GlobalTransClos _) ->
           panic "translateLLVMStmt"
           ["TypedLLVMResolveGlobal: "
            ++ " unexpected recursive function translation for symbol "
            ++ globalSymbolName (mbLift gsym)]
         Just (_, GlobalTransTerms ts) ->
           do ptrans <- translate (extMb p)
              let ts_imp = map openTermLike ts
              withPermStackM (:>: Member_Base) (:>: typeTransF ptrans ts_imp) m

  [nuMP| TypedLLVMIte _ mb_r1 _ _ |] ->
    inExtTransM ETrans_LLVM $
    do b <- translate1 $ extMb mb_r1
       tptrans <-
         translate $ mbCombine RL.typeCtxProxies $
         mbMapCl $(mkClosed
                   [| \stmt -> nu $ \ret ->
                     distPermsHeadPerm $ typedLLVMStmtOut stmt ret |])
         mb_stmt
       let t = applyGlobalTermLike "Prelude.boolToEither" [b]
       withPermStackM (:>: Member_Base) (:>: typeTransF tptrans [t]) m


----------------------------------------------------------------------
-- * Translating Sequences of Typed Crucible Statements
----------------------------------------------------------------------

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedRet tops rets ps) SpecTerm where
  translate (mbMatch -> [nuMP| TypedRet Refl mb_rets mb_rets_ns mb_perms |]) =
    do let perms =
             mbMap2
             (\rets_ns ps -> varSubst (permVarSubstOfNames rets_ns) ps)
             mb_rets_ns mb_perms
       () <- assertPermStackEqM "TypedRet" perms
       rets_trans <- translate mb_rets
       let rets_prxs = cruCtxProxies $ mbLift mb_rets
       rets_ns_trans <- translate mb_rets_ns
       ret_tp <- returnTypeM
       sigma_trm <-
         sigmaTransM "r" rets_trans
         (flip inExtMultiTransM $
          translate $ mbCombine rets_prxs mb_perms)
         rets_ns_trans (itiPermStack <$> ask)
       return $ returnSpecTerm ret_tp sigma_trm

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedRet tops rets) ext blocks tops rets where
  translateF mb_ret = translate mb_ret

instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedTermStmt blocks tops rets ps) SpecTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedJump impl_tgt |] -> translate impl_tgt
    [nuMP| TypedBr reg impl_tgt1 impl_tgt2 |] ->
      applyGlobalImpTransM "Prelude.ite"
      [compReturnTypeM, translate1 reg,
       translate impl_tgt1, translate impl_tgt2]
    [nuMP| TypedReturn impl_ret |] -> translate impl_ret
    [nuMP| TypedErrorStmt (Just str) _ |] ->
      mkErrorComp ("Error: " ++ mbLift str)
    [nuMP| TypedErrorStmt Nothing _ |] ->
      mkErrorComp "Error (unknown message)"


instance PermCheckExtC ext exprExt =>
         Translate (ImpTransInfo ext blocks tops rets ps) ctx
         (TypedStmtSeq ext blocks tops rets ps) SpecTerm where
  translate mb_x = case mbMatch mb_x of
    [nuMP| TypedImplStmt impl_seq |] -> translate impl_seq
    [nuMP| TypedConsStmt loc stmt pxys mb_seq |] ->
      translateStmt (mbLift loc) stmt (translate $ mbCombine (mbLift pxys) (_mbBinding <$> mb_seq))
    [nuMP| TypedTermStmt _ term_stmt |] -> translate term_stmt

instance PermCheckExtC ext exprExt =>
         ImplTranslateF (TypedStmtSeq
                         ext blocks tops rets) ext blocks tops rets where
  translateF mb_seq = translate mb_seq


----------------------------------------------------------------------
-- * Translating CFGs
----------------------------------------------------------------------

-- | An entrypoint over some regular and ghost arguments
data SomeTypedEntry ext blocks tops rets =
  forall ghosts args.
  SomeTypedEntry (TypedEntry TransPhase ext blocks tops rets args ghosts)

-- | Get all entrypoints in a block map that will be translated to closures,
-- which is all entrypoints with in-degree > 1
typedBlockClosEntries :: TypedBlockMap TransPhase ext blocks tops rets ->
                           [SomeTypedEntry ext blocks tops rets]
typedBlockClosEntries =
  concat . RL.mapToList (map (\(Some entry) ->
                               SomeTypedEntry entry)
                         . filter (anyF typedEntryHasMultiInDegree)
                         . (^. typedBlockEntries))

-- | Fold a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
foldBlockMapClos ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b -> b) ->
  b -> TypedBlockMap TransPhase ext blocks tops rets -> b
foldBlockMapClos f r =
  foldr (\(SomeTypedEntry entry) -> f entry) r . typedBlockClosEntries

-- | Map a function over each 'TypedEntry' in a 'TypedBlockMap' that
-- corresponds to a letrec-bound variable
mapBlockMapClos ::
  (forall args ghosts.
   TypedEntry TransPhase ext blocks tops rets args ghosts -> b) ->
  TypedBlockMap TransPhase ext blocks tops rets -> [b]
mapBlockMapClos f =
  map (\(SomeTypedEntry entry) -> f entry) . typedBlockClosEntries

-- | Build a @LetRecType@ that describes the type of the translation of a
-- 'TypedEntry' to a closure
translateEntryLRT :: TypedEntry TransPhase ext blocks tops rets args ghosts ->
                     TypeTransM ctx OpenTerm
translateEntryLRT entry@(TypedEntry {..}) =
  inEmptyCtxTransM $
  translateClosed (typedEntryAllArgs entry) >>= \arg_tps ->
  piLRTTransM "arg" arg_tps $ \ectx ->
  inCtxTransM ectx $
  translate typedEntryPermsIn >>= \perms_in_tps ->
  arrowLRTTransM perms_in_tps $
  translateEntryRetType entry >>= \retType ->
  return $ ctorOpenTerm "Prelude.LRT_Ret" [typeDescLRT retType]

-- | Build a list of @LetRecType@ values that describe the types of all of the
-- entrypoints in a 'TypedBlockMap' that will be translated to closures
translateBlockMapLRTs :: TypedBlockMap TransPhase ext blocks tops rets ->
                         TypeTransM ctx [OpenTerm]
translateBlockMapLRTs blkMap =
  sequence $ mapBlockMapClos translateEntryLRT blkMap

-- | Translate the function permission of a CFG to a @LetRecType@
translateCFGLRT :: TypedCFG ext blocks ghosts inits gouts ret ->
                   TypeTransM ctx OpenTerm
translateCFGLRT cfg =
  typeDescLRT <$> translateClosed (tpcfgFunPerm cfg)

-- | Translate a 'TypedEntry' to a 'TypedEntryTrans' by associating a closure
-- term with it if it has one, i.e., if its in-degree is greater than 1. If it
-- does need a closure, the 'Natural' state tracks the index to be used for the
-- next closure, so use the current value and increment it.
--
-- Note that the return type is a monad inside a monad. This is so that the
-- caller can see the 'Natural' state without running the 'TypeTransM'
-- computation, which is necessary later on for tying the knot
translateTypedEntry ::
  Some (TypedEntry TransPhase ext blocks tops rets args) ->
  State Natural (TypeTransM RNil (Some
                                  (TypedEntryTrans ext blocks tops rets args)))
translateTypedEntry (Some entry) =
  if typedEntryHasMultiInDegree entry then
    do i <- get
       put (i+1)
       return $ do lrt <- translateEntryLRT entry
                   return (Some (TypedEntryTrans entry $
                                 Just (lrt, mkBaseClosSpecTerm i)))
  else return $ return $ Some (TypedEntryTrans entry Nothing)

-- | Translate a 'TypedBlock' to a 'TypedBlockTrans' by translating each
-- entrypoint in the block using 'translateTypedEntry'; see
-- 'translateTypedEntry' for an explanation of the monad-in-monad type
translateTypedBlock ::
  TypedBlock TransPhase ext blocks tops rets args ->
  State Natural (TypeTransM RNil (TypedBlockTrans ext blocks tops rets args))
translateTypedBlock blk =
  (TypedBlockTrans <$>) <$> sequence <$>
  mapM translateTypedEntry (blk ^. typedBlockEntries)

-- | Helper function to translate a 'TypedBlockMap' to a 'TypedBlockMapTrans' by
-- translating every entrypoint using 'translateTypedEntry'; see
-- 'translateTypedEntry' for an explanation of the monad-in-monad type
translateTypedBlockMapH ::
  RAssign (TypedBlock TransPhase ext blocks tops rets) blks ->
  State Natural (TypeTransM RNil
                 (RAssign (TypedBlockTrans ext blocks tops rets) blks))
translateTypedBlockMapH MNil = return $ return MNil
translateTypedBlockMapH (blkMap :>: blk) =
  do blkMapTransM <- translateTypedBlockMapH blkMap
     blkTransM <- translateTypedBlock blk
     return ((:>:) <$> blkMapTransM <*> blkTransM)

-- | Translate a 'TypedBlockMap' to a 'TypedBlockMapTrans' by translating every
-- entrypoint using 'translateTypedEntry'; see 'translateTypedEntry' for an
-- explanation of the monad-in-monad type
translateTypedBlockMap ::
  TypedBlockMap TransPhase ext blocks tops rets ->
  State Natural (TypeTransM RNil (TypedBlockMapTrans ext blocks tops rets))
translateTypedBlockMap = translateTypedBlockMapH

-- | Translate the typed statements of an entrypoint to a function
--
-- > \top1 ... topn arg1 ... argm ghost1 ... ghostk p1 ... pj -> stmts_trans
--
-- over the top-level, local, and ghost arguments and (the translations of) the
-- input permissions of the entrypoint
translateEntryBody :: PermCheckExtC ext exprExt =>
                      TypedBlockMapTrans ext blocks tops rets ->
                      TypedEntry TransPhase ext blocks tops rets args ghosts ->
                      TypeTransM RNil SpecTerm
translateEntryBody mapTrans entry =
  lambdaExprCtx (typedEntryAllArgs entry) $
  lambdaPermCtx (typedEntryPermsIn entry) $ \pctx ->
  do retType <- translateEntryRetType entry
     impTransM (RL.members pctx) pctx mapTrans retType $
       translate $ _mbBinding $ typedEntryBody entry

-- | Translate all the entrypoints in a 'TypedBlockMap' that translate to
-- closures into the @LetRecType@s and bodies of those closures
translateBlockMapBodies :: PermCheckExtC ext exprExt =>
                           TypedBlockMapTrans ext blocks tops rets ->
                           TypedBlockMap TransPhase ext blocks tops rets ->
                           TypeTransM RNil [(OpenTerm, SpecTerm)]
translateBlockMapBodies mapTrans blkMap =
  sequence $ mapBlockMapClos (\entry ->
                               (,) <$> translateEntryLRT entry <*>
                               translateEntryBody mapTrans entry) blkMap

-- | Translate a CFG to a monadic function that takes all the top-level
-- arguments to that CFG and calls into its initial entrypoint; this monadic
-- function is used as the body of one of the closures used to translate the CFG
translateCFGInitBody ::
  PermCheckExtC ext exprExt =>
  TypedBlockMapTrans ext blocks (ghosts :++: inits) (gouts :> ret) ->
  TypedCFG ext blocks ghosts inits gouts ret ->
  TypeTransM RNil SpecTerm
translateCFGInitBody mapTrans cfg =
  let fun_perm = tpcfgFunPerm cfg
      h = tpcfgHandle cfg
      ctx = typedFnHandleAllArgs h
      inits = typedFnHandleArgs h
      ghosts = typedFnHandleGhosts h
      retTypes = typedFnHandleRetTypes h in
  lambdaExprCtx ctx $
  translateRetType retTypes (tpcfgOutputPerms cfg) >>= \retTypeTrans ->

  -- Extend the expr context to contain another copy of the initial arguments
  -- inits, since the initial entrypoint for the entire function takes two
  -- copies of inits, one to represent the top-level arguments and one to
  -- represent the local arguments to the entrypoint, which just happen to be
  -- the same as those top-level arguments and so get eq perms to relate them
  inExtMultiTransCopyLastM ghosts (cruCtxProxies inits) $

  lambdaPermCtx (funPermToBlockInputs fun_perm) $ \pctx ->
  let all_membs = RL.members pctx
      all_px = RL.map (\_ -> Proxy) pctx
      init_entry = lookupEntryTransCast (tpcfgEntryID cfg) CruCtxNil mapTrans in
  impTransM all_membs pctx mapTrans retTypeTrans $
  translateCallEntry "CFG" init_entry (nuMulti all_px id) (nuMulti all_px $
                                                           const MNil)

-- | Translate a CFG to a monadic function that passes all of its arguments to
-- the closure with the given index, which is meant to be the closure whose body
-- is defined by 'translateCFGInitBody'
translateCFGIxCall :: TypedCFG ext blocks ghosts inits gouts ret -> Natural ->
                      TypeTransM RNil SpecTerm
translateCFGIxCall cfg ix =
  do let fun_perm = tpcfgFunPerm cfg
         h = tpcfgHandle cfg
         ctx = typedFnHandleAllArgs h
     lrt <- translateCFGLRT cfg
     lambdaExprCtx ctx $ lambdaPermCtx (funPermIns fun_perm) $ \pctx ->
       (infoCtx <$> ask) >>= \ectx ->
       return $
       applyCallClosSpecTerm lrt (mkBaseClosSpecTerm ix) (transTerms ectx ++
                                                          transTerms pctx)

-- | The components of the spec definition that a CFG translates to. Note that,
-- if the CFG is for a function that is mutually recursive with other functions,
-- then it also needs the closures of those functions in its spec definition.
data CFGTrans =
  CFGTrans { cfgTransLRT :: OpenTerm,
             cfgTransCloss :: [(OpenTerm,SpecTerm)],
             cfgTransBody :: SpecTerm }

-- | Translate a CFG to a list of closure definitions, represented as a pair of
-- a @LetRecType@ and a monadic function of that @LetRecType@. These closures
-- are for the CFG itself and for all of its entrypoints that are translated to
-- closures, i.e., with in-degree > 1. Use the current 'Natural' in the 'State'
-- monad as the starting index for these closures, and increment that 'Natural'
-- state for each closure body returned. Also return the 'Natural' index used
-- for the closure for the entire CFG. See 'translateTypedEntry' for an
-- explanation of the monad-in-monad type.
translateCFG :: PermCheckExtC ext exprExt =>
                TypedCFG ext blocks ghosts inits gouts ret ->
                State Natural (Natural, TypeTransM RNil CFGTrans)
translateCFG cfg =
  do let blkMap = tpcfgBlockMap cfg
     -- Get the natural number index for the top-level closure of the CFG
     cfg_ix <- get
     put (cfg_ix + 1)
     -- Translate the block map of the CFG by generating calls to closures for
     -- all the entrypoints with in-degree > 1
     mapTransM <- translateTypedBlockMap blkMap
     -- Return the CFG index and the computation for creating the bodies
     return
       (cfg_ix,
        do mapTrans <- mapTransM
           -- Generate the actual closure bodies + LRTs for those entrypoints
           closs <- translateBlockMapBodies mapTrans blkMap
           -- Generate the closure body + LRT for the entire CFG
           cfg_clos_body <- translateCFGInitBody mapTrans cfg
           cfg_lrt <- translateCFGLRT cfg
           let cfg_clos = (cfg_lrt,cfg_clos_body)
           -- Generate the body of the CFG, that calls the cfg_body closure
           cfg_body <- translateCFGIxCall cfg cfg_ix
           -- Then, finally, return all the closure lrts and bodies
           return $ CFGTrans cfg_lrt (cfg_clos : closs) cfg_body)


----------------------------------------------------------------------
-- * Translating Sets of CFGs
----------------------------------------------------------------------

-- | An existentially quantified tuple of a 'TypedCFG', its 'GlobalSymbol', and
-- a 'String' name we want to translate it to
data SomeTypedCFG ext where
  SomeTypedCFG :: PermCheckExtC ext exprExt => GlobalSymbol -> String ->
                  TypedCFG ext blocks ghosts inits gouts ret ->
                  SomeTypedCFG ext

-- | Helper function to build an LLVM function permission from a 'FunPerm'
mkPtrFunPerm :: HasPtrWidth w => FunPerm ghosts args gouts ret ->
                ValuePerm (LLVMPointerType w)
mkPtrFunPerm fun_perm =
  withKnownNat ?ptrWidth $ ValPerm_Conj1 $ mkPermLLVMFunPtr ?ptrWidth fun_perm

-- | Extract the 'FunPerm' of a 'SomeTypedCFG' as a permission on LLVM function
-- pointer values
someTypedCFGPtrPerm :: HasPtrWidth w => SomeTypedCFG LLVM ->
                       ValuePerm (LLVMPointerType w)
someTypedCFGPtrPerm (SomeTypedCFG _ _ cfg) = mkPtrFunPerm $ tpcfgFunPerm cfg

-- | Convert a 'SomedTypedCFG' and a closure index for its initial entrypoint
-- closure into an entry in the permission environment
someTypedCFGIxEntry :: HasPtrWidth w => SomeTypedCFG LLVM -> Natural ->
                       PermEnvGlobalEntry
someTypedCFGIxEntry (SomeTypedCFG sym _ cfg) ix =
  withKnownNat ?ptrWidth $
  PermEnvGlobalEntry sym (mkPtrFunPerm $ tpcfgFunPerm cfg)
  (GlobalTransClos $ mkBaseClosSpecTerm ix)

-- | Translate a list of CFGs for mutually recursive functions to a list of
-- @LetRecType@s and spec definitions of those @LetRecType@s
translateCFGsToDefs :: HasPtrWidth w => PermEnv -> ChecksFlag ->
                       [SomeTypedCFG LLVM] -> [(OpenTerm,OpenTerm)]
translateCFGsToDefs env checks some_cfgs =
  let (cfg_ixs, cfg_transsM) =
        unzip $ evalState (mapM (\(SomeTypedCFG _ _ cfg) ->
                                  translateCFG cfg) some_cfgs) 0
      tmp_env = permEnvAddGlobalSyms env $
        zipWith someTypedCFGIxEntry some_cfgs cfg_ixs
      cfg_transs = runNilTypeTransM tmp_env checks $ sequence cfg_transsM
      closs = concat $ map cfgTransCloss cfg_transs in
  map (\cfg_trans ->
        let lrt = cfgTransLRT cfg_trans in
        (lrt,
         defineSpecOpenTerm (identOpenTerm $ permEnvSpecMEventType env) closs
         lrt (cfgTransBody cfg_trans)))
  cfg_transs


-- | An existentially quantified tuple of a 'CFG', its function permission, and
-- a 'String' name we want to translate it to
data SomeCFGAndPerm ext where
  SomeCFGAndPerm :: GlobalSymbol -> String -> CFG ext blocks inits ret ->
                    FunPerm ghosts (CtxToRList inits) gouts ret ->
                    SomeCFGAndPerm ext

-- | Extract the 'GlobalSymbol' from a 'SomeCFGAndPerm'
someCFGAndPermSym :: SomeCFGAndPerm ext -> GlobalSymbol
someCFGAndPermSym (SomeCFGAndPerm sym _ _ _) = sym

-- | Extract the 'String' name from a 'SomeCFGAndPerm'
someCFGAndPermToName :: SomeCFGAndPerm ext -> String
someCFGAndPermToName (SomeCFGAndPerm _ nm _ _) = nm

-- | Map a 'SomeCFGAndPerm' to a 'PermEnvGlobalEntry' with no translation, i.e.,
-- with an 'error' term for the translation
someCFGAndPermGlobalEntry :: HasPtrWidth w => SomeCFGAndPerm ext ->
                             PermEnvGlobalEntry
someCFGAndPermGlobalEntry (SomeCFGAndPerm sym _ _ fun_perm) =
  withKnownNat ?ptrWidth $
  PermEnvGlobalEntry sym (mkPtrFunPerm fun_perm) $
  panic "someCFGAndPermGlobalEntry"
  ["Attempt to translate CFG during its own type-checking"]

-- | Convert the 'FunPerm' of a 'SomeCFGAndPerm' to an inductive @LetRecType@
-- description of the SAW core type it translates to
someCFGAndPermLRT :: PermEnv -> SomeCFGAndPerm ext -> OpenTerm
someCFGAndPermLRT env (SomeCFGAndPerm _ _ _ fun_perm) =
  typeDescLRT $ runNilTypeTransM env noChecks $ translateClosed fun_perm

-- | Construct a spec definition type for the event type in the supplied
-- environment with the supplied @LetRecType@
permEnvSpecDefOpenTerm :: PermEnv -> OpenTerm -> OpenTerm
permEnvSpecDefOpenTerm env lrt =
  applyGlobalOpenTerm "Prelude.SpecDef"
  [identOpenTerm (permEnvSpecMEventType env), lrt]

-- | Type-check a list of functions in the Heapster type system, translate each
-- to a spec definition bound to the SAW core 'String' name associated with it,
-- add these translations as function permissions in the current environment,
-- and return the list of type-checked CFGs
tcTranslateAddCFGs ::
  HasPtrWidth w => SharedContext -> ModuleName -> PermEnv -> ChecksFlag ->
  EndianForm -> DebugLevel -> [SomeCFGAndPerm LLVM] ->
  IO (PermEnv, [SomeTypedCFG LLVM])
tcTranslateAddCFGs sc mod_name env checks endianness dlevel cfgs_and_perms =
  withKnownNat ?ptrWidth $
  do
    -- First, we type-check all the CFGs, mapping them to SomeTypedCFGs; this
    -- uses a temporary PermEnv where all the function symbols being
    -- type-checked are assigned their permissions, but no translation yet
    let tmp_env1 =
          permEnvAddGlobalSyms env $
          map someCFGAndPermGlobalEntry cfgs_and_perms
    let tc_cfgs =
          flip map cfgs_and_perms $ \(SomeCFGAndPerm gsym nm cfg fun_perm) ->
          SomeTypedCFG gsym nm $
          debugTraceTraceLvl dlevel ("Type-checking " ++ show gsym) $
          debugTrace verboseDebugLevel dlevel
          ("With type:\n" ++ permPrettyString emptyPPInfo fun_perm) $
          tcCFG ?ptrWidth tmp_env1 endianness dlevel fun_perm cfg

    -- Next, translate all those CFGs to spec definitions
    let lrts_defs = translateCFGsToDefs env checks tc_cfgs

    -- Insert each spec definition as a SAW core definition bound to its
    -- corresponding ident in the SAW core module mod_name, and generate entries
    -- for the environment mapping each function name to its SAW core ident
    new_entries <-
      zipWithM
      (\(SomeTypedCFG sym nm cfg) (lrt, def_tm) ->
        do tp <- completeNormOpenTerm sc $ permEnvSpecDefOpenTerm env lrt
           tm <- completeNormOpenTerm sc def_tm
           let ident = mkSafeIdent mod_name nm
           scInsertDef sc mod_name ident tp tm
           let perm = mkPtrFunPerm $ tpcfgFunPerm cfg
           return $ PermEnvGlobalEntry sym perm (GlobalTransDef $
                                                 globalOpenTerm ident))
      tc_cfgs lrts_defs

    -- Add the new entries to the environment and return the new environment and
    -- the type-checked CFGs
    return (permEnvAddGlobalSyms env new_entries, tc_cfgs)


----------------------------------------------------------------------
-- * Top-level Entrypoints for Translating Other Things
----------------------------------------------------------------------

-- | Translate a function permission to the type of a spec definition for the
-- translation of a function with that permission
translateCompleteFunPerm :: SharedContext -> PermEnv ->
                            FunPerm ghosts args gouts ret -> IO Term
translateCompleteFunPerm sc env fun_perm =
  completeNormOpenTerm sc $ permEnvSpecDefOpenTerm env $ typeDescLRT $
  runNilTypeTransM env noChecks (translateClosed fun_perm)

-- | Translate a 'TypeRepr' to the SAW core type it represents
translateCompleteType :: SharedContext -> PermEnv -> TypeRepr tp -> IO Term
translateCompleteType sc env typ_perm =
  completeNormOpenTerm sc $ typeTransType1 $
  runNilTypeTransM env noChecks $ translateType True typ_perm

-- | Translate a 'TypeRepr' within the given context of type arguments to the
-- SAW core type it represents
translateCompleteTypeInCtx :: SharedContext -> PermEnv ->
                              CruCtx args -> Mb args (TypeRepr a) -> IO Term
translateCompleteTypeInCtx sc env args ret =
  completeNormOpenTerm sc $ runNilTypeTransM env noChecks $
  piExprCtxPure args (typeTransType1 <$> translateType True (mbLift ret))

-- | Translate an input list of 'ValuePerms' and an output 'ValuePerm' to a pure
-- SAW core function type, not in the @SpecM@ monad. It is an error if any of
-- the permissions are impure, such as @lowned@ permissions.
translateCompletePureFun :: SharedContext -> PermEnv
                         -> CruCtx ctx -- ^ Type arguments
                         -> Mb ctx (ValuePerms args) -- ^ Input perms
                         -> Mb ctx (ValuePerm ret) -- ^ Return type perm
                         -> IO Term
translateCompletePureFun sc env ctx ps_in p_out =
  completeNormOpenTerm sc $ runNilTypeTransM env noChecks $ piExprCtxPure ctx $
  do ps_in_trans <- translate ps_in
     p_out_trans <- translate p_out
     let justOrPanic (Just x) = x
         justOrPanic Nothing =
           panic "translateCompletePureFun"
           ["Attempt to translate an impure permission to a pure type"]
     let (tps_in, tp_out) =
           justOrPanic
           ((,) <$>
            mapM typeDescPureType (typeTransDescs ps_in_trans) <*>
            typeDescPureType (tupleOfTypeDescs $ typeTransDescs p_out_trans))
     return $ piOpenTermMulti (map ("_",) tps_in) (const tp_out)
