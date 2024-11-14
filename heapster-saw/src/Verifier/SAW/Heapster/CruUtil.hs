{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Verifier.SAW.Heapster.CruUtil where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Reflection
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Constant
import Data.ByteString
import Numeric
import Numeric.Natural
import qualified Data.BitVector.Sized as BV
import System.FilePath
import GHC.TypeNats (KnownNat, natVal)
import Data.Functor.Product
import Control.Lens hiding ((:>), Index, Empty, ix, op)
import qualified Control.Monad.Fail as Fail
import Data.Binding.Hobbits
import qualified Data.Type.RList as RL

import What4.ProgramLoc
import What4.Partial
import What4.Interface (StringLiteral(..))
import What4.Utils.Word16String (Word16String)

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import Data.Parameterized.BoolRepr
import Data.Parameterized.Nonce (Nonce)

-- import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L
import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core hiding (App)
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Errors
import Lang.Crucible.LLVM.Errors.MemoryError
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import Verifier.SAW.Term.Functor
import Verifier.SAW.OpenTerm


-- | The lens into an 'RAssign' associated with a 'Member' proof
--
-- FIXME HERE: this should go into Hobbits, possibly using
member :: Member ctx a -> Lens' (RAssign f ctx) (f a)
member memb = lens (RL.get memb) (flip (RL.set memb))

-- | Traverse an 'RAssign' inside an 'Applicative'
--
-- FIXME HERE: move to Hobbits, renaming it just plain 'traverse'
traverseRAssign :: Applicative m => (forall x. f x -> m (g x)) ->
                   RAssign f c -> m (RAssign g c)
traverseRAssign _ MNil = pure MNil
traverseRAssign f (xs :>: x) = (:>:) <$> traverseRAssign f xs <*> f x

-- FIXME HERE: this should move to Hobbits
instance Closable a => Closable (Maybe a) where
  toClosed Nothing = $(mkClosed [| Nothing |])
  toClosed (Just a) = $(mkClosed [| Just |]) `clApply` toClosed a

-- FIXME HERE: this should move to Hobbits
instance (Closable a, Closable b) => Closable (a,b) where
  toClosed (a,b) =
    $(mkClosed [| (,) |]) `clApply` toClosed a `clApply` toClosed b


----------------------------------------------------------------------
-- * Helper Functions for 'NatRepr' and 'KnownNat'
----------------------------------------------------------------------

-- | A version of 'natVal' that takes a phantom argument with 2 applied type
-- functors instead of 1
natVal2 :: KnownNat w => f (g w) -> Natural
natVal2 (_ :: f (g w)) = natVal (Proxy :: Proxy w)

-- | A version of 'natVal' that takes a phantom argument with 3 applied type
-- functors instead of 1
natVal3 :: KnownNat w => f (g (h w)) -> Natural
natVal3 (_ :: f (g (h w))) = natVal (Proxy :: Proxy w)

-- | A version of 'natVal' that takes a phantom argument with 4 applied type
-- functors instead of 1
natVal4 :: KnownNat w => f (g (h (i w))) -> Natural
natVal4 (_ :: f (g (h (i w)))) = natVal (Proxy :: Proxy w)

-- | A version of 'knownNat' that take a phantom argument
natRepr :: KnownNat w => f w -> NatRepr w
natRepr _ = knownNat

-- | A version of 'natRepr' that take a phantom argument with 2 applied type
-- functors instead of 1
natRepr2 :: KnownNat w => f (g w) -> NatRepr w
natRepr2 _ = knownNat

-- | A version of 'natRepr' that take a phantom argument with 3 applied type
-- functors instead of 1
natRepr3 :: KnownNat w => f (g (h w)) -> NatRepr w
natRepr3 _ = knownNat

-- | A version of 'natRepr' that take a phantom argument with 4 applied type
-- functors instead of 1
natRepr4 :: KnownNat w => f (g (h (i w))) -> NatRepr w
natRepr4 _ = knownNat

-- | A 'NatRepr' for @1@
oneRepr :: NatRepr 1
oneRepr = knownRepr

-- | Convert an 'Integral' type to 'NatRepr' that is at least 1, if possible
someNatGeq1 :: Integral a => a -> Maybe (Some (Product NatRepr (LeqProof 1)))
someNatGeq1 i
  | Just (Some w) <- someNat i
  , Left leq <- decideLeq oneRepr w = Just (Some (Pair w leq))
someNatGeq1 _ = Nothing

data SomeKnownNatGeq1 where
  SomeKnownNatGeq1 :: (KnownNat n, 1 <= n) => NatRepr n -> SomeKnownNatGeq1

someKnownNatGeq1 :: Integral a => a -> Maybe SomeKnownNatGeq1
someKnownNatGeq1 i
  | Just (Some (Pair w LeqProof)) <- someNatGeq1 i
  = Just $ withKnownNat w (SomeKnownNatGeq1 w)
someKnownNatGeq1 _ = Nothing


----------------------------------------------------------------------
-- * Building 'NuMatching' and 'Closable' Instances for Crucible Types
----------------------------------------------------------------------

-- | A reification of an object of type @a@ at type level
data ReifiesObj a = forall s. Reifies s a => ReifiesObj (Proxy s)

$(mkNuMatching [t| forall a. ReifiesObj a |])

-- | Build a 'ReifiesObj' containing a value
mkReifiesObj :: a -> ReifiesObj a
mkReifiesObj a = reify a ReifiesObj

-- | Project out the value contained in a 'ReifiesObj'
projReifiesObj :: ReifiesObj a -> a
projReifiesObj (ReifiesObj prx) = reflect prx

instance NuMatching Ident where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable Ident where
  toClosed = unsafeClose

instance Liftable Ident where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching OpenTerm where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching GlobalSymbol where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable GlobalSymbol where
  toClosed = unsafeClose

instance Liftable GlobalSymbol where
  mbLift = unClosed . mbLift . fmap toClosed

-- | This is copied from 'Lang.Crucible.LLVM.Types', as that module is hidden
globalSymbolName :: GlobalSymbol -> String
globalSymbolName (GlobalSymbol (L.Symbol str)) = str

instance NuMatching (SymbolRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (BoolRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (BoolRepr tp) where
  toClosed = unsafeClose

instance Liftable (BoolRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching (NatRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (NatRepr tp) where
  toClosed = unsafeClose

instance Liftable (NatRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching (TypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (TypeRepr tp) where
  toClosed = unsafeClose

instance Liftable (TypeRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

  -- FIXME: we will need this instance when we define CruCtx via RAssign
{-
instance ClosableAny1 TypeRepr where
  closableAny1 _ = IsClosable
-}

instance NuMatching (BaseTypeRepr tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (BaseTypeRepr tp) where
  toClosed = unsafeClose

instance Liftable (BaseTypeRepr tp) where
  mbLift = unClosed . mbLift . fmap toClosed

-- NOTE: this is handled by the Assignment instance
-- instance NuMatching (CtxRepr ctx) where
--   nuMatchingProof = isoMbTypeRepr mkKnownReprObj getKnownReprObj

instance NuMatching (Index ctx a) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (Index ctx a) where
  toClosed = unsafeClose

instance Liftable (Index ctx a) where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching Text where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable Text where
  toClosed = unsafeClose

instance Liftable Text where
  mbLift = unClosed . mbLift . fmap toClosed

instance NuMatching ProgramLoc where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable ProgramLoc where
  toClosed = unsafeClose

instance Liftable ProgramLoc where
  mbLift = unClosed . mbLift . fmap toClosed

-- | Pretty-print a 'Position' with a \"short\" filename, without the path
ppShortFileName :: Position -> PP.Doc ann
ppShortFileName (SourcePos path l c) =
  PP.pretty (takeFileName $ Text.unpack path)
    PP.<> PP.colon PP.<> PP.pretty l
    PP.<> PP.colon PP.<> PP.pretty c
ppShortFileName (BinaryPos path addr) =
  PP.pretty (takeFileName $ Text.unpack path) PP.<> PP.colon PP.<>
    PP.pretty "0x" PP.<> PP.pretty (showHex addr "")
ppShortFileName (OtherPos txt) = PP.pretty (Text.unpack txt)
ppShortFileName InternalPos = PP.pretty "internal"

instance NuMatching ByteString where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (MemoryError sym) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching MemoryErrorReason where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FnHandle args ret) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching SomeHandle where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching (FloatInfoRepr fi) where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching RoundingMode where
  nuMatchingProof = unsafeMbTypeRepr

instance NuMatching EndianForm where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable EndianForm where
  toClosed BigEndian = $(mkClosed [| BigEndian |])
  toClosed LittleEndian = $(mkClosed [| LittleEndian |])

instance Liftable EndianForm where
  mbLift = unClosed . mbLift . fmap toClosed

$(mkNuMatching [t| forall f. NuMatchingAny1 f => Some f |])
$(mkNuMatching [t| forall f ctx . NuMatchingAny1 f => AssignView f ctx |])

viewToAssign :: AssignView f ctx -> Assignment f ctx
viewToAssign AssignEmpty = Ctx.empty
viewToAssign (AssignExtend asgn' f) = extend asgn' f

instance NuMatchingAny1 f => NuMatching (Assignment f ctx) where
  nuMatchingProof =
    -- FIXME: inefficient to map a whole Assignment step by step to ViewAssigns,
    -- freshen each element, and then map back to the Assignment again; maybe we
    -- need to figure out how to use the TraversableFC instance for Assignment
    -- here?
    isoMbTypeRepr viewAssign viewToAssign

instance Closable (Assignment TypeRepr ctx) where
  toClosed = unsafeClose

instance Liftable (Assignment TypeRepr ctx) where
  mbLift = unClosed . mbLift . fmap toClosed


$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => BaseTerm f tp |])
$(mkNuMatching [t| forall a. NuMatching a => NonEmpty a |])
$(mkNuMatching [t| forall p v. (NuMatching p, NuMatching v) => Partial p v |])
$(mkNuMatching [t| X86_80Val |])
-- $(mkNuMatching [t| MemoryLoadError |]) -- NOTE: contains unexported types
$(mkNuMatching [t| forall w. BV.BV w |])
$(mkNuMatching [t| Word16String |])
$(mkNuMatching [t| forall s. StringLiteral s |])
$(mkNuMatching [t| forall s. StringInfoRepr s |])

#if __GLASGOW_HASKELL__ >= 902
$(mkNuMatching [t| forall ext f tp.
                (NuMatchingAny1 f, NuMatchingAny1 (ExprExtension ext f)) =>
                App ext f tp |])
#else
-- See Note [QuantifiedConstraints + TypeFamilies trick]
$(mkNuMatching [t| forall ext f tp exprExt.
                ( NuMatchingAny1 f
                , exprExt ~ ExprExtension ext f, NuMatchingAny1 exprExt
                ) => App ext f tp |])
#endif

$(mkNuMatching [t| Bytes |])
$(mkNuMatching [t| forall v. NuMatching v => Field v |])
$(mkNuMatching [t| Alignment |])
$(mkNuMatching [t| UB.PtrComparisonOperator |])
$(mkNuMatching [t| forall v. NuMatching v => StorageTypeF v |])
$(mkNuMatching [t| StorageType |])

$(mkNuMatching [t| forall f. NuMatchingAny1 f => Poison.Poison f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => UB.UndefinedBehavior f |])
-- $(mkNuMatching [t| forall f. NuMatchingAny1 f => BadBehavior f |])
-- $(mkNuMatching [t| forall f. NuMatchingAny1 f => LLVMSafetyAssertion f |])
$(mkNuMatching [t| forall f. NuMatchingAny1 f => LLVMSideCondition f |])

$(mkNuMatching [t| forall blocks tp. BlockID blocks tp |])

-- FIXME: Hobbits mkNuMatching cannot handle empty types
-- $(mkNuMatching [t| forall f tp. EmptyExprExtension f tp |])

instance NuMatching (EmptyExprExtension f tp) where
  nuMatchingProof = unsafeMbTypeRepr

$(mkNuMatching [t| AVXOp1 |])
$(mkNuMatching [t| forall f tp. NuMatchingAny1 f => ExtX86 f tp |])

instance NuMatching (Nonce s tp) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (Nonce s tp) where
  toClosed = unsafeClose

instance Liftable (Nonce s tp) where
  mbLift = unClosed . mbLift . fmap toClosed

$(mkNuMatching [t| forall tp. GlobalVar tp |])
$(mkNuMatching [t| forall f tp. NuMatchingAny1 f =>
                LLVMExtensionExpr f tp |])

{-
$(mkNuMatching [t| forall w f tp. NuMatchingAny1 f => LLVMStmt w f tp |])
-}

instance Closable (BV.BV w) where
  toClosed = unsafeClose

instance Liftable (BV.BV w) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable Bytes where
  toClosed (Bytes i) =
    $(mkClosed [| Bytes |]) `clApply` (toClosed i)

instance Liftable Bytes where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (StringLiteral si) where
  toClosed = unsafeClose

instance Liftable (StringLiteral si) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (BadBehavior e) where
  toClosed = unsafeClose

-- instance NuMatchingAny1 e => Liftable (BadBehavior e) where
  -- mbLift = unClosed . mbLift . fmap toClosed

-- NOTE: Crucible objects can never contain any Hobbits names, but \"proving\"
-- that would require introspection of opaque types like 'Index' and 'Nonce',
-- and would also be inefficient, so we just use 'unsafeClose'

instance Closable (Block ext cblocks ret args) where
  toClosed = unsafeClose

instance Closable (FnHandle args ret) where
  toClosed = unsafeClose

instance Liftable (FnHandle args ret) where
  mbLift fh = unClosed $ mbLift $ fmap toClosed fh

instance Closable SomeHandle where
  toClosed = unsafeClose

instance Liftable SomeHandle where
  mbLift fh = unClosed $ mbLift $ fmap toClosed fh

-- | Close an assignment whose elements are all 'Closable'
closeAssign :: (forall a. f a -> Closed (f a)) -> Assignment f ctx ->
               Closed (Assignment f ctx)
closeAssign _ (viewAssign -> AssignEmpty) = $(mkClosed [| Ctx.empty |])
closeAssign f (viewAssign -> AssignExtend asgn fa) =
  $(mkClosed [| Ctx.extend |]) `clApply` closeAssign f asgn `clApply` f fa


----------------------------------------------------------------------
-- * Objects Associated with Crucible Types
----------------------------------------------------------------------

-- FIXME HERE: replace all calls to show tp with our own type-printing function
-- that prints in the same format that we are parsing

-- | An element of some representation type functor @f a@ along with a
-- 'TypeRepr' for @a@
data Typed f a = Typed { typedType :: TypeRepr a, typedObj :: f a }

$(mkNuMatching [t| forall f a. NuMatching (f a) => Typed f a |])

-- | Cast an existential 'Typed' to a particular type or raise an error
castTypedM :: Fail.MonadFail m => String -> TypeRepr a -> Some (Typed f) -> m (f a)
castTypedM _ tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = return f
castTypedM str tp (Some (Typed tp' _)) =
  fail ("Expected " ++ str ++ " of type " ++ show tp
        ++ ", found one of type " ++ show tp')

-- | A expression variable of some existentially quantified type
type TypedName = Some (Typed Name)


----------------------------------------------------------------------
-- * Contexts of Crucible Types
----------------------------------------------------------------------

-- | Convert a Crucible 'Ctx' to a Hobbits 'RList'
type family CtxToRList (ctx :: Ctx k) :: RList k where
  CtxToRList EmptyCtx = RNil
  CtxToRList (ctx' ::> x) = CtxToRList ctx' :> x

-- | Convert a Hobbits 'RList' to a Crucible 'Ctx'
type family RListToCtx (ctx :: RList k) :: Ctx k where
  RListToCtx RNil = EmptyCtx
  RListToCtx (ctx' :> x) = RListToCtx ctx' ::> x

-- | Convert a Crucible context of contexts to a Hobbits one
type family CtxCtxToRList (ctx :: Ctx (Ctx k)) :: RList (RList k) where
  CtxCtxToRList EmptyCtx = RNil
  CtxCtxToRList (ctx' ::> c) = CtxCtxToRList ctx' :> CtxToRList c

-- | Convert a Hobbits context of contexts to a Crucible one
type family RListToCtxCtx (ctx :: RList (RList k)) :: Ctx (Ctx k) where
  RListToCtxCtx RNil = EmptyCtx
  RListToCtxCtx (ctx' :> c) = RListToCtxCtx ctx' ::> RListToCtx c

-- | Convert a Crucible 'Assignment' to a Hobbits 'RAssign'
assignToRList :: Assignment f ctx -> RAssign f (CtxToRList ctx)
assignToRList asgn = case viewAssign asgn of
  AssignEmpty -> MNil
  AssignExtend asgn' f -> assignToRList asgn' :>: f

-- | Invert 'assignToRList', converting a Hobbits 'RAssign' over a Hobbits
-- context generated by 'CtxToRList' back to a Crucible 'Assignment'
unAssignToRList :: Assignment prx ctx -> RAssign f (CtxToRList ctx) ->
                   Assignment f ctx
unAssignToRList ctx fs =
  let sz = Ctx.size ctx in
  Ctx.generate sz $ \ix -> RL.get (indexToMember sz ix) fs

-- | Append two Hobbits 'RAssign's that have been generated by 'assignToRList'
assignToRListAppend :: Assignment prx1 ctx1 -> Assignment prx2 ctx2 ->
                       RAssign f (CtxToRList ctx1) ->
                       RAssign f (CtxToRList ctx2) ->
                       RAssign f (CtxToRList (ctx1 <+> ctx2))
assignToRListAppend ctx1 ctx2 fs1 fs2 =
  assignToRList (unAssignToRList ctx1 fs1 Ctx.<++> unAssignToRList ctx2 fs2)

-- | Convert a Crucible 'Assignment' over a context of contexts to an 'RAssign'
-- over a right-list of right-lists
assignToRListRList :: (forall c. f c -> g (CtxToRList c)) ->
                      Assignment f ctx -> RAssign g (CtxCtxToRList ctx)
assignToRListRList f asgn = case viewAssign asgn of
  AssignEmpty -> MNil
  AssignExtend asgn' x -> assignToRListRList f asgn' :>: f x

-- | Convert a Hobbits 'RAssign' to a Crucible 'Assignment'
rlistToAssign :: RAssign f ctx -> Assignment f (RListToCtx ctx)
rlistToAssign MNil = Ctx.empty
rlistToAssign (rlist :>: f) = extend (rlistToAssign rlist) f

-- | Convert a Crucible 'Index' to a Hobbits 'Member'
indexToMember :: Size ctx -> Index ctx tp -> Member (CtxToRList ctx) tp
indexToMember sz ix = case viewIndex sz ix of
  IndexViewLast _ -> Member_Base
  IndexViewInit ix' -> Member_Step $ indexToMember (decSize sz) ix'

-- | Convert a Crucible 'Index' into a Crucible context of contexts into a
-- Hobbits 'Member' in the associated 'RList' of 'RList's
indexCtxToMember :: Size ctx -> Index ctx c ->
                    Member (CtxCtxToRList ctx) (CtxToRList c)
indexCtxToMember sz ix = case viewIndex sz ix of
  IndexViewLast _ -> Member_Base
  IndexViewInit ix' -> Member_Step $ indexCtxToMember (decSize sz) ix'

-- | A data-level encapsulation of the 'KnownRepr' typeclass
data KnownReprObj f a = KnownRepr f a => KnownReprObj

-- | Build a 'KnownReprObj' using a phantom type
mkKnownReprObj :: KnownRepr f a => prx a -> KnownReprObj f a
mkKnownReprObj _ = KnownReprObj

-- | Extract the representation in a 'KnownReprObj'
unKnownReprObj :: KnownReprObj f a -> f a
unKnownReprObj (KnownReprObj :: KnownReprObj f a) = knownRepr :: f a

$(mkNuMatching [t| forall f a. KnownReprObj f a |])

instance Liftable (KnownReprObj f a) where
  mbLift (mbMatch -> [nuMP| KnownReprObj |]) = KnownReprObj

instance LiftableAny1 (KnownReprObj f) where
  mbLiftAny1 = mbLift

instance Liftable a => LiftableAny1 (Constant a) where
  mbLiftAny1 = mbLift

instance Liftable a => Liftable (Constant a b) where
  mbLift (mbMatch -> [nuMP| Data.Functor.Constant.Constant x |]) = Data.Functor.Constant.Constant (mbLift x)

instance (Liftable a, Liftable b, Liftable c) => Liftable (a,b,c) where
  mbLift (mbMatch -> [nuMP| (x,y,z) |]) = (mbLift x, mbLift y, mbLift z)

-- FIXME: this change for issue #28 requires ClosableAny1 to be exported from
-- Hobbits
{-
-- | A context of Crucible types
type CruCtx = RAssign TypeRepr

-- | Pattern for an empty 'CruCtx'
pattern CruCtxNil :: () => (ctx ~ RNil) => CruCtx ctx
pattern CruCtxNil = MNil

-- | Pattern for a non-empty 'CruCtx'
pattern CruCtxCons :: () => (ctx ~ (ctx' :> a)) =>
                         CruCtx ctx' -> TypeRepr a -> CruCtx ctx
pattern CruCtxCons tps tp <- tps :>: tp
  where
    CruCtxCons tps tp = tps :>: tp
-}

-- | A context of Crucible types
-- FIXME: should be defined in terms of 'RAssign' as above
data CruCtx ctx where
  CruCtxNil :: CruCtx RNil
  CruCtxCons :: CruCtx ctx -> TypeRepr a -> CruCtx (ctx :> a)

-- $(mkNuMatching [t| forall a. CruType a |])
$(mkNuMatching [t| forall ctx. CruCtx ctx |])

instance Liftable (CruCtx ctx) where
  mbLift mb_ctx = case mbMatch mb_ctx of
    [nuMP| CruCtxNil |] -> CruCtxNil
    [nuMP| CruCtxCons ctx a |] -> CruCtxCons (mbLift ctx) (mbLift a)

instance Closable (CruCtx ctx) where
  toClosed CruCtxNil = $(mkClosed [| CruCtxNil |])
  toClosed (CruCtxCons ctx a) =
    $(mkClosed [| CruCtxCons |]) `clApply` toClosed ctx `clApply` toClosed a

instance TestEquality CruCtx where
  testEquality CruCtxNil CruCtxNil = Just Refl
  testEquality (CruCtxCons ctx1 tp1) (CruCtxCons ctx2 tp2)
    | Just Refl <- testEquality ctx1 ctx2
    , Just Refl <- testEquality tp1 tp2
    = Just Refl
  testEquality _ _ = Nothing

instance PP.Pretty (CruCtx ctx) where
  pretty = PP.list . helper where
    helper :: CruCtx ctx' -> [PP.Doc ann]
    helper CruCtxNil = []
    helper (CruCtxCons ctx tp) = helper ctx ++ [PP.pretty tp]

instance KnownRepr CruCtx RNil where
  knownRepr = CruCtxNil

instance (KnownRepr CruCtx tps, KnownRepr TypeRepr tp) =>
         KnownRepr CruCtx (tps :> tp) where
  knownRepr = CruCtxCons knownRepr knownRepr

-- | Build a 'CruCtx' from a 'CtxRepr'
mkCruCtx :: CtxRepr ctx -> CruCtx (CtxToRList ctx)
mkCruCtx ctx = case viewAssign ctx of
  AssignEmpty -> CruCtxNil
  AssignExtend ctx' tp -> CruCtxCons (mkCruCtx ctx') tp

-- | Convert a 'CruCtx' to a 'CtxRepr'
cruCtxToRepr :: CruCtx ctx -> CtxRepr (RListToCtx ctx)
cruCtxToRepr CruCtxNil = Ctx.empty
cruCtxToRepr (CruCtxCons ctx tp) = Ctx.extend (cruCtxToRepr ctx) tp

-- | Build a proof that calling 'cruCtxToRepr' followed by 'mkCruCtx' yields
-- equal types
cruCtxToReprEq :: CruCtx ctx -> CtxToRList (RListToCtx ctx) :~: ctx
cruCtxToReprEq CruCtxNil = Refl
cruCtxToReprEq (CruCtxCons ctx _tp) =
  case cruCtxToReprEq ctx of
    Refl -> Refl

-- | Build a proof that calling 'mkCruCtx' followed by 'cruCtxToRepr' yields
-- equal types
reprToCruCtxEq :: CtxRepr ctx -> RListToCtx (CtxToRList ctx) :~: ctx
reprToCruCtxEq (viewAssign -> AssignEmpty) = Refl
reprToCruCtxEq (viewAssign -> AssignExtend ctx _) =
  case reprToCruCtxEq ctx of
    Refl -> Refl

-- | Build a proof that converting a Crucible context of contexts to a list of
-- lists and back again is the identity
reprReprToCruCtxCtxEq :: Assignment CtxRepr ctxs ->
                         RListToCtxCtx (CtxCtxToRList ctxs) :~: ctxs
reprReprToCruCtxCtxEq (viewAssign -> AssignEmpty) = Refl
reprReprToCruCtxCtxEq (viewAssign -> AssignExtend ctxs ctx)
  | (Refl, Refl) <- (reprReprToCruCtxCtxEq ctxs, reprToCruCtxEq ctx) = Refl

-- | Convert a 'CruCtx' to an assignment of 'TypeRepr's
--
-- FIXME: 'CruCtx' should just be defined as an assignment!
cruCtxToTypes :: CruCtx ctx -> RAssign TypeRepr ctx
cruCtxToTypes CruCtxNil = MNil
cruCtxToTypes (CruCtxCons tps tp) = cruCtxToTypes tps :>: tp

-- | Convert an assignment of 'TypeRepr's to a 'CruCtx'
--
-- FIXME: 'CruCtx' should just be defined as an assignment!
cruCtxOfTypes :: RAssign TypeRepr ctx -> CruCtx ctx
cruCtxOfTypes MNil = CruCtxNil
cruCtxOfTypes (tps :>: tp) = CruCtxCons (cruCtxOfTypes tps) tp

instance Show (CruCtx ctx) where
  show = show . cruCtxToRepr

-- | The empty context
emptyCruCtx :: CruCtx RNil
emptyCruCtx = CruCtxNil

-- | Build a singleton crucible context
singletonCruCtx :: TypeRepr tp -> CruCtx (RNil :> tp)
singletonCruCtx tp = CruCtxCons CruCtxNil tp

-- | Add an element to the end of a context
extCruCtx :: KnownRepr TypeRepr a => CruCtx ctx -> CruCtx (ctx :> a)
extCruCtx ctx = CruCtxCons ctx knownRepr

-- | Remove an element from the end of a context
unextCruCtx :: CruCtx (ctx :> a) -> CruCtx ctx
unextCruCtx (CruCtxCons ctx _) = ctx

-- | Append two contexts
appendCruCtx :: CruCtx ctx1 -> CruCtx ctx2 -> CruCtx (ctx1 :++: ctx2)
appendCruCtx ctx1 CruCtxNil = ctx1
appendCruCtx ctx1 (CruCtxCons ctx2 tp) = CruCtxCons (appendCruCtx ctx1 ctx2) tp

-- | Split a context in two
splitCruCtx :: prx1 ctx1 -> RAssign prx2 ctx2 -> CruCtx (ctx1 :++: ctx2) ->
               (CruCtx ctx1, CruCtx ctx2)
splitCruCtx _ MNil cru_ctx = (cru_ctx, CruCtxNil)
splitCruCtx ctx1 (ctx2 :>: _) (CruCtxCons cru_ctx tp) =
  let (cru_ctx1, cru_ctx2) = splitCruCtx ctx1 ctx2 cru_ctx in
  (cru_ctx1, CruCtxCons cru_ctx2 tp)

-- | Build a 'RAssign' phantom argument from a context of Crucible types
cruCtxProxies :: CruCtx ctx -> RAssign Proxy ctx
cruCtxProxies CruCtxNil = MNil
cruCtxProxies (CruCtxCons ctx _) = cruCtxProxies ctx :>: Proxy

-- | Compute the length of a 'CruCtx'
cruCtxLen :: CruCtx ctx -> Int
cruCtxLen CruCtxNil = 0
cruCtxLen (CruCtxCons ctx _) = 1 + cruCtxLen ctx

-- | Look up a type in a 'CruCtx'
cruCtxLookup :: CruCtx ctx -> Member ctx a -> TypeRepr a
cruCtxLookup CruCtxNil m = case m of {}
cruCtxLookup (CruCtxCons _ tp) Member_Base = tp
cruCtxLookup (CruCtxCons ctx _) (Member_Step memb) = cruCtxLookup ctx memb

-- | Build a 'CruCtx' of the given length.
cruCtxReplicate :: NatRepr n -> TypeRepr a -> Some CruCtx
cruCtxReplicate n tp =
  case isZeroNat n of
    ZeroNat -> Some CruCtxNil
    NonZeroNat
      | Some ctx <- cruCtxReplicate (predNat n) tp
      -> Some (CruCtxCons ctx tp)

-- | A representation of a context of types as a sequence of 'KnownRepr'
-- instances
--
-- FIXME: this can go away when existentials take explicit 'TypeRepr's instead
-- of 'KnownRepr TypeRepr' instances, as per issue #79
type KnownCruCtx = RAssign (KnownReprObj TypeRepr)

-- | Convert a 'KnownCruCtx' to a 'CruCtx'
knownCtxToCruCtx :: KnownCruCtx ctx -> CruCtx ctx
knownCtxToCruCtx MNil = CruCtxNil
knownCtxToCruCtx (ctx :>: KnownReprObj) =
  CruCtxCons (knownCtxToCruCtx ctx) knownRepr


----------------------------------------------------------------------
-- * Misc Operations on Crucible Objects
----------------------------------------------------------------------

-- | Get all the registers used in a Crucible statement
stmtInputRegs :: TraverseExt ext => Stmt ext ctx ctx' -> [Some (Reg ctx)]
stmtInputRegs (SetReg _ (Core.App app)) = foldMapFC (\r -> [Some r]) app
stmtInputRegs (ExtendAssign s') = foldMapFC (\r -> [Some r]) s'
stmtInputRegs (CallHandle _ h _ args) =
  Some h : foldMapFC (\r -> [Some r]) args
stmtInputRegs (Print msg) = [Some msg]
stmtInputRegs (ReadGlobal _) = []
stmtInputRegs (WriteGlobal _ r) = [Some r]
stmtInputRegs (FreshConstant _ _) = []
stmtInputRegs (FreshFloat _ _) = []
stmtInputRegs (FreshNat _) = []
stmtInputRegs (NewRefCell _ r) = [Some r]
stmtInputRegs (NewEmptyRefCell _) = []
stmtInputRegs (ReadRefCell r) = [Some r]
stmtInputRegs (WriteRefCell r1 r2) = [Some r1, Some r2]
stmtInputRegs (DropRefCell r) = [Some r]
stmtInputRegs (Assert r1 r2) = [Some r1, Some r2]
stmtInputRegs (Assume r1 r2) = [Some r1, Some r2]

-- | Get all the input and output registers of a Crucible statement
stmtOutputRegs :: TraverseExt ext => Size ctx' -> Stmt ext ctx ctx' ->
                  [Some (Reg ctx')]
stmtOutputRegs sz (SetReg _ (Core.App app)) =
  foldMapFC (\r -> [Some $ extendReg r]) app ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (ExtendAssign s') =
  foldMapFC (\r -> [Some $ extendReg r]) s' ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs sz (CallHandle _ h _ args) =
  Some (extendReg h) : foldMapFC (\r -> [Some $ extendReg r]) args
  ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs _ (Print msg) = [Some msg]
stmtOutputRegs _ (ReadGlobal _) = []
stmtOutputRegs _ (WriteGlobal _ r) = [Some r]
stmtOutputRegs _ (FreshConstant _ _) = []
stmtOutputRegs _ (FreshFloat _ _) = []
stmtOutputRegs _ (FreshNat _) = []
stmtOutputRegs sz (NewRefCell _ r) =
  [Some $ extendReg r] ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs _ (NewEmptyRefCell _) = []
stmtOutputRegs sz (ReadRefCell r) =
  [Some $ extendReg r] ++ [Some $ Reg $ Ctx.lastIndex sz]
stmtOutputRegs _ (WriteRefCell r1 r2) = [Some r1, Some r2]
stmtOutputRegs _ (DropRefCell r) = [Some r]
stmtOutputRegs _ (Assert r1 r2) = [Some r1, Some r2]
stmtOutputRegs _ (Assume r1 r2) = [Some r1, Some r2]

-- | Get all the registers used in a Crucible 'JumpTarget'
jumpTargetRegs :: JumpTarget blocks ctx -> [Some (Reg ctx)]
jumpTargetRegs (JumpTarget _ _ regs) = foldMapFC (\r -> [Some r]) regs

-- | Get all the registers used in a Crucible 'SwitchTarget'
switchTargetRegs :: SwitchTarget blocks ctx tp -> [Some (Reg ctx)]
switchTargetRegs (SwitchTarget _ _ regs) = foldMapFC (\r -> [Some r]) regs

-- | Get all the registers used in a Crucible termination statement
termStmtRegs :: TermStmt blocks ret ctx -> [Some (Reg ctx)]
termStmtRegs (Jump tgt) = jumpTargetRegs tgt
termStmtRegs (Br cond tgt1 tgt2) =
  Some cond : jumpTargetRegs tgt1 ++ jumpTargetRegs tgt2
termStmtRegs (MaybeBranch _ cond stgt tgt) =
  Some cond : switchTargetRegs stgt ++ jumpTargetRegs tgt
termStmtRegs (VariantElim _ cond stgts) =
  Some cond : foldMapFC switchTargetRegs stgts
termStmtRegs (Return reg) = [Some reg]
termStmtRegs (TailCall reg _ regs) =
  Some reg : foldMapFC (\r -> [Some r]) regs
termStmtRegs (ErrorStmt reg) = [Some reg]

{-
Note [QuantifiedConstraints + TypeFamilies trick]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC 9.2 and later are reasonably adept and combining TypeFamilies with type
classes that have quantified superclasses. This is important, as there are
several places in heapster-saw that require constraints of the form
`NuMatchingAny1 (ExprExtension ext f)`, where NuMatchingAny1 has a quantified
superclass and ExprExtension is a type family.

Unfortunately, GHC 9.0 and earlier suffer from a bug where constraints of the
form `NuMatchingAny1 (ExprExtension ext f)`. See
https://gitlab.haskell.org/ghc/ghc/-/issues/14860. Thankfully, it is relatively
straightforward to work around the bug. Instead of writing instances like
these:

  instance forall ext f.
           NuMatchingAny1 (ExprExtension ext f) =>
           NuMatchingAny (Foo ext f tp)

We instead write instances like these, introducing an intermediate `exprExt`
type variable that is used in conjunction with an equality constraint:

  instance forall ext f exprExt.
           (exprExt ~ ExprExtension ext f, NuMatchingAny1 exprExt) =>
           NuMatchingAny (Foo ext f tp)

A bit tedious, but this version actually works on pre-9.2 GHCs, which is nice.

I have guarded each use of this trick with CPP so that we remember to remove
this workaround when we drop support for pre-9.2 GHCs.
-}
