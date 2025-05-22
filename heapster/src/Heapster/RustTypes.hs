{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# OPTIONS_GHC -freduction-depth=0 #-}

module Heapster.RustTypes where

import Prelude hiding (span)

import Data.Maybe
import Data.List (delete, find, findIndex, intersperse)
import GHC.TypeLits
import qualified Data.BitVector.Sized as BV
import Data.Functor.Constant
import Data.Functor.Product
import qualified Control.Applicative as App
import Control.Monad (MonadPlus(..))
import Control.Monad.Except (Except, MonadError(..), runExcept)
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Fail as Fail

import Data.Parameterized.BoolRepr
import Data.Parameterized.Some
import Data.Parameterized.Context (Assignment, IsAppend(..),
                                   incSize, zeroSize, sizeInt,
                                   size, generate, extend)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableF

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import qualified Data.Type.RList as RL
import qualified Data.Binding.Hobbits.NameSet as NameSet

import Language.Rust.Syntax
import Language.Rust.Parser
import qualified Language.Rust.Pretty as RustPP
import Language.Rust.Data.Ident (Ident(..), name)

import Prettyprinter as PP

import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.MemModel hiding (Mutability(..))

import Heapster.CruUtil
import Heapster.Permissions


----------------------------------------------------------------------
-- * Data types and related types
----------------------------------------------------------------------

-- | A permission of some llvm pointer type
data SomeLLVMPerm =
  forall w. (1 <= w, KnownNat w) => SomeLLVMPerm (ValuePerm (LLVMPointerType w))

-- | An 'ArgLayoutPerm' is a set of permissions on a sequence of 0 or more
-- arguments, given by the @tps@ type-level argument. These permissions are
-- similar to the language of permissions on a Crucible struct, except that the
-- langauge is restricted to ensure that they can always be appended.
--
-- FIXME: add support for shapes like bool whose size is smaller than a byte,
-- with the constraint that the end result should only have fields whose sizes
-- are whole numbers of bytes. The idea would be to allow sub-byte-sized fields
-- be appended, but to then round their sizes up to whole numbers of bytes at
-- disjunctions and at the top level.
data ArgLayoutPerm ctx where
  ALPerm :: RAssign ValuePerm (CtxToRList ctx) -> ArgLayoutPerm ctx
  ALPerm_Or :: ArgLayoutPerm ctx -> ArgLayoutPerm ctx -> ArgLayoutPerm ctx
  ALPerm_Exists :: KnownRepr TypeRepr a =>
                   Binding a (ArgLayoutPerm ctx) -> ArgLayoutPerm ctx

-- | An argument layout captures how argument values are laid out as a Crucible
-- struct of 0 or more machine words / fields
data ArgLayout where
  ArgLayout :: CtxRepr ctx -> ArgLayoutPerm ctx -> ArgLayout

-- | Like an 'ArgLayout' but with output permissions on arguments as well
data ArgLayoutIO where
  ArgLayoutIO :: CtxRepr ctx -> ArgLayoutPerm ctx ->
                 RAssign ValuePerm (CtxToRList ctx) -> ArgLayoutIO

-- | Function permission that is existential over all types (note that there
-- used to be 3 type variables instead of 4 for 'FunPerm', thus the name)
data Some3FunPerm =
  forall ghosts args gouts ret. Some3FunPerm (FunPerm ghosts args gouts ret)


----------------------------------------------------------------------
-- * Template Haskell–generated instances
----------------------------------------------------------------------

$(mkNuMatching [t| SomeLLVMPerm |])
$(mkNuMatching [t| forall ctx. ArgLayoutPerm ctx |])
$(mkNuMatching [t| ArgLayout |])
$(mkNuMatching [t| Some3FunPerm |])


----------------------------------------------------------------------
-- * Helper Definitions
----------------------------------------------------------------------

-- | A version of 'mbSeparate' that takes in an explicit phantom argument for
-- the first context
mbSeparatePrx :: prx1 ctx1 -> RAssign prx2 ctx2 -> Mb (ctx1 :++: ctx2) a ->
                 Mb ctx1 (Mb ctx2 a)
mbSeparatePrx _ = mbSeparate

-- | Reassociate a binding list
mbAssoc :: prx1 ctx1 -> RAssign prx2 ctx2 -> RAssign prx3 ctx3 ->
           Mb (ctx1 :++: (ctx2 :++: ctx3)) a ->
           Mb ((ctx1 :++: ctx2) :++: ctx3) a
mbAssoc ctx1 ctx2 ctx3 mb_a | Refl <- RL.appendAssoc ctx1 ctx2 ctx3 = mb_a

-- | Reassociate a binding list in the reverse direction of 'mbAssoc'
mbUnAssoc :: prx1 ctx1 -> RAssign prx2 ctx2 -> RAssign prx3 ctx3 ->
             Mb ((ctx1 :++: ctx2) :++: ctx3) a ->
             Mb (ctx1 :++: (ctx2 :++: ctx3)) a
mbUnAssoc ctx1 ctx2 ctx3 mb_a | Refl <- RL.appendAssoc ctx1 ctx2 ctx3 = mb_a

-- | Prove type-level equality by reassociating four type lists
appendAssoc4 :: RAssign Proxy ctx1 -> RAssign Proxy ctx2 ->
                RAssign Proxy ctx3 -> RAssign Proxy ctx4 ->
                ctx1 :++: ((ctx2 :++: ctx3) :++: ctx4) :~:
                ((ctx1 :++: ctx2) :++: ctx3) :++: ctx4
appendAssoc4 ctx1 ctx2 ctx3 ctx4
  | Refl <- RL.appendAssoc ctx1 (RL.append ctx2 ctx3) ctx4
  , Refl <- RL.appendAssoc ctx1 ctx2 ctx3
  = Refl

-- | Reassociate a binding list of four contexts
mbAssoc4 :: RAssign Proxy ctx1 -> RAssign Proxy ctx2 ->
            RAssign Proxy ctx3 -> RAssign Proxy ctx4 ->
            Mb (ctx1 :++: ((ctx2 :++: ctx3) :++: ctx4)) a ->
            Mb (((ctx1 :++: ctx2) :++: ctx3) :++: ctx4) a
mbAssoc4 ctx1 ctx2 ctx3 ctx4 mb_a
  | Refl <- appendAssoc4 ctx1 ctx2 ctx3 ctx4 = mb_a

-- | Combine bindings lists using 'mbCombine' and reassociate them
mbCombineAssoc ::
  prx1 ctx1 ->
  RAssign prx2 ctx2 ->
  RAssign prx3 ctx3 ->
  Mb ctx1 (Mb (ctx2 :++: ctx3) a) ->
  Mb ((ctx1 :++: ctx2) :++: ctx3) a
mbCombineAssoc _ ctx2 ctx3
  = mbCombine (RL.mapRAssign (const Proxy) ctx3)
  . mbCombine (RL.mapRAssign (const Proxy) ctx2)
  . fmap (mbSeparatePrx ctx2 ctx3)

-- | Combine bindings lists using 'mbCombine' and reassociate them
mbCombineAssoc4 ::
  RAssign Proxy ctx1 -> RAssign Proxy ctx2 ->
  RAssign Proxy ctx3 -> RAssign Proxy ctx4 ->
  Mb ctx1 (Mb ((ctx2 :++: ctx3) :++: ctx4) a) ->
  Mb (((ctx1 :++: ctx2) :++: ctx3) :++: ctx4) a
mbCombineAssoc4 ctx1 ctx2 ctx3 ctx4 mb_mb_a
  | Refl <- appendAssoc4 ctx1 ctx2 ctx3 ctx4
  = mbCombine ((ctx2 `RL.append` ctx3) `RL.append` ctx4) mb_mb_a

-- | Prepend and reassociate an 'RAssign'
assocAppend :: RAssign f ctx1 -> prx2 ctx2 -> RAssign prx3 ctx3 ->
               RAssign f (ctx2 :++: ctx3) ->
               RAssign f ((ctx1 :++: ctx2) :++: ctx3)
assocAppend fs1 ctx2 ctx3 fs23 =
  let (fs2, fs3) = RL.split ctx2 ctx3 fs23 in
  RL.append (RL.append fs1 fs2) fs3

-- | Prepend and reassociate an 'RAssign' to get one with four type contexts
assocAppend4 :: RAssign f ctx1 -> prx2 ctx2 -> RAssign prx3 ctx3 ->
                RAssign prx4 ctx4 ->
                RAssign f ((ctx2 :++: ctx3) :++: ctx4) ->
                RAssign f (((ctx1 :++: ctx2) :++: ctx3) :++: ctx4)
assocAppend4 fs1 ctx2 ctx3 ctx4 fs234 =
  let (fs2, fs3, fs4) = rlSplit3 ctx2 ctx3 ctx4 fs234 in
  RL.append (RL.append (RL.append fs1 fs2) fs3) fs4

-- | Info used for converting Rust types to shapes
-- NOTE: @rciRecType@ should probably have some info about lifetimes
data RustConvInfo =
  RustConvInfo { rciPermEnv :: PermEnv,
                 rciCtx :: [(String, TypedName)],
                 rciRecType :: Maybe (RustName, [RustName], TypedName) }

-- | The default, top-level 'RustConvInfo' for a given 'PermEnv'
mkRustConvInfo :: PermEnv -> RustConvInfo
mkRustConvInfo env =
  RustConvInfo { rciPermEnv = env, rciCtx = [], rciRecType = Nothing }

-- | The Rust conversion monad is just a state-error monad
newtype RustConvM a =
  RustConvM { unRustConvM :: ReaderT RustConvInfo (Except String) a }
  deriving (Functor, Applicative, Monad,
            MonadError String, MonadReader RustConvInfo)

instance Fail.MonadFail RustConvM where
  fail = RustConvM . throwError

instance MonadBind RustConvM where
  mbM mb_m = RustConvM $ mbM $ fmap unRustConvM mb_m

-- | Prefix any error message with location information
atSpan :: Span -> RustConvM a -> RustConvM a
atSpan span m =
  catchError m (\msg -> fail ("At " ++ show span ++ ": " ++ msg))

-- | Run a Rust conversion computation with the given 'RustConvInfo', lifting
-- any errors into the outer monad
runLiftRustConvM :: Fail.MonadFail m => RustConvInfo -> RustConvM a -> m a
runLiftRustConvM info (RustConvM m) =
  case runExcept (runReaderT m info) of
    Left err -> fail err
    Right x -> return x

-- | Look up the 'TypedName' associated with a 'String' name
lookupTypedName :: String -> RustConvM TypedName
lookupTypedName str =
  fmap (lookup str) (rciCtx <$> ask) >>= \case
  Just n -> return n
  Nothing -> fail ("Could not find variable: " ++ show str)

-- | Look up a 'Name' with a given type
lookupName :: String -> TypeRepr a -> RustConvM (Name a)
lookupName str tp =
  lookupTypedName str >>= \n -> castTypedM "variable" tp n

-- | Build a 'PPInfo' structure for the names currently in scope
rsPPInfo :: RustConvM PPInfo
rsPPInfo =
  foldr (\(str, Some (Typed _ n)) -> ppInfoAddExprName str n) emptyPPInfo <$>
  rciCtx <$> ask

-- | The conversion of a context of Rust type and lifetime variables
type RustCtx = RAssign (Product (Constant String) TypeRepr)

-- | Build a 'RustCtx' for a single variable
rustCtx1 :: String -> TypeRepr a -> RustCtx (RNil :> a)
rustCtx1 name tp = MNil :>: Pair (Constant name) tp

-- | Extract a 'CruCtx' from a 'RustCtx'
rustCtxCtx :: RustCtx ctx -> CruCtx ctx
rustCtxCtx = cruCtxOfTypes . RL.map (\(Pair _ tp) -> tp)

-- | Extend a 'RustCtx' with a single binding on the right
rustCtxCons :: RustCtx ctx -> String -> TypeRepr a -> RustCtx (ctx :> a)
rustCtxCons ctx nm tp = ctx :>: Pair (Constant nm) tp

-- | Build a 'RustCtx' from the given variable names, all having the same type
rustCtxOfNames :: TypeRepr a -> [String] -> Some RustCtx
rustCtxOfNames tp =
  foldl (\(Some ctx) name -> Some (ctx :>: Pair (Constant name) tp)) (Some MNil)

-- | Run a 'RustConvM' computation in a context of bound type-level variables,
-- where the bound names are passed to the computation
inRustCtxF :: NuMatching a => RustCtx ctx -> (RAssign Name ctx -> RustConvM a) ->
              RustConvM (Mb ctx a)
inRustCtxF ctx m =
  mbM $ nuMulti (RL.map (\_ -> Proxy) ctx) $ \ns ->
  let ns_ctx =
        RL.toList $ RL.map2 (\n (Pair (Constant str) tp) ->
                              Constant (str, Some (Typed tp n))) ns ctx in
  local (\info -> info { rciCtx = ns_ctx ++ rciCtx info }) (m ns)

-- | Run a 'RustConvM' computation in a context of bound type-level variables
inRustCtx :: NuMatching a => RustCtx ctx -> RustConvM a ->
             RustConvM (Mb ctx a)
inRustCtx ctx m = inRustCtxF ctx (const m)

-- | Class for a generic \"conversion from Rust\" function, given the bit width
-- of the pointer type
class RsConvert w a b | w a -> b where
  rsConvert :: (1 <= w, KnownNat w) => prx w -> a -> RustConvM b


----------------------------------------------------------------------
-- * Converting Named Rust Types
----------------------------------------------------------------------

-- | A function that builds a shape from a sequence of 'PermExpr' arguments and
-- a 'String' representation of them for printing errors
type ShapeFun w =
  Some TypedPermExprs -> String -> RustConvM (PermExpr (LLVMShapeType w))

-- | A sequence of 'PermExprs' along with their types
type TypedPermExprs = RAssign (Typed PermExpr)

-- | The empty sequence of typed permission expressions
emptyTypedPermExprs :: Some TypedPermExprs
emptyTypedPermExprs = Some MNil

appendTypedExprs :: Some TypedPermExprs -> Some TypedPermExprs ->
                    Some TypedPermExprs
appendTypedExprs (Some exprs1) (Some exprs2) = Some (RL.append exprs1 exprs2)

-- | Extract a type context from a 'TypedPermExprs'
typedPermExprsCtx :: TypedPermExprs ctx -> CruCtx ctx
typedPermExprsCtx = cruCtxOfTypes . RL.map typedType

-- | Extract the expressions from a 'TypedPermExprs'
typedPermExprsExprs :: TypedPermExprs ctx -> PermExprs ctx
typedPermExprsExprs = rassignToExprs . RL.map typedObj

-- | Convert a list of epxressions of a given type to a TypedPermExprs
typedExprsOfList :: TypeRepr a -> [PermExpr a] -> Some TypedPermExprs
typedExprsOfList tp =
  foldl (\(Some es) e -> Some (es :>: Typed tp e)) (Some MNil)

-- | Build a 'ShapeFun' for the given 'RustName' from a function on permission
-- expressions of the supplied types
mkShapeFun :: RustName -> CruCtx ctx ->
              (PermExprs ctx -> PermExpr (LLVMShapeType w)) -> ShapeFun w
mkShapeFun nm ctx f = \some_exprs exprs_str -> case some_exprs of
  Some exprs
    | Just Refl <- testEquality ctx (typedPermExprsCtx exprs) ->
      return $ f (typedPermExprsExprs exprs)
  _ ->
    fail $ renderDoc $ fillSep
    [ pretty "Converting application of type:" <+> pretty (show nm)
    , pretty "To arguments:" <+> pretty exprs_str
    , pretty "Arguments not of expected types:" <+> pretty ctx ]

-- | Build a 'ShapeFun' with no arguments
constShapeFun :: RustName -> PermExpr (LLVMShapeType w) -> ShapeFun w
constShapeFun nm sh = mkShapeFun nm CruCtxNil (const sh)

-- | Test if a shape is \"option-like\", meaning it is a tagged union shape with
-- two tags, one of which has contents and one which has no contents; i.e., it
-- is of the form
--
-- > (fieldsh(eq(llvmword(bv1)));sh) orsh (fieldsh(eq(llvmword(bv2))))
--
-- or
--
-- > (fieldsh(eq(llvmword(bv1)))) orsh (fieldsh(eq(llvmword(bv2)));sh)
--
-- where @sh@ is non-empty. If so, return the non-empty shape @sh@, called the
-- \"payload\" shape.
matchOptionLikeShape :: PermExpr (LLVMShapeType w) ->
                        Maybe (PermExpr (LLVMShapeType w))
matchOptionLikeShape top_sh = case asTaggedUnionShape top_sh of
  Just (SomeTaggedUnionShape (taggedUnionDisjsNoTags ->
                              [PExpr_EmptyShape, PExpr_EmptyShape])) -> Nothing
  Just (SomeTaggedUnionShape (taggedUnionDisjsNoTags ->
                              [PExpr_EmptyShape, sh])) -> Just sh
  Just (SomeTaggedUnionShape (taggedUnionDisjsNoTags ->
                              [sh, PExpr_EmptyShape])) -> Just sh
  _ -> Nothing

-- | Test if a shape-in-binding is \"option-like\" as per 'matchOptionLikeShape'
matchMbOptionLikeShape :: Mb ctx (PermExpr (LLVMShapeType w)) ->
                          Maybe (Mb ctx (PermExpr (LLVMShapeType w)))
matchMbOptionLikeShape =
  mbMaybe . mbMapCl $(mkClosed [| matchOptionLikeShape |])

-- | Test if a shape is a sum type where one branch is empty, i.e., a tagged
-- union shape with two tags, one of which has the false shape as contents. If
-- so, return the non-false shape @sh@.
matchSumFalseShape :: PermExpr (LLVMShapeType w) ->
                      Maybe (PermExpr (LLVMShapeType w))
matchSumFalseShape top_sh = case asTaggedUnionShape $ simplifyShape top_sh of
  Just (SomeTaggedUnionShape (taggedUnionDisjsNoTags -> [sh1, sh2]))
    | PExpr_FalseShape <- simplifyShape sh1 -> Just sh2
  Just (SomeTaggedUnionShape (taggedUnionDisjsNoTags -> [sh1, sh2]))
    | PExpr_FalseShape <- simplifyShape sh2 -> Just sh1
  _ -> Nothing


-- | Build a `ShapeFun` from a `SomeNamedShape`
namedShapeShapeFun :: (1 <= w, KnownNat w) => RustName -> NatRepr w ->
                      SomeNamedShape -> RustConvM (ShapeFun w)
-- For an option-like shape, try to do discriminant elision
namedShapeShapeFun nm w (SomeNamedShape nmsh)
  | Just Refl <- testEquality w (natRepr nmsh)
  , DefinedShapeBody mb_sh <- namedShapeBody nmsh
  , Just mb_payload_sh <- matchMbOptionLikeShape mb_sh =
    return $ mkShapeFun nm (namedShapeArgs nmsh) $ \exprs ->
    case simplifyShape (subst (substOfExprs exprs) mb_payload_sh) of

      -- If the payload is a pointer shape, return payload orsh eq(0)
      payload_sh@(isLLVMPointerShape -> True) ->
        PExpr_OrShape payload_sh $ llvmEqWordShape w 0

      -- If the payload is a tagged union shape, add an extra tag with an empty
      -- shape for its argument
      (asTaggedUnionShape -> Just (SomeTaggedUnionShape tag_u)) ->
        let new_tag =
              foldr max 0 $ map ((1+) . BV.asUnsigned) $
              taggedUnionTags tag_u in
        taggedUnionToShape $
        taggedUnionCons (BV.mkBV knownNat new_tag) (llvmEqWordShape w new_tag)
        tag_u

      -- Otherwise, just use the named shape itself
      _ -> PExpr_NamedShape Nothing Nothing nmsh exprs

namedShapeShapeFun nm w (SomeNamedShape nmsh)
  | Just Refl <- testEquality w (natRepr nmsh) =
    return $ mkShapeFun nm (namedShapeArgs nmsh) $ \exprs ->
    case namedShapeBody nmsh of
      -- Test if nmsh applied to exprs unfolds to a sum with false, and if so,
      -- return just the non-false payload shape
      DefinedShapeBody mb_sh
        | unfolded_sh <- simplifyShape (subst (substOfExprs exprs) mb_sh)
        , Just sh <- matchSumFalseShape unfolded_sh ->
          sh
      -- Otherwise just return the named shape applied to exprs
      _ -> PExpr_NamedShape Nothing Nothing nmsh exprs

namedShapeShapeFun _ w (SomeNamedShape nmsh) =
  fail $ renderDoc $ fillSep
  [pretty "Incorrect size of shape" <+> pretty (namedShapeName nmsh),
   pretty "Expected:" <+> pretty (intValue w),
   pretty "Actual:" <+> pretty (intValue (natRepr nmsh))]

-- | A fully qualified Rust path without any of the parameters; e.g.,
-- @Foo<X>::Bar<Y,Z>::Baz@ just becomes @[Foo,Bar,Baz]@
newtype RustName = RustName [Ident] deriving (Eq)

-- | Convert a 'RustName' to a string by interspersing @"::"@
flattenRustName :: RustName -> String
flattenRustName (RustName ids) = concat $ intersperse "::" $ map name ids

instance Show RustName where
  show = show . flattenRustName

instance RsConvert w RustName (ShapeFun w) where
  rsConvert w nm =
    do let str = flattenRustName nm
       env <- rciPermEnv <$> ask
       case lookupNamedShape env str of
         Just nmsh -> namedShapeShapeFun nm (natRepr w) nmsh
         Nothing ->
           do n <- lookupName str (LLVMShapeRepr (natRepr w))
              return $ constShapeFun nm (PExpr_Var n)

-- | Get the \"name\" = sequence of identifiers out of a Rust path
rsPathName :: Path a -> RustName
rsPathName (Path _ segments _) =
  RustName $ map (\(PathSegment rust_id _ _) -> rust_id) segments

-- | Get all the parameters out of a Rust path
rsPathParams :: Path a -> [PathParameters a]
rsPathParams (Path _ segments _) =
  mapMaybe (\(PathSegment _ maybe_params _) -> maybe_params) segments

-- | Get the 'RustName' of a type, if it's a 'PathTy'
tyName :: Ty a -> Maybe RustName
tyName (PathTy _ path _) = Just $ rsPathName path
tyName _ = Nothing

-- | Decide whether a Rust type is named (i.e. a 'PathTy')
isNamedType :: Ty a -> Bool
isNamedType (PathTy _ _ _) = True
isNamedType _ = False

-- | Decide whether 'PathParameters' are all named types (angle-bracketed only)
isNamedParams :: PathParameters a -> Bool
isNamedParams (AngleBracketed _ tys _ _) = all isNamedType tys
isNamedParams _ = error "Parenthesized types not supported"

-- | Decide whether a Rust type definition is polymorphic and \"Option-like\";
-- that is, it contains only one data-bearing variant, and the data is of the
-- polymorphic type
isPolyOptionLike :: Item Span -> Bool
isPolyOptionLike (Enum _ _ _ variants (Generics _ [TyParam _ t _ _ _] _ _) _) =
  -- Short-circuit if no variant carries the type parameter. Otherwise check
  -- that all other variants carry nothing
  case find containsT variants of
    Nothing -> False
    Just v -> all isUnitVariant (delete v variants)
  where
    containsT (Variant _ _ (TupleD [StructField _ _ (PathTy _ (Path _ [PathSegment t' _ _] _) _) _ _] _) _ _) =
      name t == name t'
    containsT (Variant _ _ (StructD [StructField _ _ (PathTy _ (Path _ [PathSegment t' _ _] _) _) _ _] _) _ _) =
      name t == name t'
    containsT _ = False

    isUnitVariant (Variant _ _ (UnitD _) _ _) = True
    isUnitVariant _ = False
isPolyOptionLike _ = False

-- | Get all of the 'RustName's of path parameters, if they're angle-bracketed
pParamNames :: PathParameters a -> [RustName]
pParamNames (AngleBracketed _ tys _ _) = mapMaybe tyName tys
pParamNames _ = error "Parenthesized types not supported"

-- | Modify a 'RustConvM' to be run with a recursive type
withRecType :: (1 <= w, KnownNat w) => RustName -> [RustName] -> Name (LLVMShapeType w) ->
               RustConvM a -> RustConvM a
withRecType rust_n rust_ns rec_n = local (\info -> info { rciRecType = Just (rust_n, rust_ns, Some (Typed knownRepr rec_n)) })


----------------------------------------------------------------------
-- * Converting Rust Types to Heapster Shapes
----------------------------------------------------------------------

-- | Test if a shape matches the translation of a slice type, and, if so, return
-- the stride and the fields of the slice, where the latter can have the length
-- free
matchSliceShape :: PermExpr (LLVMShapeType w) ->
                   Maybe (Bytes,
                          Binding (BVType w) (PermExpr (LLVMShapeType w)))
matchSliceShape (PExpr_ExShape
                 [nuP| PExpr_ArrayShape (PExpr_Var len) stride mb_sh |])
  | Left Member_Base <- mbNameBoundP len =
    Just (mbLift stride, mb_sh)
matchSliceShape (PExpr_NamedShape _ _ nmsh@(NamedShape _ _
                                            (DefinedShapeBody _)) args) =
  matchSliceShape (unfoldNamedShape nmsh args)
matchSliceShape _ = Nothing

-- Convert a 'Mutability' to a modality override for a 'PExpr_PtrShape'; mutable
-- references inherit the modality of the container they are in, so they
-- translate to 'Nothing'
instance RsConvert w Mutability (Maybe (PermExpr RWModalityType)) where
  rsConvert _ Mutable = return Nothing
  rsConvert _ Immutable = return (Just PExpr_Read)

instance RsConvert w (Lifetime Span) (PermExpr LifetimeType) where
  rsConvert _ (Lifetime "static" _) = return PExpr_Always
  rsConvert _ (Lifetime l span) =
    PExpr_Var <$> atSpan span (lookupName l knownRepr)

instance RsConvert w (PathParameters Span) (Some TypedPermExprs) where
  rsConvert w (AngleBracketed rust_ls rust_tps [] _) =
    do ls <- mapM (rsConvert w) rust_ls
       shs <- mapM (rsConvert w) rust_tps
       return $ appendTypedExprs
         (typedExprsOfList knownRepr ls) (typedExprsOfList knownRepr shs)
  rsConvert _ (AngleBracketed _ _ (_:_) _) =
    error "rsConvert: angle-bracketed arguments not supported"
  rsConvert _ (Parenthesized _ _ _) =
    error "rsConvert: parenthesized types not supported"

instance RsConvert w [PathParameters Span] (Some TypedPermExprs) where
  rsConvert w paramss =
    foldr appendTypedExprs emptyTypedPermExprs <$> mapM (rsConvert w) paramss

instance RsConvert w (Ty Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (Slice tp _) =
    do sh <- rsConvert w tp
       case llvmShapeLength sh of
         Just (bvMatchConstInt -> Just stride) ->
           return (PExpr_ExShape $ nu $ \n ->
                    PExpr_ArrayShape (PExpr_Var n) (fromInteger stride) sh)
         _ ->
           rsPPInfo >>= \ppInfo ->
           fail ("rsConvert: slices not supported for dynamically-sized type: "
                 ++ show (RustPP.pretty tp) ++ " with translation:\n"
                 ++ renderDoc (permPretty ppInfo sh))
  rsConvert _ (Rptr Nothing _ _ _) =
    fail "rsConvert: lifetimes must be supplied for reference types"
  rsConvert w (Rptr (Just rust_l) mut tp' _) =
    do l <- rsConvert w rust_l
       sh <- rsConvert w tp'
       rw <- rsConvert w mut
       case sh of
         -- Test if sh is a slice type = an array of existential length
         (matchSliceShape -> Just (stride,mb_sh)) ->
           -- If so, build a "fat pointer" = a pair of a pointer to our array
           -- shape plus a length value
           return $ PExpr_ExShape $ nu $ \n ->
           PExpr_SeqShape (PExpr_PtrShape rw (Just l) $
                           PExpr_ArrayShape (PExpr_Var n) stride $
                           subst1 (PExpr_Var n) mb_sh)
           (PExpr_FieldShape $ LLVMFieldShape $ ValPerm_Eq $
            PExpr_LLVMWord $ PExpr_Var n)

         -- If it's not a slice, make sure it has a known size
         _ | Just len <- llvmShapeLength sh
           , isJust (bvMatchConst len) ->
             return $ PExpr_PtrShape rw (Just l) sh

         -- Otherwise, it's a non-standard dynamically-sized type, which we
         -- don't quite know how to handle yet...
         _ -> fail "rsConvert: pointer to non-slice dynamically-sized type"
  rsConvert w (PathTy Nothing path _) =
    do mrec <- asks rciRecType
       case mrec of
         Just (rec_n, rec_arg_ns, sh_nm)
           | rec_n == rsPathName path &&
             all isNamedParams (rsPathParams path) &&
             rec_arg_ns == concatMap pParamNames (rsPathParams path) ->
             PExpr_Var <$> castTypedM "TypedName" (LLVMShapeRepr (natRepr w)) sh_nm
         Just (rec_n, _, _)
           | rec_n == rsPathName path -> fail "Arguments do not match"
         _ ->
           do shapeFn <- rsConvert w (rsPathName path)
              someTypedArgs <- rsConvert w (rsPathParams path)
              shapeFn someTypedArgs $ show (RustPP.prettyUnresolved path)
  rsConvert (w :: prx w) (BareFn _ abi rust_ls2 fn_tp span) =
    do Some3FunPerm fun_perm <- rsConvertMonoFun w span abi rust_ls2 fn_tp
       let args = funPermArgs fun_perm
       case cruCtxToReprEq args of
         Refl ->
           return $ PExpr_FieldShape $ LLVMFieldShape @w @w $ ValPerm_Conj1 $
           Perm_LLVMFunPtr
           (FunctionHandleRepr (cruCtxToRepr args) (funPermRet fun_perm)) $
           ValPerm_Conj1 $ Perm_Fun fun_perm
  rsConvert w (TupTy tys _) =
    do tyShs <- mapM (rsConvert w) tys
       return $ foldr PExpr_SeqShape PExpr_EmptyShape tyShs
  rsConvert _ (Never _) =
    return $ PExpr_FalseShape
  rsConvert _ tp = fail ("Rust type not supported: " ++ show tp)

instance RsConvert w (Arg Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (Arg _ tp _) = rsConvert w tp
  rsConvert _ _ = error "rsConvert (Arg): argument form not yet handled"

instance RsConvert w (Generics Span) (Some RustCtx) where
  rsConvert w (Generics ltdefs tyvars _ _) =
    return $ foldl addTyVar (foldl addLt (Some MNil) ltdefs) tyvars
    where
      addLt (Some ctx) ltdef =
        Some (ctx :>: Pair (Constant (lifetimeDefName ltdef)) LifetimeRepr)

      addTyVar (Some ctx) tyvar =
        Some (ctx :>: Pair (Constant (tyParamName tyvar)) (LLVMShapeRepr (natRepr w)))

-- | Return true if and only if the provided Rust type definition is recursive
isRecursiveDef :: Item Span -> Bool
isRecursiveDef item =
  case item of
    Enum _ _ n variants _ _ -> any (containsName n . getVD) variants
    StructItem _ _ n vd _ _ -> containsName n vd
    _ -> False

  where
    tyContainsName :: Ident -> Ty Span -> Bool
    tyContainsName i ty =
      case ty of
        Slice t _                  -> tyContainsName i t
        Language.Rust.Syntax.Array t _ _ -> tyContainsName i t
        Ptr _ t _                  -> tyContainsName i t
        Rptr _ _ t _               -> tyContainsName i t
        TupTy ts _                 -> any (tyContainsName i) ts
        PathTy _ (Path _ segs _) _ -> any (segContainsName i) segs
        ParenTy t _                -> tyContainsName i t
        _                          -> False

    segContainsName :: Ident -> PathSegment Span -> Bool
    segContainsName i (PathSegment i' mParams _) =
      i == i' || case mParams of
                   Nothing -> False
                   Just params -> paramsContainName i params

    paramsContainName :: Ident -> PathParameters Span -> Bool
    paramsContainName i (AngleBracketed _ tys _ _) = any (tyContainsName i) tys
    paramsContainName _ (Parenthesized _ _ _) = error "Parenthesized types not supported"

    typeOf :: StructField Span -> Ty Span
    typeOf (StructField _ _ t _ _) = t

    getVD :: Variant Span -> VariantData Span
    getVD (Variant _ _ vd _ _) = vd

    containsName :: Ident -> VariantData Span -> Bool
    containsName i (StructD fields _) = any (tyContainsName i) $ typeOf <$> fields
    containsName i (TupleD fields _) = any (tyContainsName i) $ typeOf <$> fields
    containsName _ (UnitD _) = False

-- | NOTE: The translation of recursive types ignores lifetime parameters for now
instance RsConvert w (Item Span) (SomePartialNamedShape w) where
  rsConvert w s@(StructItem _ _ ident vd generics@(Generics _ tys _ _) _)
    | isRecursiveDef s =
      do Some ctx <- rsConvert w generics
         let ctx' = rustCtxCons ctx (name ident) (LLVMShapeRepr $ natRepr w)
             tyIdents = (\(TyParam _ i _ _ _) -> [i]) <$> tys
         sh <- inRustCtxF ctx' $ \(_ :>: rec_n) -> withRecType (RustName [ident]) (RustName <$> tyIdents) rec_n $ rsConvert w vd
         return $ RecShape (name ident) (rustCtxCtx ctx) sh
    | otherwise =
      do Some ctx <- rsConvert w generics
         sh <- inRustCtx ctx $ rsConvert w vd
         return $ NonRecShape (name ident) (rustCtxCtx ctx) sh
  rsConvert w e@(Enum _ _ ident variants generics@(Generics _ tys _ _) _)
    | isRecursiveDef e =
      do Some ctx <- rsConvert w generics
         let ctx' = rustCtxCons ctx (name ident) (LLVMShapeRepr $ natRepr w)
             tyIdents = (\(TyParam _ i _ _ _) -> [i]) <$> tys
         sh <- inRustCtxF ctx' $ \(_ :>: rec_n) -> withRecType (RustName [ident]) (RustName <$> tyIdents) rec_n $ rsConvert w variants
         return $ RecShape (name ident) (rustCtxCtx ctx) sh
    | otherwise =
      do Some ctx <- rsConvert w generics
         sh <- inRustCtx ctx $ rsConvert w variants
         return $ NonRecShape (name ident) (rustCtxCtx ctx) sh
  rsConvert _ item = fail ("Top-level item not supported: " ++ show item)

instance RsConvert w [Variant Span] (PermExpr (LLVMShapeType w)) where
  rsConvert _ [] = fail "Uninhabited types not supported"
  rsConvert w variants =
    do vshs <- mapM (rsConvert w) variants
       return $ foldr1 PExpr_OrShape (zipWith PExpr_SeqShape tags vshs)
    where
      buildTagShape =
        PExpr_FieldShape . LLVMFieldShape . ValPerm_Eq . PExpr_LLVMWord . bvIntOfSize w

      tags = map buildTagShape [0..]

instance RsConvert w (Variant Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (Variant _ _ vd _ _) = rsConvert w vd

instance RsConvert w (VariantData Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (StructD sfs _) =
    do shs <- mapM (rsConvert w) sfs
       return $ foldr PExpr_SeqShape PExpr_EmptyShape shs
  rsConvert w (TupleD sfs _) =
    do shs <- mapM (rsConvert w) sfs
       return $ foldr PExpr_SeqShape PExpr_EmptyShape shs
  rsConvert _ (UnitD _) = return PExpr_EmptyShape

instance RsConvert w (StructField Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (StructField _ _ t _ _) = rsConvert w t

----------------------------------------------------------------------
-- * Computing the ABI-Specific Layout of Rust Types
----------------------------------------------------------------------

-- | Build an 'ArgLayoutPerm' that just assigns @true@ to every field
trueArgLayoutPerm :: Assignment prx ctx -> ArgLayoutPerm ctx
trueArgLayoutPerm ctx = ALPerm (RL.map (const ValPerm_True) $ assignToRList ctx)

-- | Build an 'ArgLayoutPerm' for 0 fields
argLayoutPerm0 :: ArgLayoutPerm EmptyCtx
argLayoutPerm0 = ALPerm MNil

-- | Build an 'ArgLayoutPerm' for a single field
argLayoutPerm1 :: ValuePerm a -> ArgLayoutPerm (EmptyCtx '::> a)
argLayoutPerm1 p = ALPerm (MNil :>: p)

-- | Convert an 'ArgLayoutPerm' to a permission on a struct
argLayoutPermToPerm :: ArgLayoutPerm ctx -> ValuePerm (StructType ctx)
argLayoutPermToPerm (ALPerm ps) = ValPerm_Conj1 $ Perm_Struct ps
argLayoutPermToPerm (ALPerm_Or p1 p2) =
  ValPerm_Or (argLayoutPermToPerm p1) (argLayoutPermToPerm p2)
argLayoutPermToPerm (ALPerm_Exists mb_p) =
  ValPerm_Exists $ fmap argLayoutPermToPerm mb_p

-- | Convert an 'ArgLayoutPerm' on a single field to a permission on single
-- values of the type of that field
argLayoutPerm1ToPerm :: ArgLayoutPerm (EmptyCtx '::> a) -> ValuePerm a
argLayoutPerm1ToPerm (ALPerm (_ :>: p)) = p
argLayoutPerm1ToPerm (ALPerm_Or p1 p2) =
  ValPerm_Or (argLayoutPerm1ToPerm p1) (argLayoutPerm1ToPerm p2)
argLayoutPerm1ToPerm (ALPerm_Exists mb_p) =
  ValPerm_Exists $ fmap argLayoutPerm1ToPerm mb_p

-- | Append the field types @ctx1@ and @ctx2@ of two 'ArgLayoutPerm's to get a
-- combined 'ArgLayoutPerm' over the combined fields
appendArgLayoutPerms :: Assignment prx1 ctx1 -> Assignment prx2 ctx2 ->
                        ArgLayoutPerm ctx1 -> ArgLayoutPerm ctx2 ->
                        ArgLayoutPerm (ctx1 <+> ctx2)
appendArgLayoutPerms ctx1 ctx2 (ALPerm_Or p1 p2) q =
  ALPerm_Or (appendArgLayoutPerms ctx1 ctx2 p1 q)
  (appendArgLayoutPerms ctx1 ctx2 p2 q)
appendArgLayoutPerms ctx1 ctx2 p (ALPerm_Or q1 q2) =
  ALPerm_Or (appendArgLayoutPerms ctx1 ctx2 p q1)
  (appendArgLayoutPerms ctx1 ctx2 p q2)
appendArgLayoutPerms ctx1 ctx2 (ALPerm_Exists mb_p) q =
  ALPerm_Exists $ fmap (\p -> appendArgLayoutPerms ctx1 ctx2 p q) mb_p
appendArgLayoutPerms ctx1 ctx2 p (ALPerm_Exists mb_q) =
  ALPerm_Exists $ fmap (\q -> appendArgLayoutPerms ctx1 ctx2 p q) mb_q
appendArgLayoutPerms ctx1 ctx2 (ALPerm ps) (ALPerm qs) =
  ALPerm $ assignToRListAppend ctx1 ctx2 ps qs

-- | Count the number of fields of an 'ArgLayout'
argLayoutNumFields :: ArgLayout -> Int
argLayoutNumFields (ArgLayout ctx _) = sizeInt $ size ctx

-- | Construct an 'ArgLayout' for 0 arguments
argLayout0 :: ArgLayout
argLayout0 = ArgLayout Ctx.empty (ALPerm MNil)

-- | Construct an 'ArgLayout' for a single argument
argLayout1 :: KnownRepr TypeRepr a => ValuePerm a -> ArgLayout
argLayout1 p = ArgLayout (extend Ctx.empty knownRepr) (ALPerm (MNil :>: p))

-- | Append two 'ArgLayout's, if possible
appendArgLayout :: ArgLayout -> ArgLayout -> ArgLayout
appendArgLayout (ArgLayout ctx1 p1) (ArgLayout ctx2 p2) =
  ArgLayout (ctx1 Ctx.<++> ctx2) (appendArgLayoutPerms ctx1 ctx2 p1 p2)

-- | Test if @ctx2@ is an extension of @ctx1@
ctxIsAppend :: CtxRepr ctx1 -> CtxRepr ctx2 ->
               Maybe (IsAppend ctx1 ctx2)
ctxIsAppend ctx1 ctx2
  | Just Refl <- testEquality ctx1 ctx2
  = Just $ IsAppend zeroSize
ctxIsAppend ctx1 (ctx2' Ctx.:> _)
  | Just (IsAppend sz) <- ctxIsAppend ctx1 ctx2'
  = Just (IsAppend (incSize sz))
ctxIsAppend _ _ = Nothing

-- | Take the disjunction of two 'ArgLayout's, if possible
disjoinArgLayouts :: ArgLayout -> ArgLayout -> Maybe ArgLayout
disjoinArgLayouts (ArgLayout ctx1 p1) (ArgLayout ctx2 p2)
  | Just (IsAppend sz') <- ctxIsAppend ctx1 ctx2 =
    let ps' = generate sz' (const ValPerm_True) in
    Just $ ArgLayout ctx2 $
    ALPerm_Or
    (appendArgLayoutPerms ctx1 ps' p1 (ALPerm $ assignToRList ps'))
    p2
disjoinArgLayouts (ArgLayout ctx1 p1) (ArgLayout ctx2 p2)
  | Just (IsAppend sz') <- ctxIsAppend ctx2 ctx1 =
    let ps' = generate sz' (const ValPerm_True) in
    Just $ ArgLayout ctx1 $
    ALPerm_Or
    p1
    (appendArgLayoutPerms ctx2 ps' p2 (ALPerm $ assignToRList ps'))
disjoinArgLayouts _ _ = Nothing

-- | Make an existential 'ArgLayout'
existsArgLayout :: KnownRepr TypeRepr a => Binding a ArgLayout -> ArgLayout
existsArgLayout [nuP| ArgLayout mb_ctx mb_p |] =
  ArgLayout (mbLift mb_ctx) (ALPerm_Exists mb_p)

{-
-- | Convert an 'ArgLayout' to a permission on a @struct@ of its arguments
argLayoutStructPerm :: ArgLayout -> Some (Typed ValuePerm)
argLayoutStructPerm (ArgLayout ghosts (MNil :>: KnownReprObj) mb_perms) =
  Some $ Typed knownRepr $
  valPermExistsMulti ghosts $ fmap (\(_ :>: perm) -> perm) mb_perms
argLayoutStructPerm (ArgLayout ghosts args mb_perms)
  | args_repr <- cruCtxToRepr (knownCtxToCruCtx args)
  , Refl <- cruCtxToReprEq (knownCtxToCruCtx args) =
    Some $ Typed (StructRepr args_repr) $
    valPermExistsMulti ghosts $ fmap (ValPerm_Conj1 . Perm_Struct) mb_perms
-}

-- | Append two 'ArgLayoutIO's, if possible
appendArgLayoutIO :: ArgLayoutIO -> ArgLayoutIO -> ArgLayoutIO
appendArgLayoutIO (ArgLayoutIO ctx1 p1 ps1) (ArgLayoutIO ctx2 p2 ps2) =
  ArgLayoutIO (ctx1 Ctx.<++> ctx2) (appendArgLayoutPerms ctx1 ctx2 p1 p2)
  (assignToRListAppend ctx1 ctx2 ps1 ps2)

-- | Convert an 'ArgLayout' to an 'ArgLayoutIO' by adding @true@ output perms
argLayoutAddTrueOuts :: ArgLayout -> ArgLayoutIO
argLayoutAddTrueOuts (ArgLayout ctx p) =
  ArgLayoutIO ctx p $ trueValuePerms $ assignToRList ctx

-- | Construct an 'ArgLayoutIO' for 0 arguments
argLayoutIO0 :: ArgLayoutIO
argLayoutIO0 = ArgLayoutIO Ctx.empty (ALPerm MNil) MNil

-- | Create an 'ArgLayoutIO' from a single input and output perm
argLayoutIO1 :: KnownRepr TypeRepr a => ValuePerm a -> ValuePerm a ->
                ArgLayoutIO
argLayoutIO1 p_in p_out =
  ArgLayoutIO (extend Ctx.empty knownRepr) (ALPerm
                                            (MNil :>: p_in)) (MNil :>: p_out)

-- | Convert a shape to a writeable block permission with that shape, or fail if
-- the length of the shape is not defined
--
-- FIXME: maybe this goes in the 'Permissions' module?
shapeToBlock :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                Maybe (LLVMBlockPerm w)
shapeToBlock sh
  | Just len <- llvmShapeLength sh =
    Just $ LLVMBlockPerm
    { llvmBlockRW = PExpr_Write, llvmBlockLifetime = PExpr_Always,
      llvmBlockOffset = bvInt 0, llvmBlockLen = len, llvmBlockShape = sh }
shapeToBlock _ = Nothing

-- | Convert a shape to a writeable @memblock@ permission with that shape, or
-- fail if the length of the shape is not defined
--
-- FIXME: maybe this goes in the 'Permissions' module?
shapeToBlockPerm :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                    Maybe (ValuePerm (LLVMPointerType w))
shapeToBlockPerm = fmap ValPerm_LLVMBlock . shapeToBlock

instance PermPretty Some3FunPerm where
  permPrettyM (Some3FunPerm fun_perm) = permPrettyM fun_perm

-- | Try to convert a 'Some3FunPerm' to a 'SomeFunPerm' at a specific type
un3SomeFunPerm :: (Fail.MonadFail m) => CruCtx args -> TypeRepr ret -> Some3FunPerm ->
                  m (SomeFunPerm args ret)
un3SomeFunPerm args ret (Some3FunPerm fun_perm)
  | Just Refl <- testEquality args (funPermArgs fun_perm)
  , Just Refl <- testEquality ret (funPermRet fun_perm) =
    return $ SomeFunPerm fun_perm
un3SomeFunPerm args ret (Some3FunPerm fun_perm) =
  let ppInfo = emptyPPInfo in
    fail $ renderDoc $ vsep
    [ pretty "Unexpected LLVM type for function permission:"
    , permPretty ppInfo fun_perm
    , pretty "Actual LLVM type of function:"
      <+> PP.group (permPretty ppInfo args) <+> pretty "=>"
      <+> PP.group (permPretty ppInfo ret)
    , pretty "Expected LLVM type of function:"
      <+> PP.group (permPretty ppInfo (funPermArgs fun_perm))
      <+> pretty "=>"
      <+> PP.group (permPretty ppInfo (funPermRet fun_perm)) ]

-- | This is the more general form of 'funPerm3FromArgLayout, where there can be
-- ghost variables in the 'ArgLayout'
funPerm3FromMbArgLayout :: CtxRepr ctx ->
                           MatchedMb ghosts (ArgLayoutPerm ctx) ->
                           ValuePerms (CtxToRList ctx) ->
                           CruCtx ghosts -> CtxRepr args ->
                           ValuePerms (CtxToRList args) ->
                           ValuePerms (CtxToRList args) ->
                           TypeRepr ret -> ValuePerm ret ->
                           RustConvM Some3FunPerm

-- Special case: if the argument perms are just a sequence of permissions on the
-- individual arguments, make a function perm with those argument perms, that
-- is, we build the function permission
--
-- (ghosts). arg1:p1, ..., argn:pn -o ret:ret_perm
funPerm3FromMbArgLayout ctx [nuMP| ALPerm mb_ps_in |] ps_out
                        ghosts ctx1 ps1_in ps1_out ret_tp ret_perm
  | ctx_args <- mkCruCtx (ctx1 Ctx.<++> ctx)
  , ctx_all <- appendCruCtx ghosts ctx_args
  , ghost_perms <- trueValuePerms $ cruCtxProxies ghosts
  , mb_ps_in_all <-
      mbCombine (cruCtxProxies ctx_args) $
      fmap (\ps_in ->
             nuMulti (cruCtxProxies ctx_args) $ const $
             RL.append ghost_perms
             (assignToRListAppend ctx1 ctx ps1_in ps_in)) mb_ps_in
  , ps_out_all <-
      RL.append ghost_perms (assignToRListAppend
                             ctx1 ctx ps1_out ps_out) :>: ret_perm =
    return $ Some3FunPerm $
    FunPerm ghosts ctx_args CruCtxNil ret_tp mb_ps_in_all
    (nuMulti (cruCtxProxies ctx_all :>: Proxy) $ \_ -> ps_out_all)
funPerm3FromMbArgLayout ctx [nuMP| ALPerm_Exists mb_p |] ps_out
                            ghosts ctx1 ps1_in ps1_out ret_tp ret_perm =
  funPerm3FromMbArgLayout ctx (mbMatch $ mbCombine (MNil :>: Proxy) mb_p) ps_out
  (CruCtxCons ghosts knownRepr) ctx1 ps1_in ps1_out ret_tp ret_perm
funPerm3FromMbArgLayout _ctx [nuMP| ALPerm_Or _ _ |] _ps_out
                        _ghosts _ctx1 _ps1_in _ps1_out _ret_tp _ret_perm =
  fail "Cannot (yet) handle Rust enums or other disjunctive types in functions"


-- | Build a function permission from an 'ArgLayoutIO' that describes the
-- arguments and their input and output permissions and a return permission that
-- describes the output permissions on the return value. The caller also
-- specifies additional arguments to be prepended to the argument list that do
-- have output permissions as a struct of 0 or more fields along with input and
-- output permissions on those arguments.
funPerm3FromArgLayout :: ArgLayoutIO -> CtxRepr args ->
                         ValuePerms (CtxToRList args) ->
                         ValuePerms (CtxToRList args) ->
                         TypeRepr ret -> ValuePerm ret ->
                         RustConvM Some3FunPerm
funPerm3FromArgLayout (ArgLayoutIO
                       ctx p_in ps_out) ctx1 ps1_in ps1_out ret_tp ret_perm =
  funPerm3FromMbArgLayout ctx (mbMatch $ emptyMb p_in) ps_out CruCtxNil
  ctx1 ps1_in ps1_out ret_tp ret_perm

-- | Like 'funPerm3FromArgLayout' but with no additional arguments
funPerm3FromArgLayoutNoArgs :: ArgLayoutIO -> TypeRepr ret -> ValuePerm ret ->
                               RustConvM Some3FunPerm
funPerm3FromArgLayoutNoArgs layout ret ret_perm =
  funPerm3FromArgLayout layout Ctx.empty MNil MNil ret ret_perm


-- | Add ghost variables with the supplied permissions for the bound names in a
-- 'FunPerm' in a binding
mbGhostsFunPerm ::
  CruCtx new_ghosts ->
  Mb ((new_ghosts :++: ghosts) :++: args) (ValuePerms new_ghosts) ->
  Mb new_ghosts (FunPerm ghosts args gouts ret) ->
  FunPerm (new_ghosts :++: ghosts) args gouts ret
mbGhostsFunPerm new_ghosts mb_new_ps (mbMatch ->
                                      [nuMP| FunPerm ghosts args
                                           gouts ret ps_in ps_out |]) =
  let new_prxs = cruCtxProxies new_ghosts
      ghosts_prxs = cruCtxProxies $ mbLift ghosts
      rets_prxs = cruCtxProxies (mbLift gouts) :>: Proxy
      args_prxs = cruCtxProxies $ mbLift args in
  FunPerm (appendCruCtx new_ghosts $ mbLift ghosts)
  (mbLift args) (mbLift gouts) (mbLift ret)
  (mbMap2 (\new_ps ps -> assocAppend new_ps ghosts_prxs args_prxs ps) mb_new_ps $
   mbAssoc new_prxs ghosts_prxs args_prxs $
   mbCombine (RL.append ghosts_prxs args_prxs) ps_in)
  (mbAssoc4 new_prxs ghosts_prxs args_prxs rets_prxs $
   fmap (assocAppend4 (RL.map (const ValPerm_True) new_prxs)
         ghosts_prxs args_prxs rets_prxs) $
         mbCombine (RL.append
                    (RL.append ghosts_prxs args_prxs) rets_prxs) ps_out)

-- | Add ghost variables with no permissions for the bound names in a
-- 'Some3FunPerm' in a binding
mbGhostsFunPerm3 :: CruCtx new_ghosts -> Mb new_ghosts Some3FunPerm ->
                    Some3FunPerm
mbGhostsFunPerm3 new_ghosts (mbMatch -> [nuMP| Some3FunPerm fun_perm |]) =
  let new_ps =
        nuMulti (cruCtxProxies
                 ((new_ghosts
                   `appendCruCtx` mbLift (fmap funPermGhosts fun_perm))
                  `appendCruCtx` mbLift (fmap funPermArgs fun_perm))) $
        const $ RL.map (const ValPerm_True) (cruCtxProxies new_ghosts) in
  Some3FunPerm $ mbGhostsFunPerm new_ghosts new_ps fun_perm


-- | Try to compute the layout of a structure of the given shape as a value,
-- over 1 or more registers, if this is possible
layoutArgShapeByVal :: (1 <= w, KnownNat w) => Abi ->
                       PermExpr (LLVMShapeType w) ->
                       MaybeT RustConvM ArgLayout

-- The empty shape --> no values
layoutArgShapeByVal Rust PExpr_EmptyShape = return argLayout0

-- Named shapes that unfold --> layout their unfoldings
layoutArgShapeByVal Rust (PExpr_NamedShape rw l nmsh args)
  | TrueRepr <- namedShapeCanUnfoldRepr nmsh
  , Just sh' <- unfoldModalizeNamedShape rw l nmsh args =
    layoutArgShapeByVal Rust sh'

-- Opaque named shapes that are bigger than 16 bytes --> not laid out by value
--
-- FIXME: if an opaque named shape somehow corresponds to > 2 fields, it is also
-- not laid out by value
layoutArgShapeByVal Rust sh@(PExpr_NamedShape _ _ nmsh _)
  | not (namedShapeCanUnfold nmsh)
  , Just len <- llvmShapeLength sh
  , bvLt (bvInt 16) len =
    mzero

-- Opaque named shapes that could potentially be laid out by value are an error,
-- because we do not know their representation
layoutArgShapeByVal Rust (PExpr_NamedShape _ _ nmsh _)
  | not (namedShapeCanUnfold nmsh) =
    lift $ fail $ renderDoc
    (pretty "layoutArgShapeByVal: Cannot lay out opaque named shape by value:"
     <+> pretty (namedShapeName nmsh))

-- The ptr shape --> a single pointer value, if we know its length
layoutArgShapeByVal Rust (PExpr_PtrShape maybe_rw maybe_l sh)
  | Just bp <- llvmBlockAdjustModalities maybe_rw maybe_l <$> shapeToBlock sh =
    return $ argLayout1 $ ValPerm_LLVMBlock bp

-- If we don't know the length of our pointer, we can't lay it out at all
layoutArgShapeByVal Rust (PExpr_PtrShape _ _ sh) =
  lift rsPPInfo >>= \ppInfo ->
  lift $ fail $ renderDoc $ fillSep
  [pretty "layoutArgShapeByVal: Shape with unknown length:",
   permPretty ppInfo sh]

-- A field shape --> the contents of the field
layoutArgShapeByVal Rust (PExpr_FieldShape (LLVMFieldShape p)) =
  return $ argLayout1 p

-- Array shapes have unknown length, and so are never passed by value
layoutArgShapeByVal Rust (PExpr_ArrayShape _ _ _) = mzero

-- Sequence shapes are only laid out as values in the Rust ABI if the result has
-- at most two fields
layoutArgShapeByVal Rust (PExpr_SeqShape sh1 sh2) =
  do layout1 <- layoutArgShapeByVal Rust sh1
     layout2 <- layoutArgShapeByVal Rust sh2
     let layout = appendArgLayout layout1 layout2
     if argLayoutNumFields layout <= 2 then return layout else mzero

-- Disjunctive shapes are only laid out as values in the Rust ABI if both sides
-- can be laid out as values that we can coerce to have the same number of type
-- of fields.
--
-- FIXME: The check for whether we can do this coercion is currently done by
-- disjoinArgLayouts, but it is probably ABI-specific, so should be performed by
-- a function that knows how to join two lists of field types depending on the
-- ABI
layoutArgShapeByVal Rust (PExpr_OrShape sh1 sh2) =
  do layout1 <- layoutArgShapeByVal Rust sh1
     layout2 <- layoutArgShapeByVal Rust sh2
     case disjoinArgLayouts layout1 layout2 of
       Just layout -> return layout
       Nothing -> mzero

-- For existential shapes, just add the existential variable to the ghosts
layoutArgShapeByVal Rust (PExpr_ExShape mb_sh) =
  existsArgLayout <$> mbM (fmap (layoutArgShapeByVal Rust) mb_sh)

-- False shape is like the empty shape --> no values
layoutArgShapeByVal Rust PExpr_FalseShape = return argLayout0

layoutArgShapeByVal Rust sh =
  lift rsPPInfo >>= \ppInfo ->
  lift $ fail $ renderDoc $ fillSep
  [pretty "layoutArgShapeByVal: Unsupported shape:", permPretty ppInfo sh]
layoutArgShapeByVal abi _ =
  lift $ fail ("layoutArgShapeByVal: Unsupported ABI: " ++ show abi)


-- | Try to compute the layout of a structure of the given shape as a value,
-- over 1 or more registers, if this is possible. Otherwise convert the shape to
-- an LLVM block permission.
layoutArgShapeOrBlock :: (1 <= w, KnownNat w) => Abi ->
                         PermExpr (LLVMShapeType w) ->
                         RustConvM (Either (LLVMBlockPerm w) ArgLayout)
layoutArgShapeOrBlock abi sh =
  runMaybeT (layoutArgShapeByVal abi sh) >>= \case
  Just layout -> return $ Right layout
  Nothing | Just bp <- shapeToBlock sh -> return $ Left bp
  _ ->
    rsPPInfo >>= \ppInfo ->
    fail $ renderDoc $ fillSep
    [pretty "layoutArgShapeOrBlock: Could not layout shape with unknown size:",
     permPretty ppInfo sh]

-- | Compute the layout of an argument with the given shape as 1 or more
-- register arguments of a function. If the argument is laid out as a value,
-- then it has no output permissions, but if it is laid out as a pointer, the
-- memory occupied by that pointer is returned with an empty shape.
layoutArgShape :: (1 <= w, KnownNat w) => Abi ->
                  PermExpr (LLVMShapeType w) -> RustConvM ArgLayoutIO
layoutArgShape abi sh =
  layoutArgShapeOrBlock abi sh >>= \case
  Right layout -> return $ argLayoutAddTrueOuts layout
  Left bp ->
    return (argLayoutIO1 (ValPerm_LLVMBlock bp)
            (ValPerm_LLVMBlock $ bp { llvmBlockShape = PExpr_EmptyShape }))

-- | Compute the layout for the inputs and outputs of a function with the given
-- shapes as arguments and return value as a function permission
layoutFun :: (1 <= w, KnownNat w) => Abi ->
             [PermExpr (LLVMShapeType w)] -> PermExpr (LLVMShapeType w) ->
             RustConvM Some3FunPerm
layoutFun abi arg_shs ret_sh =
  do args_layout <-
       foldr appendArgLayoutIO argLayoutIO0 <$> mapM (layoutArgShape abi) arg_shs
     ret_layout_eith <- layoutArgShapeOrBlock abi ret_sh
     case ret_layout_eith of

       -- Special case: if the return type is empty, use the unit type as the
       -- return type
       Right (ArgLayout Ctx.Empty _) ->
         funPerm3FromArgLayoutNoArgs args_layout UnitRepr ValPerm_True

       -- Special case: if the return type is a single field, remove the struct
       -- type and just use the type of that single field
       Right (ArgLayout (Ctx.Empty Ctx.:> ret_tp)
              (argLayoutPerm1ToPerm -> ret_p)) ->
         funPerm3FromArgLayoutNoArgs args_layout ret_tp ret_p

       -- If the return type can be laid out as a struct type, then do so
       Right (ArgLayout ret_ctx ret_p) ->
         funPerm3FromArgLayoutNoArgs args_layout (StructRepr ret_ctx)
         (argLayoutPermToPerm ret_p)

       -- Otherwise add an extra pointer argument used as an out variable
       Left bp ->
           funPerm3FromArgLayout args_layout
           (extend Ctx.empty knownRepr)
           (MNil :>: ValPerm_LLVMBlock (bp { llvmBlockShape =
                                               PExpr_EmptyShape}))
           (MNil :>: ValPerm_LLVMBlock bp)
           UnitRepr ValPerm_True


----------------------------------------------------------------------
-- * Converting Function Types
----------------------------------------------------------------------

-- | An 'ExprPerms' with types for the expressions
data TypedExprPerms ctx = TypedExprPerms (CruCtx ctx) (ExprPerms ctx)

-- | Convert a 'TypedDistPerms' to a 'TypedExprPerms'
typedDistToExprPerms :: TypedDistPerms ctx -> TypedExprPerms ctx
typedDistToExprPerms perms =
  TypedExprPerms (typedDistPermsCtx perms) (distPermsToExprPerms $
                                            unTypeDistPerms perms)

-- | Find all portions of an atomic permission containing a lifetime, returning
-- 'Nothing' if it does not contain the lifetime
atomicPermForLifetime :: ExprVar LifetimeType -> AtomicPerm a ->
                         Maybe (AtomicPerm a)
atomicPermForLifetime l p | not $ NameSet.member l $ freeVars p = Nothing
atomicPermForLifetime l (Perm_Struct ps) =
  Just $ Perm_Struct $
  RL.map (\p -> fromMaybe ValPerm_True (permForLifetime l p)) ps
atomicPermForLifetime _ p = Just p

-- | Find all portions of a permission containing a lifetime, returning
-- 'Nothing' if it does not contain the lifetime
permForLifetime :: ExprVar LifetimeType -> ValuePerm a -> Maybe (ValuePerm a)
permForLifetime l p | not $ NameSet.member l $ freeVars p = Nothing
permForLifetime l (ValPerm_Conj ps) =
  Just $ ValPerm_Conj $ mapMaybe (atomicPermForLifetime l) ps
permForLifetime _ p = Just p

-- | Find all permissions containing lifetime @l@ and return just those portions
-- of the these permissions that contain @l@
lownedPermsForLifetime :: CruCtx ctx -> ExprVar LifetimeType -> DistPerms ctx ->
                          Some TypedExprPerms
lownedPermsForLifetime tps l ps =
  fmapF typedDistToExprPerms $ concatSomeRAssign $
  RL.mapToList (\case
                   (Typed tp (VarAndPerm x p))
                     | Just p' <- permForLifetime l p ->
                       Some (MNil :>: Typed tp (VarAndPerm x p'))
                   _ -> Some MNil)
  (RL.map2 Typed (cruCtxToTypes tps) ps)

-- | Get the 'String' name defined by a 'LifetimeDef'
lifetimeDefName :: LifetimeDef a -> String
lifetimeDefName (LifetimeDef _ (Lifetime name _) _ _) = name

-- | Get the 'String' name defined by a 'TyParam'
tyParamName :: TyParam a -> String
tyParamName (TyParam _ ident _ _ _) = name ident

extMbOuter :: RAssign Proxy ctx1 -> Mb ctx2 a -> Mb (ctx1 :++: ctx2) a
extMbOuter prxs mb_a = mbCombine (mbToProxy mb_a) $ nuMulti prxs $ const mb_a

extMbAppInner :: NuMatching a => any ctx1 ->
                 RAssign Proxy ctx2 -> RAssign Proxy ctx3 ->
                 Mb (ctx1 :++: ctx2) a -> Mb (ctx1 :++: ctx2 :++: ctx3) a
extMbAppInner (_ :: any ctx1) ctx2 ctx3 mb_a =
  mbCombine (RL.append ctx2 ctx3) $
  mbMapCl ($(mkClosed [| extMbMulti |]) `clApply` toClosed ctx3) $
  mbSeparate @_ @ctx1 ctx2 mb_a

-- | Add a lifetime described by a 'LifetimeDef' to a 'Some3FunPerm'
mbLifetimeFunPerm :: LifetimeDef Span -> Binding LifetimeType Some3FunPerm ->
                     RustConvM Some3FunPerm
mbLifetimeFunPerm (LifetimeDef _ _ [] _)
                  (mbMatch -> [nuMP| Some3FunPerm fun_perm |]) =
  do let ghosts = mbLift $ fmap funPermGhosts fun_perm
     let ghosts_prxs = cruCtxProxies ghosts
     let gouts = mbLift $ fmap funPermGouts fun_perm
     let rets_prxs = cruCtxProxies gouts :>: Proxy
     let args = mbLift $ fmap funPermArgs fun_perm
     let args_prxs = cruCtxProxies args
     let ret = mbLift $ fmap funPermRet fun_perm
     let l_prxs = MNil :>: (Proxy :: Proxy LifetimeType)
     let fp_outs = mbLift $ fmap funPermOutCtx fun_perm
     let mb_ps_in =
           mbCombineAssoc l_prxs ghosts_prxs args_prxs $
           fmap (mbValuePermsToDistPerms . funPermIns) fun_perm
     let mb_ps_out =
           mbCombineAssoc4 l_prxs ghosts_prxs args_prxs rets_prxs $
           fmap (mbValuePermsToDistPerms . funPermOuts) fun_perm
     let mb_l = extMbMulti args_prxs $ extMbMulti ghosts_prxs $ nu id
     let mb_l_out =
           extMbMulti rets_prxs $ extMbMulti args_prxs $
           extMbMulti ghosts_prxs $ nu id
     [nuMP| Some (TypedExprPerms mb_tps_in mb_lops_in) |] <-
       return $ mbMatch $ mbMap2 (lownedPermsForLifetime
                                  (appendCruCtx ghosts args)) mb_l mb_ps_in
     [nuMP| Some (TypedExprPerms mb_tps_out mb_lops_out) |] <-
       return $ mbMatch $
       mbMap2 (lownedPermsForLifetime fp_outs) mb_l_out mb_ps_out
     let tps_in = mbLift mb_tps_in
     let tps_out = mbLift mb_tps_out
     case abstractModalities mb_lops_in of
       SomeTypedMb ghosts' mb_mb_lops_in_abs ->
         return $ mbGhostsFunPerm3 ghosts' $
         flip fmap mb_mb_lops_in_abs $ \mb_lops_in_abs ->
         Some3FunPerm $
         FunPerm (appendCruCtx
                  (singletonCruCtx LifetimeRepr) ghosts) args gouts ret
         (mbMap2 (\ps_in lops_in_abs ->
                   assocAppend (MNil :>: ValPerm_LOwnedSimple tps_in lops_in_abs)
                   ghosts args_prxs $ distPermsToValuePerms ps_in)
          mb_ps_in mb_lops_in_abs)
         (mbMap3 (\ps_out lops_out lops_in_abs ->
                   let (ps_ghosts, ps_args, ps_rets) =
                         rlSplit3 ghosts_prxs args_prxs rets_prxs $
                         distPermsToValuePerms ps_out in
                   (((MNil :>: ValPerm_LOwned [] tps_out tps_in lops_out lops_in_abs)
                     `RL.append` ps_ghosts) `RL.append` ps_args)
                   `RL.append` ps_rets)
          mb_ps_out mb_lops_out (extMbMulti rets_prxs mb_lops_in_abs))
mbLifetimeFunPerm (LifetimeDef _ _ _bounds _) _ =
  fail "Rust lifetime bounds not yet supported!"

-- | Run a computation of a function permission in the context of a list of
-- Rust lifetime definitions
withLifetimes :: [LifetimeDef Span] -> RustConvM Some3FunPerm ->
                 RustConvM Some3FunPerm
withLifetimes [] m = m
withLifetimes (ldef : ldefs) m =
  inRustCtx (rustCtx1 (lifetimeDefName ldef)
             LifetimeRepr) (withLifetimes ldefs m) >>=
  mbLifetimeFunPerm ldef

-- | An object of type @a@ inside some name-binding context where each bound
-- name is assigned its own permission
data SomeMbWithPerms a where
  SomeMbWithPerms :: CruCtx ctx -> MbValuePerms ctx -> Mb ctx a ->
                     SomeMbWithPerms a

instance Functor SomeMbWithPerms where
  fmap f (SomeMbWithPerms ctx ps mb_a) = SomeMbWithPerms ctx ps (fmap f mb_a)

instance App.Applicative SomeMbWithPerms where
  pure a = SomeMbWithPerms CruCtxNil (emptyMb MNil) $ emptyMb a
  liftA2 f (SomeMbWithPerms ctx1 mb_ps1 mb_a1) (SomeMbWithPerms ctx2 mb_ps2 mb_a2) =
    SomeMbWithPerms (appendCruCtx ctx1 ctx2)
    (mbCombine (cruCtxProxies ctx2) $ flip fmap mb_ps1 $ \ps1 ->
      flip fmap mb_ps2 $ \ps2 -> RL.append ps1 ps2)
    (mbCombine (cruCtxProxies ctx2) $
     flip fmap mb_a1 $ \a1 -> flip fmap mb_a2 $ \a2 -> f a1 a2)

-- NOTE: the Monad instance fails here because it requires the output type of f
-- to satisfy NuMatching. That is, it is a \"restricted monad\", that is only a
-- monad over types that satisfy the NuMatching restriction. Thus we define
-- bindSomeMbWithPerms to add this restriction.
{-
instance Monad SomeMbWithPerms where
  return = pure
  (SomeMbWithPerms ctx1 mb_ps1 mb_a) >>= f =
    case mbMatch (fmap f mb_a) of
      [nuMP| SomeMbWithPerms ctx2 mb_mb_ps2 mb_mb_b |] ->
        let ctx2_prxs = cruCtxProxies $ mbLift ctx2 in
        SomeMbWithPerms (appendCruCtx ctx1 $ mbLift ctx2)
        (mbCombine ctx2_prxs $
         mbMap2 (\ps1 mb_ps2 -> fmap (RL.append ps1) mb_ps2) mb_ps1 mb_mb_ps2)
        (mbCombine ctx2_prxs mb_mb_b)
-}

-- | A monadic bind for 'SomeMbWithPerms', which requires a 'NuMatching'
-- instance for the output type
bindSomeMbWithPerms :: NuMatching b => SomeMbWithPerms a ->
                       (a -> SomeMbWithPerms b) -> SomeMbWithPerms b
bindSomeMbWithPerms (SomeMbWithPerms ctx1 mb_ps1 mb_a) f =
  case mbMatch (fmap f mb_a) of
    [nuMP| SomeMbWithPerms ctx2 mb_mb_ps2 mb_mb_b |] ->
      let ctx2_prxs = cruCtxProxies $ mbLift ctx2 in
      SomeMbWithPerms (appendCruCtx ctx1 $ mbLift ctx2)
      (mbCombine ctx2_prxs $
       mbMap2 (\ps1 mb_ps2 -> fmap (RL.append ps1) mb_ps2) mb_ps1 mb_mb_ps2)
      (mbCombine ctx2_prxs mb_mb_b)

-- | Make a 'SomeMbWithPerms' with a single bound variable
someMbWithPermsVar1 :: TypeRepr a -> ValuePerm a -> SomeMbWithPerms (ExprVar a)
someMbWithPermsVar1 tp p =
  SomeMbWithPerms (singletonCruCtx tp) (nu $ const (MNil :>: p)) (nu id)

-- | Move a 'SomeMbWithPerms' out of a binding by adding the bound variables as
-- variables that are bound with @true@ permissions by the 'SomeMbWithPerms'
mbSomeMbWithPerms :: NuMatching a => CruCtx ctx -> Mb ctx (SomeMbWithPerms a) ->
                     SomeMbWithPerms a
mbSomeMbWithPerms ctx (mbMatch -> [nuMP| SomeMbWithPerms ctx' mb_ps' mb_a |]) =
  let ctx'_prxs = cruCtxProxies $ mbLift ctx' in
  SomeMbWithPerms (appendCruCtx ctx $ mbLift ctx')
  (fmap (RL.append $ trueValuePerms (cruCtxProxies ctx)) $
   mbCombine ctx'_prxs mb_ps')
  (mbCombine ctx'_prxs mb_a)

-- | Add additional gnost output variables to a 'FunPerm'
mbGoutsFunPerm ::
  out_ctx ~ ((ghosts :++: args) :++: gouts :> ret) =>
  CruCtx ghosts -> CruCtx args -> CruCtx gouts -> TypeRepr ret ->
  MbValuePerms (ghosts :++: args) -> CruCtx new_gouts ->
  Mb new_gouts (Mb out_ctx (ValuePerms new_gouts)) ->
  Mb new_gouts (Mb out_ctx (ValuePerms out_ctx)) ->
  FunPerm ghosts args (gouts :++: new_gouts) ret
mbGoutsFunPerm ghosts args gouts ret ps_in gouts' mb_gps' mb_ps_out'
  | ga_prxs <- cruCtxProxies $ appendCruCtx ghosts args
  , gouts_prxs <- cruCtxProxies gouts
  , gag_prxs <- RL.append ga_prxs gouts_prxs
  , ret_prxs <- cruCtxProxies $ singletonCruCtx ret
  , gouts'_prxs <- cruCtxProxies gouts'
  , Refl <- RL.appendAssoc ga_prxs gouts_prxs gouts'_prxs =
    FunPerm ghosts args (appendCruCtx gouts gouts') ret ps_in $
    mbCombine ret_prxs $ mbCombine gouts'_prxs $
    mbSwap gag_prxs $ fmap (mbSeparate ret_prxs) $
    mbMap2
    (mbMap2
     (\gps' ps_out' ->
       let (ga_perms, gouts_perms, MNil :>: ret_perm) =
             rlSplit3 ga_prxs gouts_prxs ret_prxs ps_out' in
       RL.append ga_perms (RL.append gouts_perms gps') :>: ret_perm))
    mb_gps' mb_ps_out'

-- | Find each subterm of the input that is a field, array, or block permission
-- with a different lifetime than the supplied one. Abstract out these
-- permissions by replacing each such permission @p@ with an @eq(x)@ permission
-- for a fresh variable @x@ which is itself assigned permission @p@. Only do
-- this abstraction, though, at locations where @x@ in the resulting permission
-- is a determined variable. When the supplied lifetime is omitted, i.e., is
-- 'Nothing', only perform this abstraction at strict subterms.
class AbstractVarsForLifetimes a where
  abstractVarsForLifetimes :: Maybe (PermExpr LifetimeType) -> a ->
                              SomeMbWithPerms a

instance AbstractVarsForLifetimes (ValuePerms ps) where
  abstractVarsForLifetimes l = traverseRAssign (abstractVarsForLifetimes l)

-- | Return the type of an atomic permission if we can compute it, specifically
-- if it is a field, array, or block permission
atomicPermType :: AtomicPerm a -> Maybe (TypeRepr a)
atomicPermType (Perm_LLVMField _) = Just knownRepr
atomicPermType (Perm_LLVMArray _) = Just knownRepr
atomicPermType (Perm_LLVMBlock _) = Just knownRepr
atomicPermType _ = Nothing

instance AbstractVarsForLifetimes (ValuePerm a) where
  abstractVarsForLifetimes (Just l) p@(ValPerm_Conj ps)
    | any (/= l) (mapMaybe atomicPermLifetime ps)
    , tp:_ <- mapMaybe atomicPermType ps =
      bindSomeMbWithPerms (abstractVarsForLifetimes Nothing p) $ \p' ->
      ValPerm_Eq <$> PExpr_Var <$> someMbWithPermsVar1 tp p'
  abstractVarsForLifetimes l (ValPerm_Conj ps) =
    ValPerm_Conj <$> traverse (abstractVarsForLifetimes l) ps
  abstractVarsForLifetimes l (ValPerm_Exists mb_p) =
    -- Any existentials also become abstracted variables, so they can be bound
    -- as ghosts or gouts (depending on whether they occur in the input or
    -- output permissions)
    mbSomeMbWithPerms knownRepr $ fmap (abstractVarsForLifetimes l) mb_p
  abstractVarsForLifetimes _ p = pure p

-- NOTE: for AtomicPerms, we don't ever replace the permission itself, since we
-- don't want to replace each individual permission pi in a conjunction p1*..*pn
-- with an equality perm, but instead want to replace the entire conjunction all
-- at once. This is handled in the above case for ValPerm_Conj.
instance AbstractVarsForLifetimes (AtomicPerm a) where
  abstractVarsForLifetimes _ (Perm_LLVMField fp) =
    (\p -> Perm_LLVMField $ fp { llvmFieldContents = p }) <$>
    abstractVarsForLifetimes (Just $ llvmFieldLifetime fp) (llvmFieldContents fp)
  -- FIXME: we can't yet abstract array permissions, because shapes in arrays
  -- could be repeated multiple times and thus we would have to somehow abstract
  -- over multiple copies of the same variable for that to work...
  abstractVarsForLifetimes _ (Perm_LLVMBlock bp) =
    (\sh -> Perm_LLVMBlock $ bp { llvmBlockShape = sh }) <$>
    abstractVarsForLifetimesSh (llvmBlockRW bp) (llvmBlockLifetime bp)
    (llvmBlockShape bp)
  abstractVarsForLifetimes _ (Perm_Struct ps) =
    -- NOTE: for struct perms we want to abstract any permission with any
    -- non-always lifetime, so we set l to always
    Perm_Struct <$>
    traverseRAssign (abstractVarsForLifetimes (Just PExpr_Always)) ps
  abstractVarsForLifetimes _ p = pure p

-- | Like 'abstractVarsForLifetimes' but for an LLVM shape inside a @memblock@
-- with the given modalities
abstractVarsForLifetimesSh :: (1 <= w, KnownNat w) => PermExpr RWModalityType ->
                              PermExpr LifetimeType ->
                              PermExpr (LLVMShapeType w) ->
                              SomeMbWithPerms (PermExpr (LLVMShapeType w))
abstractVarsForLifetimesSh _ l (PExpr_FieldShape (LLVMFieldShape p)) =
    PExpr_FieldShape <$> LLVMFieldShape <$> abstractVarsForLifetimes (Just l) p
abstractVarsForLifetimesSh rw l (PExpr_PtrShape maybe_rw (Just l') sh)
  | l /= l'
  , rw' <- maybe rw id maybe_rw
  , Just len <- llvmShapeLength sh =
    -- NOTE: abstracting a shape should return one with the same length
    bindSomeMbWithPerms (abstractVarsForLifetimesSh rw' l' sh) $ \sh' ->
    PExpr_FieldShape <$> LLVMFieldShape <$> ValPerm_Eq <$> PExpr_Var <$>
    someMbWithPermsVar1 knownRepr (ValPerm_LLVMBlock $
                                   LLVMBlockPerm rw' l' (bvInt 0) len sh')
abstractVarsForLifetimesSh rw l (PExpr_PtrShape maybe_rw maybe_l sh) =
  let rw' = maybe rw id maybe_rw in
  PExpr_PtrShape maybe_rw maybe_l <$> abstractVarsForLifetimesSh rw' l sh
abstractVarsForLifetimesSh rw l (PExpr_SeqShape sh1 sh2) =
    PExpr_SeqShape <$> abstractVarsForLifetimesSh rw l sh1 <*>
    abstractVarsForLifetimesSh rw l sh2
abstractVarsForLifetimesSh rw l (PExpr_ExShape mb_sh) =
  mbSomeMbWithPerms knownRepr $ fmap (abstractVarsForLifetimesSh rw l) mb_sh
abstractVarsForLifetimesSh _ _ sh = pure sh

-- | A 'SomeMbWithPerms' in a binding
data MbSomeMbWithPerms ctx a where
  MbSomeMbWithPerms :: CruCtx ctx' -> Mb ctx' (Mb ctx (ValuePerms ctx')) ->
                       Mb ctx' (Mb ctx a) ->
                       MbSomeMbWithPerms ctx a

mbAbstractVarsForLifetimes :: Mb ctx (ValuePerms ps) ->
                              MbSomeMbWithPerms ctx (ValuePerms ps)
mbAbstractVarsForLifetimes mb_ps
  | [nuMP| SomeMbWithPerms ctx' mb_ctx_ps' mb_ps' |] <-
      mbMatch (fmap (abstractVarsForLifetimes Nothing) mb_ps)
  , ctx'_prxs <- cruCtxProxies $ mbLift ctx' =
    MbSomeMbWithPerms (mbLift ctx') (mbSwap ctx'_prxs mb_ctx_ps')
    (mbSwap ctx'_prxs mb_ps')

-- | For both the input and output permissions of a function permission, find
-- all permissions @p@ in with a lifetime that are contained inside a struct
-- permission or a field or block permission with a different lifetime, and
-- replace each such permission with an @eq(z)@ permission for a fresh ghost
-- variable @z@ that is itself assigned permissions @p@.
abstractFunVarsForLifetimes :: Some3FunPerm -> Some3FunPerm
abstractFunVarsForLifetimes (Some3FunPerm
                         (FunPerm ghosts args gouts ret ps_in ps_out))
  | MbSomeMbWithPerms ghosts' mb_gps' mb_ps_in' <-
      mbAbstractVarsForLifetimes ps_in
  , MbSomeMbWithPerms gouts' mb_gops' mb_ps_out' <-
      mbAbstractVarsForLifetimes ps_out
  , ghosts_prxs <- cruCtxProxies ghosts
  , args_prxs <- cruCtxProxies args =
    Some3FunPerm $ mbGhostsFunPerm ghosts'
    (mbCombineAssoc ghosts' ghosts_prxs args_prxs mb_gps') $
    flip fmap mb_ps_in' $ \ps_in' ->
    mbGoutsFunPerm ghosts args gouts ret ps_in' gouts' mb_gops' mb_ps_out'

-- | Convert a monomorphic function type, i.e., one with no type arguments
rsConvertMonoFun :: (1 <= w, KnownNat w) => prx w -> Span -> Abi ->
                    [LifetimeDef Span] -> FnDecl Span ->
                    RustConvM Some3FunPerm
rsConvertMonoFun w span abi ls fn_tp =
  rsConvertFun w abi (Generics ls [] (WhereClause [] span) span) fn_tp

-- | Convert a Rust polymorphic function type to a Heapster function permission
rsConvertFun :: (1 <= w, KnownNat w) => prx w ->
                Abi -> Generics Span -> FnDecl Span -> RustConvM Some3FunPerm
rsConvertFun w abi (Generics ldefs _tparams@[]
                    (WhereClause [] _) _) (FnDecl args maybe_ret_tp False _) =
  -- fmap (\ret ->
  --        tracePretty (pretty "rsConvertFun returning:" <+>
  --                     permPretty emptyPPInfo ret) ret) $
  withLifetimes ldefs $
  do arg_shapes <- mapM (rsConvert w) args
     ret_shape <- maybe (return PExpr_EmptyShape) (rsConvert w) maybe_ret_tp
     abstractFunVarsForLifetimes <$> layoutFun abi arg_shapes ret_shape
rsConvertFun _ _ _ _ = fail "rsConvertFun: unsupported Rust function type"


----------------------------------------------------------------------
-- * Top-level Entrypoints
----------------------------------------------------------------------

-- | Parse a polymorphic Rust function type of the form
--
-- > <generics> (T1,...,Tn) -> T
--
-- and convert it to a Heapster function permission
parseFunPermFromRust :: (Fail.MonadFail m, 1 <= w, KnownNat w) =>
                        PermEnv -> prx w -> CruCtx args -> TypeRepr ret ->
                        String -> m (SomeFunPerm args ret)
parseFunPermFromRust env w args ret str =
  do get3SomeFunPerm <- parseSome3FunPermFromRust env w str
     un3SomeFunPerm args ret get3SomeFunPerm


-- | Just like `parseFunPermFromRust`, but returns a `Some3FunPerm`
parseSome3FunPermFromRust :: (Fail.MonadFail m, 1 <= w, KnownNat w) =>
                        PermEnv -> prx w ->
                        String -> m Some3FunPerm
parseSome3FunPermFromRust env w str
  | Just i <- findIndex (== '>') str
  , (gen_str, fn_str) <- splitAt (i+1) str
  , Right (Generics rust_ls1 rust_tvars wc span) <-
      parse (inputStreamFromString gen_str)
  , Right (BareFn _ abi rust_ls2 fn_tp _) <-
      parse (inputStreamFromString fn_str) =
    runLiftRustConvM (mkRustConvInfo env) $
    rsConvertFun w abi (Generics (rust_ls1 ++ rust_ls2) rust_tvars wc span) fn_tp

  | Just i <- findIndex (== '>') str
  , (gen_str, _) <- splitAt (i+1) str
  , Left err <- parse @(Generics Span) (inputStreamFromString gen_str) =
    fail ("Error parsing generics: " ++ show err)

  | Just i <- findIndex (== '>') str
  , (_, fn_str) <- splitAt (i+1) str
  , Left err <- parse @(Ty Span) (inputStreamFromString fn_str) =
    fail ("Error parsing generics: " ++ show err)
parseSome3FunPermFromRust _ _ str =
    fail ("Malformed Rust type: " ++ str)

-- | Parse a polymorphic Rust type declaration and convert it to a Heapster
-- shape
-- Note: No CruCtx / TypeRepr as arguments for now
parseNamedShapeFromRustDecl :: (Fail.MonadFail m, 1 <= w, KnownNat w) =>
                               PermEnv -> prx w -> String ->
                               m (SomePartialNamedShape w)
parseNamedShapeFromRustDecl env w str =
  case parse @(Item Span) (inputStreamFromString str) of
   Right item -> runLiftRustConvM (mkRustConvInfo env) $ rsConvert w item
   Left err -> fail ("Error parsing top-level item: " ++ show err)
