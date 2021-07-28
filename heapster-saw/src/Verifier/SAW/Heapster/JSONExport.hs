{-# Language TemplateHaskell #-}
{-# Language PolyKinds #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language OverloadedStrings #-}
{-# Language FlexibleContexts #-}
{-# Language DataKinds #-}
{-# Language PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Verifier.SAW.Heapster.JSONExport where

import Data.Aeson ( defaultOptions, ToJSON(toJSON), Value(String), object )
import Data.Aeson.TH ( deriveToJSON, mkToJSON )
import Data.Binding.Hobbits
import Data.BitVector.Sized ( BV, pattern BV )
import Data.Kind (Type)
import Data.Parameterized.BoolRepr ( BoolRepr )
import Data.Parameterized.Context ( Assignment )
import Data.Parameterized.Nonce (Nonce, indexValue)
import Data.Parameterized.TraversableFC ( FoldableFC(toListFC) )
import Data.Reflection ( give, Given(given) )
import Data.Type.RList ( mapToList )
import Lang.Crucible.FunctionHandle ( FnHandle )
import Lang.Crucible.LLVM.Bytes ( Bytes )
import Lang.Crucible.Types
import Verifier.SAW.Heapster.CruUtil ( CruCtx )
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Name ( Ident )
import What4.FunctionName ( FunctionName )

deriveToJSON defaultOptions ''NamedPermName
deriveToJSON defaultOptions ''FnHandle
deriveToJSON defaultOptions ''NameSortRepr
deriveToJSON defaultOptions ''BoolRepr
deriveToJSON defaultOptions ''TypeRepr
deriveToJSON defaultOptions ''NatRepr
deriveToJSON defaultOptions ''SymbolRepr
deriveToJSON defaultOptions ''FloatInfoRepr
deriveToJSON defaultOptions ''FloatPrecisionRepr
deriveToJSON defaultOptions ''StringInfoRepr
deriveToJSON defaultOptions ''BaseTypeRepr
deriveToJSON defaultOptions ''NameReachConstr
deriveToJSON defaultOptions ''CruCtx

-- Work-around for avoiding QuantifiedConstraints
class ToJSONf f where toJSONf :: f a -> Value
instance ToJSONf (FnHandle a) where toJSONf = toJSON
instance ToJSONf TypeRepr where toJSONf = toJSON
instance ToJSONf BaseTypeRepr where toJSONf = toJSON
instance Given PPInfo => ToJSONf PermExpr where toJSONf = toJSON
instance Given PPInfo => ToJSONf LOwnedPerm where toJSONf = toJSON
instance Given PPInfo => ToJSONf ValuePerm where toJSONf = toJSON
instance Given PPInfo => ToJSONf (Name :: CrucibleType -> Type) where toJSONf = toJSON

instance Given PPInfo => ToJSON (LLVMArrayBorrow a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMArrayBorrow)
instance Given PPInfo => ToJSON (LLVMArrayField a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMArrayField)
instance Given PPInfo => ToJSON (NamedShape a b c) where
    toJSON = $(mkToJSON defaultOptions ''NamedShape)
instance Given PPInfo => ToJSON (NamedShapeBody a b c) where
    toJSON = $(mkToJSON defaultOptions ''NamedShapeBody)
instance Given PPInfo => ToJSON (AtomicPerm a) where
    toJSON = $(mkToJSON defaultOptions ''AtomicPerm)
instance Given PPInfo => ToJSON (BVProp a) where
    toJSON = $(mkToJSON defaultOptions ''BVProp)
instance Given PPInfo => ToJSON (PermOffset a) where
    toJSON = $(mkToJSON defaultOptions ''PermOffset)
instance Given PPInfo => ToJSON (BVFactor a) where
    toJSON = $(mkToJSON defaultOptions ''BVFactor)
instance Given PPInfo => ToJSON (FunPerm a b c) where
    toJSON = $(mkToJSON defaultOptions ''FunPerm)
instance Given PPInfo => ToJSON (LLVMFieldShape a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMFieldShape)
instance Given PPInfo => ToJSON (LLVMFieldPerm a b) where
    toJSON = $(mkToJSON defaultOptions ''LLVMFieldPerm)
instance Given PPInfo => ToJSON (LLVMBlockPerm a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMBlockPerm)
instance Given PPInfo => ToJSON (LLVMArrayIndex a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMArrayIndex)
instance Given PPInfo => ToJSON (BVRange a) where
    toJSON = $(mkToJSON defaultOptions ''BVRange)
instance Given PPInfo => ToJSON (LLVMArrayPerm a) where
    toJSON = $(mkToJSON defaultOptions ''LLVMArrayPerm)
instance Given PPInfo => ToJSON (LOwnedPerm a) where
    toJSON = $(mkToJSON defaultOptions ''LOwnedPerm)
instance Given PPInfo => ToJSON (ValuePerm x) where
    toJSON = $(mkToJSON defaultOptions ''ValuePerm)
instance Given PPInfo => ToJSON (PermExpr x) where
    toJSON = $(mkToJSON defaultOptions ''PermExpr)

instance ToJSON RWModality where
    toJSON Read = String "Read"
    toJSON Write = String "Write"

instance ToJSON Bytes where
    toJSON = toJSON . show

instance ToJSON Ident where
    toJSON = toJSON . show

instance ToJSON FunctionName where
    toJSON = toJSON . show

instance ToJSON (BV n) where
    toJSON (BV n) = toJSON n

instance ToJSON (Nonce a b) where
    toJSON = toJSON . indexValue

instance ToJSONf f => ToJSON (RAssign f xs) where
    toJSON x = toJSON (mapToList toJSONf x)

instance Given PPInfo => ToJSON (Name (t :: CrucibleType)) where
    toJSON x = toJSON (permPrettyString given x)

instance ToJSONf f => ToJSON (Assignment f xs) where
    toJSON x = toJSON (toListFC toJSONf x)

instance (Given PPInfo, ToJSON b) => ToJSON (Mb (a :: RList CrucibleType) b) where
    toJSON mb = mbLift $ flip nuMultiWithElim1 mb $ \names body ->
        object [
            ("arguments", toJSON names),
            ("body", toJSON body)
        ]

instance NuMatching Value where
    nuMatchingProof = unsafeMbTypeRepr

instance Liftable Value where
    mbLift = unClosed . mbLift . fmap unsafeClose

ppToJson :: PPInfo -> ValuePerm x -> Value
ppToJson ppi x = give ppi (toJSON x)
