{-# Language TemplateHaskell #-}
{-# Language PolyKinds #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language OverloadedStrings #-}
{-# Language FlexibleContexts, FlexibleInstances, DefaultSignatures #-}
{-# Language DataKinds #-}
{-# Language PatternSynonyms #-}
{-# Language ParallelListComp #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Verifier.SAW.Heapster.JSONExport where

import Control.Monad
import Data.Aeson ( ToJSON(toJSON), Value(..), object )
import Data.Binding.Hobbits
import Data.BitVector.Sized ( BV, pattern BV )
import Data.Kind (Type)
import Data.Parameterized.BoolRepr ( BoolRepr )
import Data.Parameterized.Context ( Assignment )
import Data.Parameterized.Nonce (Nonce, indexValue)
import Data.Parameterized.TraversableFC ( FoldableFC(toListFC) )
import Data.Text (Text)
import Data.Type.RList ( mapToList )
import GHC.Natural (Natural)
import Lang.Crucible.FunctionHandle ( FnHandle )
import Lang.Crucible.LLVM.Bytes ( Bytes )
import Lang.Crucible.Types
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Datatype as TH
import Verifier.SAW.Heapster.CruUtil ( CruCtx )
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Name ( Ident )
import What4.FunctionName ( FunctionName )

instance NuMatching Value where
    nuMatchingProof = unsafeMbTypeRepr

instance Liftable Value where
    mbLift = unClosed . mbLift . fmap unsafeClose

ppToJson :: PPInfo -> ValuePerm x -> Value
ppToJson = jsonExport

class JsonExport a where
    jsonExport :: PPInfo -> a -> Value
    default jsonExport :: ToJSON a => PPInfo -> a -> Value
    jsonExport _ = toJSON

instance JsonExport (Name (t :: CrucibleType)) where
    jsonExport ppi x = toJSON (permPrettyString ppi x)

instance JsonExport1 f => JsonExport (Assignment f x) where
    jsonExport ppi x = toJSON (toListFC (jsonExport1 ppi) x)

instance JsonExport1 f => JsonExport (RAssign f x) where
    jsonExport ppi x = toJSON (mapToList (jsonExport1 ppi) x)

instance JsonExport b => JsonExport (Mb (a :: RList CrucibleType) b) where
    jsonExport ppi mb = mbLift $ flip nuMultiWithElim1 mb $ \names body ->
        object [
            ("args", jsonExport ppi names),
            ("body", jsonExport ppi body)
        ]

instance JsonExport (Nonce a b) where
    jsonExport _ = toJSON . indexValue

instance JsonExport Bytes where
    jsonExport _ = toJSON . show

instance JsonExport Ident where
    jsonExport _ = toJSON . show

instance JsonExport FunctionName where
    jsonExport _ = toJSON . show

instance JsonExport a => JsonExport (Maybe a) where
    jsonExport _ Nothing = Null
    jsonExport ppi (Just x) = jsonExport ppi x

instance (JsonExport a, JsonExport b) => JsonExport (a,b) where
    jsonExport ppi (x,y) = toJSON (jsonExport ppi x, jsonExport ppi y)

instance JsonExport a => JsonExport [a] where
    jsonExport ppi xs = toJSON (jsonExport ppi <$> xs)

instance JsonExport (BV n) where
    jsonExport _ (BV n) = toJSON n

instance JsonExport Natural
instance JsonExport Integer
instance JsonExport Int
instance JsonExport Bool
instance JsonExport Text
instance {-# OVERLAPPING #-} JsonExport String

class JsonExport1 f where
    jsonExport1 :: PPInfo -> f a -> Value
    default jsonExport1 :: JsonExport (f a) => PPInfo -> f a -> Value
    jsonExport1 = jsonExport

instance JsonExport1 BaseTypeRepr
instance JsonExport1 TypeRepr
instance JsonExport1 (Name :: CrucibleType -> Type)
instance JsonExport1 LOwnedPerm
instance JsonExport1 PermExpr
instance JsonExport1 ValuePerm

let newNames :: String -> Int -> TH.Q [TH.Name]
    newNames base n = forM [0..n-1] $ \i -> TH.newName (base ++ show i)

    build :: String -> TH.ConstructorVariant -> [TH.ExpQ] -> TH.ExpQ
    -- Record, use record field names as JSON field names
    build tag (TH.RecordConstructor fieldNames) xs =
        TH.listE
          $ [| ("tag", tag) |]
          : [ [| (n, $x) |] | n <- TH.nameBase <$> fieldNames | x <- xs]

    -- No fields, so just report the constructor tag
    build tag _ []  = [| [("tag", tag)] |]

    -- One field, just report that field
    build tag _ [x] = [| [("tag", tag), ("contents", $x)] |]

    -- Multiple fields, report them as a list
    build tag _ xs  = [| [("tag", tag), ("contents", toJSON $(TH.listE xs))] |]

    generateJsonExport n =
      do info <- TH.reifyDatatype n
         tVars <- newNames "a" (length (TH.datatypeInstTypes info))
         let t = foldl TH.AppT (TH.ConT n) (TH.VarT <$> tVars)
         [d| instance JsonExport $(pure t) where
                jsonExport _ppi x = $(
                    TH.caseE [|x|] [
                      do fieldVars <- newNames "x" (length (TH.constructorFields con))
                         TH.match
                            (TH.conP (TH.constructorName con) (TH.varP <$> fieldVars))
                            (TH.normalB [| object
                            $(build
                                (TH.nameBase (TH.constructorName con))
                                (TH.constructorVariant con)
                                [ [| jsonExport _ppi $(TH.varE v) |] | v <- fieldVars ]) |])
                            []
                         | con <- TH.datatypeCons info ]) |]

    typesNeeded =
        [''AtomicPerm, ''BaseTypeRepr, ''BoolRepr, ''BVFactor, ''BVProp,
        ''BVRange, ''CruCtx, ''FloatInfoRepr, ''FloatPrecisionRepr,
        ''FnHandle, ''FunPerm, ''LLVMArrayBorrow, ''LLVMArrayField,
        ''LLVMArrayIndex, ''LLVMArrayPerm, ''LLVMBlockPerm, ''LLVMFieldPerm,
        ''LLVMFieldShape, ''LOwnedPerm, ''NamedPermName, ''NamedShape,
        ''NamedShapeBody, ''NameReachConstr, ''NameSortRepr, ''NatRepr,
        ''PermExpr, ''PermOffset, ''StringInfoRepr, ''SymbolRepr, ''TypeRepr,
        ''ValuePerm, ''RWModality]

 in concat <$> traverse generateJsonExport typesNeeded

