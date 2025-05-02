{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap(singleton)
import Test.Tasty
import Heapster.Permissions
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.MemModel (LLVMPointerType)
import Heapster.Implication (proveVarImpl, checkVarImpl)
import Test.Tasty.HUnit
import Lang.Crucible.Types (BVType)
import GHC.TypeLits

infix 5 ===>
infixl 8 \\
infixl 8 \\\
infixl 8 \\\\

(===>) :: (ToConj p1, ToConj p2) => p1 -> p2 -> Bool
xs ===> ys = conj xs `checkImpl` conj ys

(\\) :: LLVMArrayPerm w -> [LLVMArrayBorrow w] -> LLVMArrayPerm w
(\\) a bs = a { llvmArrayBorrows = llvmArrayBorrows a ++ bs }

(\\\) :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => LLVMArrayPerm 64 -> (a1, a2) -> LLVMArrayPerm 64
(\\\) a (i, l) = a \\ [RangeBorrow (BVRange (toIdx i) (toIdx l))]

(\\\\) :: (ArrayIndexExpr a) => LLVMArrayPerm 64 -> a -> LLVMArrayPerm 64
(\\\\) a i = a \\ [FieldBorrow (toIdx i)]

class t ~ LLVMPointerType 64 => ToAtomic a t | a -> t where
  atomic :: a -> AtomicPerm t

instance t ~ LLVMPointerType 64 => ToAtomic (AtomicPerm t) t where
  atomic = id

instance t ~ LLVMPointerType 64 => ToAtomic (LLVMArrayPerm 64) t where
  atomic = Perm_LLVMArray

class ToConj a where
  conj :: a -> ValuePerm (LLVMPointerType 64)

instance (ToAtomic p t, t ~ LLVMPointerType 64) => ToConj p where
  conj x = ValPerm_Conj1 (atomic x)

instance (ToAtomic p t, t ~ LLVMPointerType 64) => ToConj [p] where
  conj = ValPerm_Conj . fmap atomic

instance (t ~ LLVMPointerType 64) => ToConj [AtomicPerm t] where
  conj = ValPerm_Conj

class ArrayIndexExpr a where
  toIdx :: a -> PermExpr (BVType 64)

instance ArrayIndexExpr (PermExpr (BVType 64)) where
  toIdx = id

instance Integral i => ArrayIndexExpr i where
  toIdx i = bvInt (toInteger i)

instance t ~ BVType 64 => ArrayIndexExpr (Name t) where
  toIdx x = PExpr_Var x

passes :: Bool -> Assertion
passes = assertBool "should succeed"

fails :: Bool -> Assertion
fails = assertBool "should fail" . not

withName :: (Name (BVType 64) -> Bool) -> Bool
withName k = mbLift (nu k)

checkImpl :: ValuePerm (LLVMPointerType 64) -> ValuePerm (LLVMPointerType 64) -> Bool
checkImpl lhs rhs = mbLift (nu $ \x -> checkVarImpl (pset x) (proveVarImpl x perm_rhs))
  where
    perm_lhs = lhs
    perm_rhs = emptyMb rhs
    pset x = PermSet { _varPermMap = singleton x perm_lhs, _distPerms = DistPermsNil }

memblockPerm :: (ArrayIndexExpr a1, ArrayIndexExpr a2) =>
             a1 -> a2 -> PermExpr (LLVMShapeType 64) -> LLVMBlockPerm 64
memblockPerm off len shape  = LLVMBlockPerm
 { llvmBlockRW = PExpr_Write
 , llvmBlockLifetime = PExpr_Always
 , llvmBlockOffset = toIdx off
 , llvmBlockLen = toIdx len
 , llvmBlockShape = shape
 }

intValuePerm :: (KnownNat sz, 1 <= sz) => ValuePerm (LLVMPointerType sz)
intValuePerm = ValPerm_Exists $ nu $ \x -> ValPerm_Eq (PExpr_LLVMWord (PExpr_Var x))

fieldShape :: (KnownNat sz, 1 <= sz) => ValuePerm (LLVMPointerType sz) -> PermExpr (LLVMShapeType 64)
fieldShape p = PExpr_FieldShape (LLVMFieldShape p)

fieldPerm :: ArrayIndexExpr a => a -> ValuePerm (LLVMPointerType w) -> LLVMFieldPerm 64 w
fieldPerm off contents = LLVMFieldPerm
  { llvmFieldRW = PExpr_Write
  , llvmFieldLifetime = PExpr_Always
  , llvmFieldOffset = toIdx off
  , llvmFieldContents = contents
  }

field :: (KnownNat sz, 1 <= sz, ArrayIndexExpr a) =>
            a -> ValuePerm (LLVMPointerType sz) -> AtomicPerm (LLVMPointerType 64)
field off contents = Perm_LLVMField (fieldPerm off contents)

memblock_int64field :: (ArrayIndexExpr a) => a -> AtomicPerm (LLVMPointerType 64)
memblock_int64field off = Perm_LLVMBlock $ memblockPerm off 8 (fieldShape (intValuePerm @64))

memblock_int64array :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> AtomicPerm (LLVMPointerType 64)
memblock_int64array off len = Perm_LLVMBlock $ memblockPerm off (bvMult 8 (toIdx len)) (arrayShape len 8 (fieldShape (intValuePerm @64)))

int64field :: ArrayIndexExpr a => a -> AtomicPerm (LLVMPointerType 64)
int64field off = field off (intValuePerm :: ValuePerm (LLVMPointerType 64))

int64array :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> AtomicPerm (LLVMPointerType 64)
int64array off len = Perm_LLVMArray (int64ArrayPerm off len)

int32array :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> AtomicPerm (LLVMPointerType 64)
int32array off len = Perm_LLVMArray (int32ArrayPerm off len)

int64ArrayPerm :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> LLVMArrayPerm 64
int64ArrayPerm off len = arrayPerm (toIdx off) (toIdx len) 8 (fieldShape (intValuePerm @64))

int32ArrayPerm :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> LLVMArrayPerm 64
int32ArrayPerm off len = arrayPerm (toIdx off) (toIdx len) 4 (fieldShape (intValuePerm @32))

charShape :: PermExpr (LLVMShapeType 64)
charShape = fieldShape (intValuePerm @8)

charArray :: (ArrayIndexExpr a1, ArrayIndexExpr a2) => a1 -> a2 -> AtomicPerm (LLVMPointerType 64)
charArray off len = Perm_LLVMArray (arrayPerm (toIdx off) (toIdx len) 1 (fieldShape (intValuePerm @8)))

str3Block :: (ArrayIndexExpr a) => a -> AtomicPerm (LLVMPointerType 64)
str3Block off = Perm_LLVMBlock $
  memblockPerm off 3 (PExpr_SeqShape charShape (PExpr_SeqShape charShape charShape))

arrayPerm ::
  PermExpr (BVType w) ->
  PermExpr (BVType w) ->
  Bytes ->
  PermExpr (LLVMShapeType w) ->
  LLVMArrayPerm w
arrayPerm off len stride shape  = LLVMArrayPerm
  { llvmArrayRW = PExpr_Write
  , llvmArrayLifetime = PExpr_Always
  , llvmArrayOffset = off
  , llvmArrayLen    = len
  , llvmArrayStride = stride
  , llvmArrayCellShape = shape
  , llvmArrayBorrows = []
  }

arrayShape :: (ArrayIndexExpr a) => a -> Bytes -> PermExpr (LLVMShapeType 64) -> PermExpr (LLVMShapeType 64)
arrayShape len = PExpr_ArrayShape (toIdx len)

arrayTests :: TestTree
arrayTests =
  testGroup "arrayTests"
  [ testCase "too small" $ fails  $ int64array 0 3 ===> int64array 0 6
  , testCase "bigger"    $ passes $ int64array 0 6 ===> int64array 0 3

  , testGroup "sum of two arrays"
    [ testCase "exact"      $ passes $ [ int64array 0 3, int64array 24 3 ] ===> int64array 0 6
    , testCase "larger"     $ passes $ [ int64array 0 3, int64array 24 3 ] ===> int64array 0 5
    , testCase "not enough" $ fails  $ [ int64array 0 3, int64array 24 3 ] ===> int64array 0 7
    ]

  , testGroup "sum of fields"
    [ testCase "some fields" $ passes $
      [ int64field 0, int64field 8, int64field 16 ] ===> int64array 0 3
    , testCase "some extra fields" $ passes $
      [ int64field 0, int64field 8, int64field 16 ] ===> int64array 8 2
    , testCase "insufficient fields (1)" $ fails $
      [ int64field 0, int64field 8, int64field 16 ] ===> int64array 8 3
    , testCase "insufficient fields (2)" $ fails $
      [ int64field 0, int64field 8, int64field 16 ] ===> int64array 0 4
    , testCase "string" $ passes $ str3Block 0 ===> charArray 0 3
    ]

  , testGroup "mix of permission types"
    [ testCase "memblocks 1:1" $ passes $
      memblock_int64field 0 ===> int64array 0 1
    , testCase "memblocks insufficient" $ fails $
      [ memblock_int64field 0, memblock_int64field 8 ] ===> int64array 0 3
    , testCase "memblocks array 1:1" $ passes $
      memblock_int64array 0 3 ===> int64array 0 3
    , testCase "memblocks array 2:1" $ passes $
      [ memblock_int64array 8 3, memblock_int64array 32 4 ] ===> int64array 8 7
    ]

  , testGroup "symbolic"
    [ testCase "borrowed concrete field" $ fails $
      withName $ \l ->
        int64ArrayPerm 0 l \\\\ 0 ===> int64array 0 l
    , testCase "borrowed concrete field" $ passes $
      withName $ \l ->
        [atomic (int64ArrayPerm 0 l \\\\ 0), int64field 0]  ===> int64array 0 l
    , testCase "borrowed symbolic field" $ passes $
      withName $ \l -> withName $ \i ->
        [atomic (int64ArrayPerm 0 l \\\\ i), int64field (bvMult 8 (toIdx i))]  ===> int64array 0 l
    , testCase "symbolic length append" $ passes $
      withName $ \l ->
        [int64ArrayPerm 0 l, int64ArrayPerm (bvMult 8 (toIdx l)) l] ===> int64array 0 (bvMult 2 (toIdx l))
    ]

  , testGroup "borrows on rhs"
    [ testCase "matched borrows" $ passes $
      int64ArrayPerm 0 3 \\\ (1,2) ===> int64ArrayPerm 0 3 \\\ (1,2)

    , testCase "sum of matched borrows" $ passes $
      [ int64ArrayPerm 0 3 \\\ (1,2) , int64ArrayPerm 24 3 ]
      ===> int64ArrayPerm 0 6 \\\ (1,2)

    , testCase "borrowed lhs/rhs offset" $ passes $
      [ int64ArrayPerm 24 3,
        int64ArrayPerm 48 2 ] ===> int64ArrayPerm 24 5 \\\ (3, 2)

    , testCase "rhs borrow intersects two lhs borrows " $ fails $
      int64ArrayPerm 0 10 \\\ (1, 3) \\\ (7,3) ===> int64ArrayPerm 0 10 \\\ (2,6)

    , testCase "rhs borrow intersects two lhs borrows " $ passes $
      [ int64ArrayPerm 0 5 \\\ (1, 3) \\\ (7,3)
      , int64ArrayPerm 8 3
      , int64ArrayPerm 56 3
      ] ===> int64ArrayPerm 0 5 \\\ (2,6)

    , testCase "too much lhs borrowed" $ fails $ int64ArrayPerm 0 10 \\\ (5,2) ===> int64ArrayPerm 0 10 \\\ (5,1)

    , testCase "sum of borrows" $ passes $
      [ int64ArrayPerm 0 3 \\\ (1,2) , int64ArrayPerm 24 4 \\\ (1,2) ]
      ===> int64ArrayPerm 0 7 \\\ (1,2) \\\ (3,3)

    , testCase "fully-borrowed refl" $ passes $
      int64ArrayPerm 0 4 \\\ (0, 2) \\\ (2, 2)
      ===> int64ArrayPerm 0 4 \\\ (0, 2) \\\ (2, 2)
    ]
  ]

main :: IO ()
main = defaultMain arrayTests
