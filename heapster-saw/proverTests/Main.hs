{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap(singleton)
import Test.Tasty
import Verifier.SAW.Heapster.Permissions
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.MemModel (LLVMPointerType)
import Verifier.SAW.Heapster.Implication (proveVarImpl, checkVarImpl)
import Test.Tasty.HUnit
import Lang.Crucible.Types (BVType)

infix 5 ===>
infix 5 =/=>
infixl 8 \\
infixl 8 \\\
infixl 8 \\\\

(===>) :: (ToConj p1, ToConj p2) => p1 -> p2 -> IO ()
xs ===> ys = conj xs `doesImply` conj ys
(=/=>) :: (ToConj p1, ToConj p2) => p1 -> p2 -> IO ()
xs =/=> ys = conj xs `doesNotImply` conj ys

(\\) :: LLVMArrayPerm w -> [LLVMArrayBorrow w] -> LLVMArrayPerm w
(\\) a bs = a { llvmArrayBorrows = llvmArrayBorrows a ++ bs }

(\\\) :: (Integral a1, Integral a2) => LLVMArrayPerm 64 -> (a1, a2) -> LLVMArrayPerm 64
(\\\) a (i, l) = a \\ [RangeBorrow (BVRange (toIdx i) (toIdx l))]

(\\\\) :: (Integral a) => LLVMArrayPerm 64 -> a -> LLVMArrayPerm 64
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

instance Integral i => ArrayIndexExpr i where
  toIdx i = bvInt (toInteger i)

instance t ~ BVType 64 => ArrayIndexExpr (Name t) where
  toIdx x = PExpr_Var x

doesNotImply :: ValuePerm (LLVMPointerType 64) -> ValuePerm (LLVMPointerType 64) -> Assertion
doesNotImply l r =
  assertBool "should fail" (not $ checkImpl l r)

doesImply :: ValuePerm (LLVMPointerType 64) -> ValuePerm (LLVMPointerType 64) -> Assertion
doesImply l r =
  assertBool "should succeed" (checkImpl l r)


checkImpl :: ValuePerm (LLVMPointerType 64) -> ValuePerm (LLVMPointerType 64) -> Bool
checkImpl lhs rhs = mbLift (nu $ \x -> checkVarImpl (pset x) (proveVarImpl x perm_rhs))
  where
    perm_lhs = lhs
    perm_rhs = emptyMb rhs
    pset x = PermSet { _varPermMap = singleton x perm_lhs, _distPerms = DistPermsNil }

intShape :: PermExpr (LLVMShapeType 64)
intShape = PExpr_FieldShape $ LLVMFieldShape intField

intField :: ValuePerm (LLVMPointerType 64)
intField = ValPerm_Exists $ nu $ \x -> ValPerm_Eq (PExpr_LLVMWord (PExpr_Var x))

int64array :: ArrayIndexExpr a => a -> a -> AtomicPerm (LLVMPointerType 64)
int64array off len = Perm_LLVMArray (int64ArrayPerm off len)

int64ArrayPerm :: ArrayIndexExpr a => a -> a -> LLVMArrayPerm 64
int64ArrayPerm off len = arrayPerm (toIdx off) (toIdx len) 8 intShape

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

arrayTests :: TestTree
arrayTests =
  testGroup "arrayTests"
  [ testCase "too small" $ int64array 0 3 =/=> int64array 0 6
  , testCase "bigger"    $ int64array 0 6 ===> int64array 0 3

  , testGroup "sum of two arrays"
    [ testCase "exact"      $ [ int64array 0 3, int64array 24 3 ] ===> int64array 0 6
    , testCase "larger"     $ [ int64array 0 3, int64array 24 3 ] ===> int64array 0 5
    , testCase "not enough" $ [ int64array 0 3, int64array 24 3 ] =/=> int64array 0 7
    ]

  , testGroup "borrows on rhs"
    [ testCase "matched borrows" $
      int64ArrayPerm 0 3 \\\ (1,2) ===> int64ArrayPerm 0 3 \\\ (1,2)

    , testCase "sum of matched borrows" $
      [ int64ArrayPerm 0 3 \\\ (1,2) , int64ArrayPerm 24 3 ]
      ===> int64ArrayPerm 0 6 \\\ (1,2)

    , testCase "rhs borrow intersects two lhs borrows " $
      -- TODO: variant with enough perms to prove this
      int64ArrayPerm 0 5 \\\ (1, 3) \\\ (7,3) =/=> int64ArrayPerm 0 5 \\\ (2,6)

    , testCase "too much lhs borrowed" $ int64ArrayPerm 0 10 \\\ (5,2) =/=> int64ArrayPerm 0 10 \\\ (5,1)

    , testCase "sum of borrows" $
      [ int64ArrayPerm 0 3 \\\ (1,2) , int64ArrayPerm 24 4 \\\ (1,2) ]
      ===> int64ArrayPerm 0 7 \\\ (1,2) \\\ (3,3)
    ]
  ]

main :: IO ()
main = defaultMain arrayTests
