{- |
Module      : SAWScript.CrucibleLLVM
Description : Re-exports from the crucible-llvm package
License     : BSD3
Maintainer  : huffman
Stability   : provisional

This module collects declarations from various modules in the
@crucible-llvm@ package into a single API.

-}
{-# LANGUAGE PatternSynonyms #-}

module SAWScript.CrucibleLLVM
  (
    -- * Re-exports from "Lang.Crucible.LLVM"
    llvmGlobals
  , llvmExtensionImpl
  , registerModuleFn
    -- * Re-exports from "Lang.Crucible.LLVM.Bytes"
  , Bytes
  , bytesToBits
  , bytesToInteger
  , toBytes
    -- * Re-exports from "Lang.Crucible.LLVM.DataLayout"
  , Alignment
  , padToAlignment
  , DataLayout
  , intWidthSize
  , ptrBitwidth
  , integerAlignment
  , floatAlignment
  , EndianForm(..)
    -- * Re-exports from "Lang.Crucible.LLVM.Extension"
  , ArchWidth
    -- * Re-exports from "Lang.Crucible.LLVM.Intrinsics"
  , LLVM
  , llvmTypeCtx
  , register_llvm_overrides
  , llvmIntrinsicTypes
    -- * Re-exports from "Lang.Crucible.LLVM.MemType"
  , SymType(MemType, Alias, VoidType)
  , MemType(..)
  , memTypeSize
  , fiOffset
  , fiType
  , siFields
  , siFieldInfo
  , siFieldOffset
  , siFieldTypes
  , siIsPacked
  , mkStructInfo
  , Ident -- re-exported from llvm-pretty package
    -- * Re-exports from "Lang.Crucible.LLVM.LLVMContext"
  , LLVMTyCtx
  , llvmMetadataMap
  , llvmDataLayout
  , asMemType
  , liftType
  , liftMemType
  , liftRetType
    -- * Re-exports from "Lang.Crucible.LLVM.Translation"
  , ModuleTranslation
  , llvmMemVar
  , toStorableType
  , symbolMap
  , LLVMHandleInfo(LLVMHandleInfo)
  , cfgMap
  , transContext
  , llvmPtrWidth
  , initializeMemory
  , initMemoryCFG
  , LLVMContext
  , translateModule
    -- * Re-exports from "Lang.Crucible.LLVM.MemModel"
  , doResolveGlobal
  , Mem
  , MemImpl
  , doMalloc
  , doLoad
  , doStore
  , loadRawWithCondition
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  , ppMem
  , packMemValue
  , unpackMemValue
  , coerceAny
  , buildDisjointRegionsAssertion
  , doPtrAddOffset
  , emptyMem
  , LLVMPointerType
  , pattern LLVMPointerRepr
  , AllocType(HeapAlloc, GlobalAlloc)
  , Mutability(..)
  , typeF
  , Type
  , TypeF(Struct, Float, Double, Array, Bitvector)
  , typeSize
  , fieldVal
  , bitvectorType
  , fieldPad
  , arrayType
  , mkStructType
  , LLVMVal(LLVMValStruct, LLVMValInt, LLVMValArray, LLVMValReal)
  , LLVMPtr
  , HasPtrWidth
  , ptrToPtrVal
  , mkNullPointer
  , ptrIsNull
  , ptrEq
  , pattern PtrWidth
  , llvmPointerView
  , llvmPointer_bv
  , withPtrWidth
  , pattern LLVMPointer
  , pattern PtrRepr
  , ppPtr
  , projectLLVM_bv
  ) where

import Lang.Crucible.LLVM
  (llvmGlobals, llvmExtensionImpl, registerModuleFn)

import Lang.Crucible.LLVM.Bytes
  (Bytes, bytesToBits, bytesToInteger, toBytes)

import Lang.Crucible.LLVM.DataLayout
  (Alignment, padToAlignment, DataLayout, EndianForm(..),
   integerAlignment, floatAlignment, intWidthSize, ptrBitwidth)

import Lang.Crucible.LLVM.Extension
  (ArchWidth)

import Lang.Crucible.LLVM.Intrinsics
  (LLVM, llvmTypeCtx, register_llvm_overrides, llvmIntrinsicTypes)

import Lang.Crucible.LLVM.MemType
  (SymType(MemType, Alias, VoidType),
   MemType(..),
   Ident, memTypeSize, fiOffset, fiType,
   siFields, siFieldInfo, siFieldOffset, siFieldTypes, siIsPacked,
   mkStructInfo)

import Lang.Crucible.LLVM.LLVMContext
  (llvmMetadataMap, llvmDataLayout, asMemType, liftType, liftMemType, liftRetType)

import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx

import Lang.Crucible.LLVM.Translation
  (llvmMemVar, toStorableType, symbolMap, LLVMHandleInfo(LLVMHandleInfo),
   cfgMap, transContext, llvmPtrWidth, initializeMemory, initMemoryCFG,
   ModuleTranslation, LLVMContext, translateModule)

import Lang.Crucible.LLVM.MemModel
  (Mem, MemImpl, doResolveGlobal, storeConstRaw, mallocRaw, mallocConstRaw,
   ppMem, packMemValue, unpackMemValue, coerceAny, buildDisjointRegionsAssertion,
   doLoad, doStore, loadRawWithCondition, doPtrAddOffset, emptyMem, doMalloc,
   pattern LLVMPointerRepr, LLVMPointerType,
   AllocType(HeapAlloc, GlobalAlloc), Mutability(..),
   typeF, Type, TypeF(Struct, Float, Double, Array, Bitvector),
   typeSize, fieldVal, bitvectorType, fieldPad, arrayType, mkStructType,
   LLVMVal(LLVMValStruct, LLVMValInt, LLVMValArray, LLVMValReal),
   LLVMPtr, HasPtrWidth, ptrToPtrVal, mkNullPointer, ptrIsNull, ppPtr, ptrEq,
   pattern PtrWidth, llvmPointer_bv, withPtrWidth, pattern LLVMPointer, pattern PtrRepr,
   llvmPointerView, projectLLVM_bv)

-- | Renamed copy of 'TyCtx.LLVMContext' from module "Lang.Crucible.LLVM.LLVMContext".
type LLVMTyCtx = TyCtx.LLVMContext
