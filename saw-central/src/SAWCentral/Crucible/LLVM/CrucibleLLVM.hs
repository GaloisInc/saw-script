{- |
Module      : SAWCentral.Crucible.LLVM.CrucibleLLVM
Description : Re-exports from the crucible-llvm package
License     : BSD3
Maintainer  : huffman
Stability   : provisional

This module collects declarations from various modules in the
@crucible-llvm@ package into a single API.

-}
{-# LANGUAGE PatternSynonyms #-}

module SAWCentral.Crucible.LLVM.CrucibleLLVM
  (
    -- * Re-exports from "Lang.Crucible.LLVM"
    llvmGlobals
  , llvmExtensionImpl
  , registerLazyModule
    -- * Re-exports from "Lang.Crucible.LLVM.Bytes"
  , Bytes
  , bytesToBits
  , bytesToInteger
  , toBytes
    -- * Re-exports from "Lang.Crucible.LLVM.DataLayout"
  , Alignment
  , noAlignment
  , padToAlignment
  , DataLayout
  , intWidthSize
  , ptrBitwidth
  , integerAlignment
  , floatAlignment
  , fromAlignment
  , EndianForm(..)
    -- * Re-exports from "Lang.Crucible.LLVM.Extension"
  , ArchWidth
  , LLVMArch
    -- * Re-exports from "Lang.Crucible.LLVM.Intrinsics"
  , LLVM
  , llvmTypeCtx
  , register_llvm_overrides
  , llvmIntrinsicTypes
    -- * Re-exports from "Lang.Crucible.LLVM.MemType"
  , SymType(MemType, Alias, VoidType)
  , MemType(..)
  , memTypeSize
  , memTypeAlign
  , fiOffset
  , fiType
  , siFields
  , siFieldInfo
  , siFieldOffset
  , siFieldTypes
  , siIsPacked
  , mkStructInfo
  , ppMemType
  , Ident -- re-exported from llvm-pretty package
    -- * Re-exports from "Lang.Crucible.LLVM.LLVMContext"
  , TyCtx.TypeContext
  , llvmMetadataMap
  , llvmDataLayout
  , asMemType
  , liftType
  , liftMemType
  , liftRetType
    -- * Re-exports from "Lang.Crucible.LLVM.Globals"
  , GlobalInitializerMap
  , initializeMemoryConstGlobals
  , initializeAllMemory
  , makeGlobalMap
  , populateConstGlobals
    -- * Re-exports from "Lang.Crucible.LLVM.Translation"
  , ModuleTranslation
  , llvmMemVar
  , toStorableType
  , transContext
  , llvmPtrWidth
  , LLVMContext
  , translateModule
  , llvmDeclToFunHandleRepr'
  , TranslationOptions(..)
  , defaultTranslationOptions
  , getTranslatedCFG
    -- * Re-exports from "Lang.Crucible.LLVM.MemModel"
  , doResolveGlobal
  , Mem
  , MemImpl
  , doMalloc
  , doLoad
  , doStore
  , loadRaw
  , storeRaw
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  , assertSafe
  , isZero
  , testEqual
  , ppMem
  , packMemValue
  , unpackMemValue
  , buildDisjointRegionsAssertion
  , doPtrAddOffset
  , emptyMem
  , LLVMPointerType
  , pattern LLVMPointerRepr
  , AllocType(HeapAlloc, GlobalAlloc)
  , Mutability(..)
  , storageTypeF
  , StorageType
  , StorageTypeF(..)
  , storageTypeSize
  , fieldVal
  , bitvectorType
  , fieldPad
  , arrayType
  , mkStructType
  , mkStruct
  , LLVMVal(..)
  , LLVMPtr
  , HasPtrWidth
  , ptrToPtrVal
  , mkNullPointer
  , ptrIsNull
  , ptrEq
  , muxLLVMPtr
  , pattern PtrWidth
  , llvmPointerView
  , llvmPointer_bv
  , withPtrWidth
  , pattern LLVMPointer
  , pattern PtrRepr
  , ppPtr
  , projectLLVM_bv
  , mkMemVar
  ) where

import Lang.Crucible.LLVM
  (llvmGlobals, llvmExtensionImpl, registerLazyModule)

import Lang.Crucible.LLVM.Bytes
  (Bytes, bytesToBits, bytesToInteger, toBytes)

import Lang.Crucible.LLVM.DataLayout
  (Alignment, noAlignment, padToAlignment, DataLayout, EndianForm(..),
   integerAlignment, floatAlignment, fromAlignment, intWidthSize, ptrBitwidth)

import Lang.Crucible.LLVM.Extension
  (ArchWidth, LLVMArch)

import Lang.Crucible.LLVM.Intrinsics
  (LLVM, register_llvm_overrides, llvmIntrinsicTypes)

import Lang.Crucible.LLVM.MemType
  (SymType(MemType, Alias, VoidType),
   MemType(..),
   Ident, memTypeSize, memTypeAlign, fiOffset, fiType,
   siFields, siFieldInfo, siFieldOffset, siFieldTypes, siIsPacked,
   mkStructInfo, ppMemType)

import Lang.Crucible.LLVM.TypeContext
  (llvmMetadataMap, llvmDataLayout, asMemType, liftType, liftMemType, liftRetType)

import qualified Lang.Crucible.LLVM.TypeContext as TyCtx

import Lang.Crucible.LLVM.Globals
  (GlobalInitializerMap, makeGlobalMap, populateConstGlobals,
   initializeAllMemory, initializeMemoryConstGlobals)

import Lang.Crucible.LLVM.Translation
  (llvmMemVar, transContext, llvmPtrWidth, llvmTypeCtx,
   ModuleTranslation, LLVMContext, translateModule, llvmDeclToFunHandleRepr',
   TranslationOptions(..), defaultTranslationOptions, getTranslatedCFG )

import Lang.Crucible.LLVM.MemModel
  (Mem, MemImpl, doResolveGlobal, storeRaw, storeConstRaw, mallocRaw, mallocConstRaw,
   ppMem, packMemValue, unpackMemValue, buildDisjointRegionsAssertion,
   doLoad, doStore, loadRaw, doPtrAddOffset, assertSafe, isZero, testEqual,
   emptyMem, doMalloc, mkMemVar,
   LLVMVal(..),
   LLVMPtr, HasPtrWidth, ptrToPtrVal, mkNullPointer, ptrIsNull, ppPtr, ptrEq,
   pattern LLVMPointerRepr, LLVMPointerType,
   pattern PtrWidth, llvmPointer_bv, withPtrWidth, pattern LLVMPointer, pattern PtrRepr,
   llvmPointerView, projectLLVM_bv,
   muxLLVMPtr,
   storageTypeF, StorageType, StorageTypeF(..),
   storageTypeSize, toStorableType, fieldVal, bitvectorType, fieldPad, arrayType,
   mkStructType, AllocType(HeapAlloc, GlobalAlloc), Mutability(..))

import Lang.Crucible.Syntax (mkStruct)
