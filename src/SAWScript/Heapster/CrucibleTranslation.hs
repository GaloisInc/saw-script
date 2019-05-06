{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.Heapster.CrucibleTranslation (
  CrucibleTranslate''(..),
  ) where

import qualified Control.Lens                           as Lens
import           Data.Functor.Const
import           Data.List
import           Data.Maybe
import           Data.Parameterized.TraversableFC

import           Data.Parameterized.Context
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.Types
import           SAWScript.Heapster.Permissions
import           SAWScript.Heapster.JudgmentTranslation
import           SAWScript.Heapster.TypedCrucible
import           SAWScript.Heapster.TypeTranslation
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm

data SomeTypedEntryID blocks where
  SomeTypedEntryID :: TypedEntryID blocks ghosts args -> SomeTypedEntryID blocks

data CrucibleInfo blocks = CrucibleInfo
  { entryPoints :: [(SomeTypedEntryID blocks, OpenTerm)]
  }

class CrucibleTranslate' blocks f | f -> blocks where
  crucibleTranslate' :: CrucibleInfo blocks -> f ctx -> OpenTerm

class CrucibleTranslate'' blocks f | f -> blocks where
  crucibleTranslate'' :: CrucibleInfo blocks -> f -> OpenTerm

instance CrucibleTranslate'' blocks (TypedCFG ext blocks ghosts init ret) where
  crucibleTranslate'' info (TypedCFG {..}) =
    let typArgs  = error "TODO" in
    let typPerms = typeTranslate' (error "TODO") tpcfgInputPerms in
    lambdaOpenTerm "inputs" (pairTypeOpenTerm typArgs typPerms)
    -- lambdaPermSet (typedCFGInputTypes cfg) tpcfgInputPerms
    (\ inputs ->
     let blockCodes = concat $ toListFC (map (translateBlock info) . getTypedBlockEntries) tpcfgBlockMap in
     letRec blockCodes
     (\ blockBinders ->
       let entryPoint = lookupBlock blockBinders tpcfgEntryBlockID in
       applyOpenTerm entryPoint inputs
     )
    )

getTypedEntryID :: TypedEntry ext blocks ret args -> SomeTypedEntryID blocks
getTypedEntryID (TypedEntry i _ _ _) = SomeTypedEntryID i

getTypedBlockEntries :: TypedBlock ext blocks ret args -> [TypedEntry ext blocks ret args]
getTypedBlockEntries (TypedBlock entries) = entries

translateBlock :: CrucibleInfo blocks -> TypedEntry ext blocks ret args -> (SomeTypedEntryID blocks, OpenTerm)
translateBlock info e = (getTypedEntryID e, crucibleTranslate'' info e)

instance CrucibleTranslate'' blocks (TypedEntry ext blocks ret args) where
  crucibleTranslate'' info (TypedEntry _ _ _ stmtSeq) =
    crucibleTranslate' info stmtSeq

instance CrucibleTranslate' blocks (TypedStmtSeq ext blocks ret) where

  crucibleTranslate' info (TypedElimStmt perms elim) =
    error "TODO"

  crucibleTranslate' info (TypedConsStmt loc stmt stmtSeq) =
    error "TODO"

  crucibleTranslate' info (TypedTermStmt loc termStmt) =
    error "TODO"

letRec ::
  [(SomeTypedEntryID blocks, OpenTerm)] ->
  -- ^ maps entries to their code
  ([(SomeTypedEntryID blocks, OpenTerm)] -> OpenTerm) ->
  -- ^ maps entries to a let-bound variable implementing their code
  OpenTerm
letRec  = error "Will exist"

lambdaPermSet ::
  CtxRepr ctx ->
  PermSet ctx ->
  (JudgmentContext ctx -> OpenTerm) ->
  OpenTerm
lambdaPermSet = error "Will exist"

lookupBlock :: [(SomeTypedEntryID blocks, OpenTerm)] -> TypedEntryID blocks ghosts args -> OpenTerm
lookupBlock = error "Will exist"
