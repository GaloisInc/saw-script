{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.Heapster.CrucibleTranslation (
  BlockTranslate'(..),
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

type ResolveEntryIDs blocks = [(SomeTypedEntryID blocks, OpenTerm)]

-- TODO: I'm not sure this combinator can be written, because the `args` might
-- be escaping its scope.  Anyway, there's a way of inverting the flow of the
-- code so as to get something morally equivalent.
letRec ::
  TypedBlockMap ext blocks ret ->
  (ResolveEntryIDs blocks -> TypedEntry ext blocks ret args -> OpenTerm) ->
  (ResolveEntryIDs blocks -> OpenTerm) ->
  OpenTerm
letRec = error "TODO"

-- letRec'
--   [(SomeTypedEntryID blocks, ([(SomeTypedEntryID blocks, OpenTerm)] -> OpenTerm))] ->
--   -- ^ This is a list of mappings [(fun1, mkCode1), (fun2, mkCode2), ...], where
--   -- at index N, mkCodeN must construct the code for function funN, given as input
--   -- a list of mappings [(fun1, var1), (fun2, var2)] of mappings from entries to
--   -- a SAW variable that said function will be bound to (in a recursive let
--   -- form).  Therefore, if `mkCode2` wants to call `fun1`, it should use `var1`.
--   -- It can also perform recursive calls by using `var2`.
--   ([(SomeTypedEntryID blocks, OpenTerm)] -> OpenTerm) ->
--   -- ^ This builds the body of the `let rec`, usually calling in one of the
--   -- mutually-bound functions, whichever one is considered the "entry point".
--   -- It is given a mapping from entry IDs to the SAW variable that implements
--   -- the function with that ID.
--   OpenTerm
-- letRec' = error "Will exist"

translateCFG :: TypedCFG ext blocks ghosts init ret -> OpenTerm
translateCFG (TypedCFG {..}) =
    let initCtxRepr = permSetCtx tpcfgInputPerms in
    let typArgs     = typeTranslate'' initCtxRepr in
    let typPerms    = typeTranslate' (error "TODO") tpcfgInputPerms in
    lambdaOpenTerm "inputs" (pairTypeOpenTerm typArgs typPerms)
    -- lambdaPermSet (typedCFGInputTypes cfg) tpcfgInputPerms
    (\ inputs ->
     let mkBlockCode blockBinders entry =
           let info = BlocksInfo { entryPoints = blockBinders } in
           translateTypedEntry info entry
     in
     letRec tpcfgBlockMap mkBlockCode
     (\ blockBinders ->
       let entryPoint = lookupBlock blockBinders tpcfgEntryBlockID in
       applyOpenTerm entryPoint inputs
     )
    )

getTypedEntryID :: TypedEntry ext blocks ret args -> SomeTypedEntryID blocks
getTypedEntryID (TypedEntry i _ _ _) = SomeTypedEntryID i

getTypedBlockEntries :: TypedBlock ext blocks ret args -> [TypedEntry ext blocks ret args]
getTypedBlockEntries (TypedBlock entries) = entries

-- translateBlock :: BlocksInfo blocks -> TypedEntry ext blocks ret args -> (SomeTypedEntryID blocks, OpenTerm)
-- translateBlock info e = (getTypedEntryID e, translateTypedEntry info e)

translateTypedEntry :: BlocksInfo blocks -> TypedEntry ext blocks ret args -> OpenTerm
translateTypedEntry info (TypedEntry id types perms stmtSeq) =
  -- needs
  let ghostsCtxtRepr = entryGhosts id in
  let ctxtRepr = ghostsCtxtRepr <++> types in
  -- fold-right over the `fst` of t creating lambdas binding each term
  let typArgs = error "TODO" in
  let typPerms = error "TODO" in
  lambdaOpenTerm "inputs" (pairTypeOpenTerm typArgs typPerms)
  (\ inputs ->
   buildLambdaAsgn (fmapFC (Const . typeTranslate'') ctxtRepr) inputs
   (\ typeEnvironment ->
    buildLambdaAsgn (fmapFC (Const . typeTranslate typeEnvironment) $ permSetAsgn perms) inputs
    (\ permissionMap ->
     let jctx = JudgmentContext
                { typeEnvironment
                , permissionSet   = perms
                , permissionMap
                , catchHandler    = Nothing
                }
     in
     let t = blockTranslate' info jctx stmtSeq in
     error "TODO"
    )
   )
  )

buildLambdaAsgn ::
  Assignment (Const OpenTerm) ctx ->               -- ^ types
  OpenTerm ->                                      -- ^ nested tuple of said types
  (Assignment (Const OpenTerm) ctx -> OpenTerm) -> -- ^ body
  OpenTerm
buildLambdaAsgn = error "TODO"
--   (\ inputs ->
--    elimPair typArgs typPerms (\ _ -> error "TODO") inputs
--    (\ types perms ->
--
--    )
--   )

data BlocksInfo blocks = BlocksInfo
  { entryPoints :: ResolveEntryIDs blocks
  }

class BlockTranslate' blocks f | f -> blocks where
  blockTranslate' :: BlocksInfo blocks -> JudgmentContext ctx -> f ctx -> OpenTerm

instance BlockTranslate' blocks (TypedStmtSeq ext blocks ret) where

  blockTranslate' info jctx (TypedElimStmt perms elim) =
    error "TODO"

  blockTranslate' info jctx (TypedConsStmt loc stmt stmtSeq) =
    error "TODO"

  blockTranslate' info jctx (TypedTermStmt loc termStmt) =
    error "TODO"

instance BlockTranslate' blocks (TypedTermStmt blocks ret) where

  blockTranslate' info jctx (TypedJump tgt) = error "TODO"

  blockTranslate' info jctx (TypedBr cond tgt1 tgt2) = error "TODO"

  blockTranslate' info jctx (TypedReturn ret intros) = error "TODO"

  blockTranslate' info jctx (TypedErrorStmt err) = error "TODO"

-- TODO: For `Stmt`, for now, only need to deal with `SetReg`

instance JudgmentTranslate' (TypedStmt ext ctx) where

  judgmentTranslate' = error "TODO"

lambdaPermSet ::
  CtxRepr ctx ->
  PermSet ctx ->
  (JudgmentContext ctx -> OpenTerm) ->
  OpenTerm
lambdaPermSet = error "Will exist"

lookupBlock :: [(SomeTypedEntryID blocks, OpenTerm)] -> TypedEntryID blocks ghosts args -> OpenTerm
lookupBlock = error "Will exist"
