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
  JudgmentTranslate'(..),
  translateCFG,
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
import           SAWScript.Heapster.ValueTranslation
import           SAWScript.TopLevel
import           Verifier.SAW.OpenTerm

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
     let t = judgmentTranslate' info jctx (error "TODO") stmtSeq in
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

instance JudgmentTranslate' blocks (TypedStmtSeq ext blocks ret) where

  judgmentTranslate' info jctx outputType (TypedElimStmt perms elim) =
    let elim' = judgmentTranslate' info jctx outputType elim in
    elim'

  judgmentTranslate' info jctx outputType (TypedConsStmt _ stmt stmtSeq) =
    let typeBefore  = error "TODO" in
    let typeBetween = error "TODO" in
    let typeAfter   = outputType in
    let stmt'       = translateTypedStmt jctx stmt in -- probably want to also pass [[typeBetween]]
    let jctx'       = error "TODO" in                 -- should this come from `translateTypedStmt`?
    let stmtSeq'    = judgmentTranslate' info jctx' outputType stmtSeq in
    -- composeM : (a b c: sort 0) -> (a -> CompM b) -> (b -> CompM c) -> a -> CompM c;
    applyOpenTermMulti (globalOpenTerm "Prelude.composeM")
    [ typeBefore
    , typeBetween
    , typeAfter
    , stmt'
    , stmtSeq'
    ]

  judgmentTranslate' info jctx outputType (TypedTermStmt _ termStmt) =
    judgmentTranslate' info jctx outputType termStmt

-- Should this function help in building a `JudgmentContext ctx'`?
translateTypedStmt :: JudgmentContext ctx -> TypedStmt ext ctx ctx' -> OpenTerm
translateTypedStmt jctx (TypedStmt pIn pOut stmt) = error "TODO"
translateTypedStmt jctx (DestructLLVMPtr w index) = error "TODO"

instance JudgmentTranslate' blocks (TypedTermStmt blocks ret) where

  judgmentTranslate' info jctx outputType (TypedJump tgt) =
    translateTypedJumpTarget info jctx tgt

  judgmentTranslate' info jctx outputType (TypedBr cond tgt1 tgt2) =
    let thenBranch = translateTypedJumpTarget info jctx tgt1 in
    let elseBranch = translateTypedJumpTarget info jctx tgt2 in
    error "TODO"

  judgmentTranslate' info jctx outputType (TypedReturn ret intros) =
    error "TODO"

  judgmentTranslate' info jctx outputType (TypedErrorStmt err) =
    error "TODO"

translateTypedJumpTarget ::
  BlocksInfo blocks ->
  JudgmentContext ctx ->
  TypedJumpTarget blocks ctx ->
  OpenTerm
translateTypedJumpTarget info jctx (TypedJumpTarget entryID args) =
  let targetFunction = lookupBlock (entryPoints info) entryID in
  let (TranslatedTypedArgs {..}) = translateTypedArgs jctx args in
  error "TODO"

data TranslatedTypedArgs ctx = TranslatedTypedArgs
  { argsCtxt  :: Assignment (Const OpenTerm) ctx
  , argsVars  :: [OpenTerm]
  , argsPerms :: [OpenTerm]
  , argsIntro :: OpenTerm
  }

translateTypedArgs ::
  JudgmentContext ctx ->
  TypedArgs ghostsAndArgs ctx ->
  TranslatedTypedArgs ghostsAndArgs
translateTypedArgs jctx (TypedArgs ctxRepr perms intros) =
  TranslatedTypedArgs
  { argsCtxt  = fmapFC (Const . typeTranslate'') ctxRepr
  , argsVars  = toListFC (valueTranslate (typeEnvironment jctx)) perms
  , argsPerms = toListFC (valueTranslate (permissionMap jctx)) perms
  , argsIntro = introJudgmentTranslate' jctx intros
  }

-- TODO: For `Stmt`, for now, only need to deal with `SetReg`

lambdaPermSet ::
  CtxRepr ctx ->
  PermSet ctx ->
  (JudgmentContext ctx -> OpenTerm) ->
  OpenTerm
lambdaPermSet = error "Will exist"

lookupBlock :: [(SomeTypedEntryID blocks, OpenTerm)] -> TypedEntryID blocks ghosts args -> OpenTerm
lookupBlock = error "Will exist"
