{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE LambdaCase #-}

module Verifier.SAW.Heapster.HintExtract ( heapsterRequireName, extractHints ) where

import Data.String (fromString)
import Data.Functor.Constant (Constant(..))
import Control.Lens ((^.))
import Control.Monad.Except
import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Map as Map
import Data.Char (chr)
import Text.LLVM.AST as L

import Data.Parameterized (toListFC, fmapFC, (:~:)(..), testEquality)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC (traverseFC)

import Data.Type.RList (mapRAssign, (:++:))
import Lang.Crucible.LLVM.Extension ( LLVM, LLVMStmt(..))
import Lang.Crucible.CFG.Core ( Some(Some)
                              , CtxRepr
                              , CFG(..)
                              , Reg(..)

                              , Block(..)
                              , blockStmts
                              , StmtSeq(..)
                              , Stmt (..), BlockID )

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.ParsedCtx
import Verifier.SAW.Heapster.PatternMatchUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.PermParser

heapsterRequireName :: String
heapsterRequireName = "heapster.require"

-- | The monad we use for extracting hints, which just has 'String' errors
type ExtractM = Except String

-- | Extract block hints from calls to @heapster.require@ in the Crucible CFG.
extractHints ::
  forall ghosts args outs blocks init ret.
  PermEnv ->
  [L.Module] {- ^ The original source modules: used for finding constant values (i.e. spec strings) -} ->
  FunPerm ghosts args outs ret {- ^ The FunPerm corresponding to the CFG we are scanning -} ->
  CFG LLVM blocks init ret {- ^ The Crucible CFG for which to build the block hint map -} ->
  Either String (Ctx.Assignment (Constant (Maybe Hint)) blocks)
extractHints env modules perm cfg =
  runExcept $ traverseFC extractHint (cfgBlockMap cfg)
  where
    globals =
      Map.fromList
        [ (globalSym g, str) | m <- modules,
                               g <- modGlobals m,
                               ValString chars <- maybeToList (globalValue g),
                               let str = chr . fromEnum <$> chars ]

    extractHint :: Block LLVM blocks ret ctx ->
                   ExtractM (Constant (Maybe Hint) ctx)
    extractHint block =
      extractBlockHints env globals (funPermTops perm) block >>= \case
      Just (SomeHintSpec ghosts valuePerms) ->
        return $ Constant $ Just (mkBlockEntryHint
                                  cfg
                                  (blockID block)
                                  (funPermTops perm)
                                  ghosts
                                  valuePerms)
      _ -> return $ Constant Nothing

-- | Packs up the ghosts in a parsed hint permission spec
data SomeHintSpec tops ctx where
  SomeHintSpec ::
    CruCtx ghosts ->
    MbValuePerms ((tops :++: CtxToRList ctx) :++: ghosts) ->
    SomeHintSpec tops ctx

-- | Try to find a hint in a Block
extractBlockHints ::
  forall blocks ret ctx tops.
  PermEnv ->
  Map.Map L.Symbol String {- ^ Globals map -} ->
  CruCtx tops {- ^ top context derived from current function's perm -} ->
  Block LLVM blocks ret ctx ->
  ExtractM (Maybe (SomeHintSpec tops ctx))
extractBlockHints env globals tops block =
  extractStmtsHint who env globals tops inputs stmts
  where
    stmts = block ^. blockStmts
    inputs = blockInputs block
    who = show (blockID block)

-- | Test if a sequence of statements starts with the Crucible representation of
-- a call to the dummy function @heapster.require@
extractStmtsHint ::
  forall blocks ret ctx tops.
  String ->
  PermEnv ->
  Map.Map L.Symbol String {- ^ globals -} ->
  CruCtx tops {- ^ top context derived from current function's perm -} ->
  CtxRepr ctx {- ^ block arguments -} ->
  StmtSeq LLVM blocks ret ctx ->
  ExtractM (Maybe (SomeHintSpec tops ctx))
extractStmtsHint who env globals tops inputs = loop Ctx.zeroSize
  where
    loop ::
      forall rest.
      Ctx.Size rest ->
      StmtSeq LLVM blocks ret (ctx Ctx.<+> rest) ->
      ExtractM (Maybe (SomeHintSpec tops ctx))
    loop sz_rest s =
      extractHintFromSequence who env globals tops inputs sz_rest s >>= \case
      Just p -> return $ Just p
      _ | ConsStmt _ s' rest <- s ->
          let inc_rest :: forall tp. Ctx.Size (rest Ctx.::> tp)
              inc_rest = Ctx.incSize sz_rest in
          case s' of
            SetReg{} -> loop inc_rest rest
            ExtendAssign{} -> loop inc_rest rest
            CallHandle{} -> loop inc_rest rest
            Print{} -> loop sz_rest rest
            ReadGlobal{} -> loop inc_rest rest
            WriteGlobal{} -> loop sz_rest rest
            FreshConstant {} -> loop inc_rest rest
            FreshFloat {} -> loop inc_rest rest
            FreshNat {} -> loop inc_rest rest
            NewRefCell {} -> loop inc_rest rest
            NewEmptyRefCell {} -> loop inc_rest rest
            ReadRefCell {} -> loop inc_rest rest
            WriteRefCell {} -> loop sz_rest rest
            DropRefCell {} -> loop sz_rest rest
            Assert {} -> loop sz_rest rest
            Assume {} -> loop sz_rest rest
      _ -> return Nothing

-- | Try to recognize the sequence of Crucible instructions leading up to
-- a call to heapster.require. If found, build a hint by parsing the provided
-- (global) ghost context string and spec string by looking them up
-- in the global map.
--
-- Will throw an error if the @require@ is malformed (malformed spec strings
-- or references out-of-scope values)
extractHintFromSequence ::
  forall tops ctx rest blocks ret.
  String ->
  PermEnv ->
  Map.Map L.Symbol String {- ^ globals -} ->
  CruCtx tops {- ^ toplevel context -} ->
  CtxRepr ctx {- ^ block arguments -} ->
  Ctx.Size rest {- ^ keeps track of how deep we are into the current block -} ->
  StmtSeq LLVM blocks ret (ctx Ctx.<+> rest) ->
  ExtractM (Maybe (SomeHintSpec tops ctx))
extractHintFromSequence who env globals tops blockIns sz s =
  case s of
    ConsStmt _ (ExtendAssign (LLVM_ResolveGlobal _ _ f))
      (ConsStmt _ (ExtendAssign (LLVM_ResolveGlobal _ _ ghosts))
        (ConsStmt _ (ExtendAssign (LLVM_ResolveGlobal _ _ spec))
          (ConsStmt _ (ExtendAssign (LLVM_LoadHandle _ _ ptr _ _))
            (ConsStmt _ (CallHandle _ fh _ actuals) _))))
          | globalSymbolName f == heapsterRequireName
          , Just Refl <- testEquality ptr fnPtrReg
          , Just Refl <- testEquality fh fnHdlReg
          , Just ghosts_str <- Map.lookup (fromString (globalSymbolName ghosts)) globals
          , Just spec_str <- Map.lookup (fromString (globalSymbolName spec)) globals ->
            -- The first two arguments are the ghost/spec strings.
            -- we can't "demote" their contexts to block args since they're globals
            -- and hence loaded in this block
            let (_, _, args) = expectLengthAtLeastTwo $ toListFC Some actuals in
            -- "demote" the context of each reg to the block input context,
            -- proving that each arg is in fact defined in a previous block
            -- (and is thus valid for use in this spec)
            case sequence (toBlockArg (Ctx.size blockIns) sizeAtCall <$> args) of
              Just demoted ->
                Just <$> requireArgsToHint who env blockIns tops demoted ghosts_str spec_str
              Nothing ->
                throwError (who ++ ": spec refers to block-defined expressions")

    _ -> return Nothing

  where
    fnPtrReg :: forall a b tp. Reg (ctx Ctx.<+> rest Ctx.::> tp Ctx.::> a Ctx.::> b) tp
    fnPtrReg = Reg (Ctx.skipIndex (Ctx.skipIndex (Ctx.nextIndex (Ctx.addSize (Ctx.size blockIns) sz))))

    fnHdlReg :: forall a b c tp. Reg ((ctx Ctx.<+> rest) Ctx.::> a Ctx.::> b Ctx.::> c Ctx.::> tp) tp
    fnHdlReg = Reg (Ctx.lastIndex (Ctx.addSize (Ctx.size blockIns) sizeAtCall))

    sizeAtCall :: forall a b c d. Ctx.Size (rest Ctx.::> a Ctx.::> b Ctx.::> c Ctx.::> d)
    sizeAtCall = Ctx.incSize (Ctx.incSize (Ctx.incSize (Ctx.incSize sz)))

-- | Assemble a Hint
--
-- Will throw an error if the @require@ is malformed (malformed spec strings
-- or references out-of-scope values)
requireArgsToHint ::
  String {-^ A string representing the block in which this call appears (for errors) -} ->
  PermEnv ->
  CtxRepr ctx {-^ The block arguments -}  ->
  CruCtx tops {-^ Toplevel arguments -} ->
  [Some (Reg ctx)] {-^ The actual arguments to the require, demoted to block args -} ->
  String {-^ The ghost ctx to parse -} ->
  String {-^ The permissions to parse -} ->
  ExtractM (SomeHintSpec tops ctx)
requireArgsToHint who env blockIns tops args ghostString specString =
  case parseParsedCtxString who env ghostString of
    Just (Some ghost_ctx) ->
      let full_ctx = appendParsedCtx (appendParsedCtx top_ctx ctx_rename) ghost_ctx
          sub = buildHintSub blockIns args
          ctx = mkArgsParsedCtx (mkCruCtx blockIns)
          top_ctx = mkTopParsedCtx tops
          ctx_rename = renameParsedCtx sub ctx
      in maybe (throwError (who ++ ": error parsing permissions"))
               (return . SomeHintSpec (parsedCtxCtx ghost_ctx))
               (parsePermsString who env full_ctx specString)
    Nothing ->
      throwError (who ++ ": error parsing ghost context")

-- | Apply a substitution to the names in a ParsedCtx
renameParsedCtx :: [(String, String)] -> ParsedCtx ctx -> ParsedCtx ctx
renameParsedCtx sub ctx = ctx { parsedCtxNames = renamed }
  where
    renamed = mapRAssign (\(Constant x) ->
                           Constant (substNames x)) (parsedCtxNames ctx)
    substNames x = fromMaybe x (lookup x sub)

-- | Build a susbstitution to apply to block arguments based on the actual
-- arguments provided to a @requires@ call, i.e. given
-- @heapster.require(..., ..., %11, %50)@
-- if @%11@ corresponds to block argument 1 and @%50@ to block argument 0,
-- with block arg 2 unused, then return the substitution
-- @[("arg1", "arg0"), ("arg1, arg0"), ("arg2", "arg2")]@
buildHintSub ::
  forall block_args.
  CtxRepr block_args ->
  [Some (Reg block_args)] ->
  [(String, String)]
buildHintSub blockArgs args = usedSub
  where
    argNames = someRegName <$> args
    unusedNames = argNamei <$> [length argNames .. (Ctx.sizeInt (Ctx.size blockArgs))]
    usedSub  = [ (a, argNamei i) | i <- [0..] | a <- argNames ++ unusedNames ]

-- | Check if we can use a register in a smaller context, and
-- return the register indexed by the new context if so.
toBlockArg ::
  Ctx.Size block_args ->
  Ctx.Size rest ->
  Some (Reg (block_args Ctx.<+> rest)) ->
  Maybe (Some (Reg block_args))
toBlockArg argsSz _restSz reg =
  case reg of
    Some (Reg idx) ->
      do Some idx' <- Ctx.intIndex (Ctx.indexVal idx) argsSz
         pure $ Some $ Reg idx'

-- | Constructor for block entry hints
mkBlockEntryHint ::
  forall blocks init ret top_args ghosts args.
  CFG LLVM blocks init ret ->
  BlockID blocks args ->
  CruCtx top_args ->
  CruCtx ghosts ->
  MbValuePerms ((top_args :++: CtxToRList args) :++: ghosts) ->
  Hint
mkBlockEntryHint cfg blockId tops ghosts valPerms  =
  Hint_Block $ BlockHint h blocks blockId entryHint
  where
    entryHint = BlockEntryHintSort tops ghosts valPerms
    h = cfgHandle cfg
    blocks = fmapFC blockInputs $ cfgBlockMap cfg

-- | Like mkArgParsedContext, but with all of the names
-- set to \"topi\" instead of \"argi\"
mkTopParsedCtx :: CruCtx ctx -> ParsedCtx ctx
mkTopParsedCtx = mkPrefixParsedCtx "top"

someRegName :: Some (Reg ctx) -> String
someRegName (Some (Reg i)) = argNamei (Ctx.indexVal i)

argNamei :: Int -> String
argNamei i = "arg" ++ show i
