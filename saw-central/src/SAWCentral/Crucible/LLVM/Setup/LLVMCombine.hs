{-# LANGUAGE LambdaCase #-}
{- |
Module      : SAWCentral.Crucible.LLVM.Setup.LLVMCombine
Description : Combine LLVM Modules
License     : BSD3
Maintainer  : Kevin Quick <kquick@galois.com>
Stability   : provisional

Thos module provides the ability to smash together LLVM Module specifications to
provide the ability to load separate LLVM Modules (e.g. bitcode files) and
analyze them as if they had been linked together as a single program.

The module exists separately from "SAWCentral.Crucible.LLVM.MethodSpecIR" and
"SAWCentral.Crucible.LLVM.Setup.Value" to confine this functionality and keep it
distinct from the other two.
-}

module SAWCentral.Crucible.LLVM.Setup.LLVMCombine
  ( llvmModuleCombine
  ) where

import Control.Lens
import Data.Bool ( bool )
import Data.Function ( on )
import Data.List ( find )
import Data.Maybe ( fromMaybe )
import Data.String ( fromString )
import Text.LLVM.AST
import Text.LLVM.Lens


-- | Combines LLVM Modules into a single, composite Module.  This is akin to
-- linking, but just from the perspective of what is needed for SAW/Cryptol
-- analysis.
--
-- Note that there is a Semigroup instance for 'Module', which is necessary for
-- the @llvm_pretty@ implementation of the @LLVM@ Monad containing a @WriterT
-- Module@, but it should *only* be used for building a 'Module' from elements
-- that do *not* have unresolved cross-Module symbols or other considerations.
-- The implementation here provides proper combination of independent Modules,
-- allowing symbol references in one module to be resolved by definitions in the
-- other, etc.
llvmModuleCombine :: Module -> Module -> Module
llvmModuleCombine a b =
  let defs = a ^. modDefinesLens
      decls = a ^. modDeclaresLens
      newDefs = b ^. modDefinesLens
      newDecls = b ^. modDeclaresLens
      rmvDefined = flip (foldr removeDefined)
      newDeclsLessOldDefs = rmvDefined defs newDecls
      oldDeclsLessNewDefs = rmvDefined newDefs decls
      joinName n = Just $ fromMaybe "..." n <> "+" <> fromMaybe "..." (modSourceName b)
  in a
     & modSourceNameLens %~ joinName
     & modDeclaresLens .~ (oldDeclsLessNewDefs <> newDeclsLessOldDefs)
     & modDefinesLens %~ deConflict (b ^. modDefinesLens)
     & modTypesLens <>~ b ^. modTypesLens
     & modNamedMdLens <>~ b ^. modNamedMdLens
     & modComdatLens <>~ b ^. modComdatLens
     & modGlobalsLens <>~ b ^. modGlobalsLens
     & modInlineAsmLens <>~ b ^. modInlineAsmLens
     & modAliasesLens <>~ b ^. modAliasesLens
  -- TODO Globals any should override Linkage external for the same name
  -- TODO extend modUnnamedMd and propagate those changes
  -- TODO verify modTriple and modDataLayout are the same?


-- | A Define takes precedence over a Declare.  When combining modules, module A
-- may Declare a function that is handled by a Define in module B, so get rid of
-- the Declare when putting A and B together.

removeDefined :: Define -> [Declare] -> [Declare]
removeDefined def = filter ((def ^. defNameLens /=) . view decNameLens)


-- | Module A and Module B may have a Define with the same name (Symbol).  This
-- is normal when linking multiple modules together, and is resolved by linkers
-- as guided by the Linkage information for the two Definitions, usually by
-- either renaming or merging.

deConflict :: [Define] -> [Define] -> [Define]
deConflict new curr = uncurry (<>) $ foldl deConflictDef (curr, new) new
  where
    deConflictDef (ads, bds) bd =
      case find (((==) `on` defName) bd) ads of
        Nothing -> (ads, bds)
        Just ad -> handle ads bds ad bd
    handle ads bds ad bd =
      case bd ^. defLinkageLens of
        Just Private -> (ads, renameDef bd (view defNameLens <$> ads) bds)
        Just LinkerPrivate -> (ads, renameDef bd (view defNameLens <$> ads) bds)
        Just LinkerPrivateWeak ->
          (ads, renameDef bd (view defNameLens <$> ads) bds) -- ??
        Just LinkerPrivateWeakDefAuto ->
          (ads, renameDef bd (view defNameLens <$> ads) bds) -- ??
        Just Internal -> (ads, renameDef bd (view defNameLens <$> ads) bds)
        Just AvailableExternally ->
          -- Never happen: not allowed on defines.  Ignore
          (ads, bds)
        Just Linkonce -> (mergeDef ad bd ads, removeDef bd bds)
        Just Weak -> (mergeDef ad bd ads, removeDef bd bds)
        Just Common -> (mergeDef ad bd ads, removeDef bd bds)
        Just ExternWeak -> (mergeDef ad bd ads, removeDef bd bds)
        Just LinkonceODR -> (mergeDef ad bd ads, removeDef bd bds)
        Just WeakODR -> (mergeDef ad bd ads, removeDef bd bds)
        Just Appending -> (appendDef ad bd ads, removeDef bd bds)
        Just External ->
          -- This should never happen: it is truly a symbol conflict.  A
          -- linker would reject this, but here we will just preserve the
          -- original.
          (ads, removeDef bd bds)
        Just DLLImport -> (ads, removeDef bd bds) -- ??
        Just DLLExport -> (ads, removeDef bd bds) -- ??
        Nothing ->
          -- No linkage specified.  The default is 'External', with associated
          -- considerations as documented for that case above.
          (ads, removeDef bd bds)

-- Note: Used for Linkonce, Weak, Common, ExternWeak, LinkonceODR, WeakODR. LLVM
-- docs say "merged", but also indicates that maybe there is a replacement
-- instead?  For now, treat "merged" as appending.
mergeDef :: Define -> Define -> [Define] -> [Define]
mergeDef = appendDef

appendDef :: Define -> Define -> [Define] -> [Define]
appendDef d1 d2 =
  let appenD = d1 & defBodyLens <>~ d2 ^. defBodyLens
  in (appenD :) . filter (((/=) `on` defName) d1)

removeDef :: Define -> [Define] -> [Define]
removeDef d = filter (((/=) `on` defName) d)


-- Renames the Defined symbol to a new name using a discriminator to avoid a
-- conflict.  Only valid for renaming Private/Internal Defines such that changing
-- any reference to the original Symbol to the new Symbol in the provided set of
-- Defines is sufficient to change all references.  Note therefore this excludes:
-- renaming of global variables, changing a GlobalAlias.

renameDef :: Define -> [Symbol] -> [Define] -> [Define]
renameDef toRename known inDefs =
  -- KWQ TODO: needs to change GlobalAlias aliasName?
  --
  let getNewName nm n =
        -- Note: adds a "discriminator" to the name in a way that is valid for
        -- both C functions and C++ mangled names (see
        -- https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangling-scope).
        let nn = if n < 10
                 then nm <> "_" <> show n
                 else nm <> "__" <> show n <> "_"
        in case find ((fromString nn ==) . defName) inDefs of
             Just _ -> getNewName nm $ succ n
             Nothing ->
               if fromString nn `elem` known
               then getNewName nm $ succ n
               else nn
      (Symbol oldname) = defName toRename
      newName = Symbol $ getNewName oldname (1 :: Integer)
  in changeSym (defName toRename) newName inDefs


changeSym :: Symbol -> Symbol -> [Define] -> [Define]
changeSym old new defs = fmap chngDef defs
  where
    chngDef d =
      d & defNameLens %~ chngSym
      & defBodyLens %~ fmap chngBlock
    chngBlock = bbStmtsLens %~ fmap chngStmt
    chngStmt = \case
      Result i inst drs vmds ->
        Result i (chngInstr inst) drs $ (fmap chngValMd <$> vmds)
      Effect inst drs vmds ->
        Effect (chngInstr inst) drs $ (fmap chngValMd <$> vmds)
    chngInstr = \case
      Ret tv -> Ret $ chngTyVal tv
      RetVoid -> RetVoid
      Arith o tv v -> Arith o (chngTyVal tv) (chngVal v)
      UnaryArith o tv -> UnaryArith o $ chngTyVal tv
      Bit o tv v -> Bit o (chngTyVal tv) (chngVal v)
      Conv o tv t -> Conv o (chngTyVal tv) t
      Call b t v tvs -> Call b t (chngVal v) (chngTyVal <$> tvs)
      CallBr t v tvs l ls -> CallBr t (chngVal v) (chngTyVal <$> tvs) l ls
      Alloca t mbtv i -> Alloca t (chngTyVal <$> mbtv) i
      Load t tv o a -> Load t (chngTyVal tv) o a
      Store tv1 tv2 o a -> Store (chngTyVal tv1) (chngTyVal tv2) o a
      Fence s o -> Fence s o
      CmpXchg b1 b2 tv1 tv2 tv3 s o1 o2 ->
        CmpXchg b1 b2 (chngTyVal tv1) (chngTyVal tv2) (chngTyVal tv3) s o1 o2
      AtomicRW b o tv1 tv2 s a ->
        AtomicRW b o (chngTyVal tv1) (chngTyVal tv2) s a
      ICmp b o tv v -> ICmp b o (chngTyVal tv) (chngVal v)
      FCmp o tv v -> FCmp o (chngTyVal tv) (chngVal v)
      Phi t vs -> Phi t ((\(v,l) -> (chngVal v, l)) <$> vs)
      GEP as t tv tvs -> GEP as t (chngTyVal tv) (chngTyVal <$> tvs)
      Select tv1 tv2 v -> Select (chngTyVal tv1) (chngTyVal tv2) (chngVal v)
      ExtractValue tv is -> ExtractValue (chngTyVal tv) is
      InsertValue tv1 tv2 is -> InsertValue (chngTyVal tv1) (chngTyVal tv2) is
      ExtractElt tv v -> ExtractElt (chngTyVal tv) (chngVal v)
      InsertElt tv1 tv2 v -> InsertElt (chngTyVal tv1) (chngTyVal tv2) (chngVal v)
      ShuffleVector tv1 v tv2 ->
        ShuffleVector (chngTyVal tv1) (chngVal v) (chngTyVal tv2)
      Jump t -> Jump t
      Br tv l1 l2 -> Br (chngTyVal tv) l1 l2
      Invoke t v tvs l1 l2 -> Invoke t (chngVal v) (chngTyVal <$> tvs) l1 l2
      Comment s -> Comment s
      Unreachable -> Unreachable
      Unwind -> Unwind
      VaArg tv t -> VaArg (chngTyVal tv) t
      IndirectBr tv lbs -> IndirectBr (chngTyVal tv) lbs
      Switch tv l tgts -> Switch (chngTyVal tv) l tgts
      LandingPad t mbtv b cls ->
        LandingPad t (chngTyVal <$> mbtv) b (chngClause <$> cls)
      Resume tv -> Resume $ chngTyVal tv
      Freeze tv -> Freeze $ chngTyVal tv
    chngClause = \case
      Catch tv -> Catch $ chngTyVal tv
      Filter tv -> Filter $ chngTyVal tv
    chngVal = \case
      ValSymbol s -> ValSymbol $ chngSym s
      ValArray t vs -> ValArray t (chngVal <$> vs)
      ValVector t vs -> ValVector t (chngVal <$> vs)
      ValStruct tvs -> ValStruct (chngTyVal <$> tvs)
      ValPackedStruct tvs -> ValPackedStruct (chngTyVal <$> tvs)
      ValMd vmd -> ValMd $ chngValMd vmd
      o -> o
    chngTyVal = typedValueLens %~ chngVal
    chngValMd = \case
      ValMdValue tv -> ValMdValue $ chngTyVal tv
      ValMdNode mvmds -> ValMdNode $ (fmap chngValMd <$> mvmds)
      o -> o
    chngSym s = bool s new $ old == s
