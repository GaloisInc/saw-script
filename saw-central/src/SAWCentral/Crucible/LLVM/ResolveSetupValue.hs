{- |
Module      : SAWCentral.Crucible.LLVM.ResolveSetupValue
Description : Turn SetupValues back into LLVMVals
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SAWCentral.Crucible.LLVM.ResolveSetupValue
  ( LLVMVal, LLVMPtr
  , resolveSetupVal
  , resolveSetupValBitfield
  , typeOfSetupValue
  , exceptToFail
  , resolveTypedTerm
  , resolveSAWPred
  , resolveSAWSymBV
  , recoverStructFieldInfo
  , resolveSetupValueInfo
  , BitfieldIndex(..)
  , resolveSetupBitfield
  , resolveSetupElemOffset
  , equalValsPred
  , memArrayToSawCoreTerm
  , scPtrWidthBvNat
  , W4EvalTactic(..)
  ) where

import Control.Lens ( (^.), view )
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Maybe (fromMaybe, fromJust, mapMaybe)
import Data.Void (absurd)

import qualified Data.Dwarf as Dwarf
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word (Word64)
import           Numeric.Natural

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import qualified Text.PrettyPrint.HughesPJ as PPHPJ -- for importing llvm-pretty docs

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.DebugUtils as L
import qualified Text.LLVM.PP as LPP

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))

import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr

import qualified What4.Interface    as W4

import qualified Lang.Crucible.LLVM.Bytes       as Crucible
import qualified Lang.Crucible.LLVM.MemModel    as Crucible
import qualified Lang.Crucible.LLVM.MemType     as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as Crucible

import qualified SAWSupport.Pretty as PPS

import SAWCore.SharedTerm

import CryptolSAWCore.Cryptol (translateType)
import CryptolSAWCore.TypedTerm
import SAWCoreWhat4.ReturnTrip

import           SAWCentral.Crucible.Common (Sym, sawCoreState, HasSymInterface(..))
import           SAWCentral.Crucible.Common.MethodSpec (AllocIndex(..), SetupValue(..), prettyAllocIndex)
import qualified SAWCentral.Crucible.Common.ResolveSetupValue as Common

import SAWCentral.Crucible.LLVM.MethodSpecIR
import SAWCentral.Crucible.LLVM.Setup.Value (LLVMPtr)

type LLVMVal = Crucible.LLVMVal Sym


------------------------------------------------------------
-- LLVM printing support

-- | Wrapper for an llvm-pretty printer.
--
--   llvm-pretty uses @Text.PrettyPrint.HughesPJ@ rather than
--   @Prettyprinter@ so we can't use the generated docs directly.
--
--   FUTURE: move this to its own file like @CryPP@ so we can just
--   do `LLVMPP.pretty` or whatever and not expose the plumbing.
--   ...or, just migrate llvm-pretty to @Prettyprinter@...
--
--   XXX: this should not arbitrarily bake in the latest supported
--   LLVM version but should use the version of the module we're
--   working on. Don't know how to get that info though.
llpretty :: ((?config :: LPP.Config) => a -> PPHPJ.Doc) -> a -> PPS.Doc
llpretty pp item =
    let hpjdoc = LPP.ppLLVM LPP.llvmVlatest $ pp item in
    let str = PPHPJ.render hpjdoc in
    PP.pretty str

-- | Print an `L.BitfieldInfo`. FUTURE: move to llvm-pretty
prettyBitfieldInfo :: PPS.Opts -> L.BitfieldInfo -> PPS.Doc
prettyBitfieldInfo ppopts info =
  let off = PPS.prettyWord64 ppopts (L.biBitfieldOffset info)
      sz = PPS.prettyWord64 ppopts (L.biFieldSize info)
  in
  sz <+> "bits at offset" <+> off

-- | Print an `L.StructFieldInfo`. FUTURE: move to llvm-pretty
prettyStructFieldInfo :: PPS.Opts -> L.StructFieldInfo -> PPS.Doc
prettyStructFieldInfo ppopts sfi =
    let name = PP.pretty $ L.sfiName sfi
        offset = PPS.prettyWord64 ppopts $ L.sfiOffset sfi
        mbf = prettyBitfieldInfo ppopts <$> L.sfiBitfield sfi
        info = prettyLLVMInfo ppopts $ L.sfiInfo sfi
        part1 = name <+> "@" <> offset <+> ":" <+> info
        part2 = case mbf of
            Nothing -> []
            Just bf -> ["..." <+> bf]
    in
    PP.hsep $ [part1] ++ part2

-- | Print an `L.UnionFieldInfo`. FUTURE: move to llvm-pretty
prettyUnionFieldInfo :: PPS.Opts -> L.UnionFieldInfo -> PPS.Doc
prettyUnionFieldInfo ppopts ufi =
    let name = PP.pretty $ L.ufiName ufi
        info = prettyLLVMInfo ppopts $ L.ufiInfo ufi
    in
    name <+> ":" <+> info

-- | Print an `L.Info`. FUTURE: move to llvm-pretty
--   XXX: what output syntax should this use?
prettyLLVMInfo :: PPS.Opts -> L.Info -> PPS.Doc
prettyLLVMInfo ppopts info0 = case info0 of
    L.Pointer info1 ->
        "pointer" <+> prettyLLVMInfo ppopts info1
    L.Structure mname fields ->
        let mname' = case mname of
              Nothing -> "anonymous struct"
              Just name -> "struct" <+> PP.pretty name
            fields' = PP.indent 3 $ PP.vsep $ map (prettyStructFieldInfo ppopts) fields
        in
        PP.vsep [mname', fields']
    L.Union mname fields ->
        let mname' = case mname of
              Nothing -> "anonymous union"
              Just name -> "union" <+> PP.pretty name
            fields' = PP.indent 3 $ PP.vsep $ map (prettyUnionFieldInfo ppopts) fields
        in
        PP.vsep [mname', fields']
    L.Typedef name info1 ->
        "typedef" <+> PP.pretty name <+> prettyLLVMInfo ppopts info1
    L.ArrInfo info1 ->
        "array" <+> prettyLLVMInfo ppopts info1
    L.BaseType name _ ->
        PP.pretty name
    L.Unknown ->
        "unknown"

------------------------------------------------------------
-- Errors

-- | Errors from various functions in here.
--
--   Unlike the roughly corresponding `MIRTypeOfError`, this one does
--   not print in advance; instead it throws unprinted values and
--   relies on the intercept site to be able to do the printing. In
--   both cases the printing needs access to the `PPS.Opts` and also
--   sometimes needs `IO`. However, here we use `ExceptT` to issue an
--   error of arbitrary type; the MIR code uses @MonadThrow@ to throw
--   `Exception`s, and the latter is tied to `Show` in a way that
--   makes it impossible for the receiver to print correctly.
--
--   Probably either this code or the MIR code should be rewritten
--   to work like the other one. It isn't clear yet which is better,
--   and we should put off that decision until we have access to
--   the new @SAWSupport.Console@ error mechanism in this layer.
--
data LLVMSetupError
  = LLVMUnresolvedPrestateVar AllocIndex
  | LLVMUnrepresentableType ToLLVMTypeErr
  | LLVMUnexpectedPolymorphic TypedTermType
  | LLVMEmptyArray
  | LLVMTypeFromDebugFailure L.Info
  | LLVMInvalidCast L.Type String
  | LLVMNonPointerCast Crucible.MemType
  | LLVMArrayOutOfBounds Int Natural
  | LLVMStructOutOfBounds Int Crucible.MemType
  | LLVMInvalidElem Crucible.MemType (Maybe String)
  | LLVMUnknownGlobal Text
  | LLVMInvalidType L.Type String
  | LLVMNoStruct Text L.Info
  | LLVMNoStructField Text (Maybe String) [L.StructFieldInfo]
  | LLVMBadOffsetStructField Text (Maybe String) Crucible.MemType
  | LLVMNoBitfieldStruct Text L.Info
  | LLVMNoBitfieldStructField Text (Maybe String) [L.StructFieldInfo]
  | LLVMBadOffsetBitfieldStructField Text (Maybe String) Crucible.MemType
  | LLVMNoUnion Text L.Info
  | LLVMNoUnionField Text (Maybe String) [L.UnionFieldInfo]
  | LLVMNoGlobalDebugInfo Text
  | LLVMNoLocalTypeInfo AllocIndex

ppLLVMSetupError :: SharedContext -> PPS.Opts -> LLVMSetupError -> IO Text
ppLLVMSetupError sc ppopts err = case err of
    LLVMUnresolvedPrestateVar i ->
        let i' = prettyAllocIndex i in
        pure $ PPS.renderText ppopts $ "typeOfSetupValue: Unresolved" <+>
            "prestate variable:" <+> i'
    LLVMUnrepresentableType suberr ->
        pure $ PPS.renderText ppopts $ prettyToLLVMTypeErr suberr
    LLVMUnexpectedPolymorphic tp -> do
        tp' <- prettyTypedTermType sc tp
        pure $ PPS.renderText ppopts $ "typeOfSetupValue: expected" <+>
              "monomorphic term; instead got " <+> tp'
    LLVMEmptyArray ->
        pure $ "typeOfSetupValue: invalid empty llvm_array_value"
    LLVMTypeFromDebugFailure info ->
        let info' = prettyLLVMInfo ppopts info in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Could not determine LLVM type from computed debug type information:",
            PP.indent 3 info'
        ]
    LLVMInvalidCast ltp suberr ->
        let ltp' = llpretty LPP.ppType ltp
            -- suberr comes from Crucible code and is just a String
            suberr' = PP.pretty suberr
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "typeOfSetupValue: invalid type in cast" <+> ltp',
            "Details:",
            suberr'
        ]
    LLVMNonPointerCast memTy ->
        let memTy' = Crucible.ppMemType memTy in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "typeOfSetupValue: Tried to cast the type of a non-pointer value",
            "Actual type of value:" <+> memTy'
        ]
    LLVMArrayOutOfBounds i n ->
        let i' = PPS.prettyInt ppopts i
            n' = PPS.prettyNatural ppopts n
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "typeOfSetupValue: Array index out of bounds",
            "Index:" <+> i',
            "Array length:" <+> n'
        ]
    LLVMStructOutOfBounds i memTy ->
        let i' = PPS.prettyInt ppopts i
            memTy' = Crucible.ppMemType memTy
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "typeOfSetupValue: Struct type index out of bounds",
            "Index:" <+> i',
            "Type:" <+> memTy'
        ]
    LLVMInvalidElem memTy mSuberr ->
        let memTy' = Crucible.ppMemType memTy in

        -- If you insert PP.emptyDoc in PP.vsep you get a blank line,
        -- which seems like a bug. But we don't get to decide that.
        let line1 = "typeOfSetupValue: llvm_elem requires pointer to struct or array"
            line2 = "found:" <+> memTy'
            rest = case mSuberr of
                Nothing -> []
                Just suberr ->
                    -- suberr comes from Crucible code and is just a String
                    [PP.pretty suberr]
        in
        pure $ PPS.renderText ppopts $ PP.vsep ([line1, line2] ++ rest)
    LLVMUnknownGlobal name ->
        pure $ "typeOfSetupValue: Unknown global " <> name
    LLVMInvalidType ty suberr ->
        let ty' = llpretty LPP.ppType ty
            -- suberr comes from Crucible code and is just a String
            suberr' = PP.pretty suberr
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "typeOfSetupValue: invalid type" <+> ty',
            "Details:",
            suberr'
        ]
    LLVMNoStruct n info ->
        let n' = PP.pretty n
            info' = case info of
                L.Unknown -> "Perhaps you need to compile with debug symbols enabled."
                _ -> prettyLLVMInfo ppopts info
        in
        pure $ PPS.renderText ppopts $ PP.vsep [      
            "Unable to resolve struct field name:" <+> n',
            "Could not resolve setup value debug information into a struct type.",
            info'
        ]
    LLVMNoStructField n snm xs ->
        let n' = PP.pretty n
            snm' = case snm of
                Nothing -> "an anonymous struct"
                Just nm -> "a struct" <+> PP.pretty nm
            xs' = PP.vsep $ map (\x -> "-" <+> PP.pretty (L.sfiName x)) xs
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Unable to resolve struct field name:" <+> n',
            "Found" <+> snm' <+> "with these fields:",
            xs'
        ]
    LLVMBadOffsetStructField n snm vty ->
        let n' = PP.pretty n
            snm' = case snm of
                Nothing -> "an anonymous struct"
                Just nm -> "a struct" <+> PP.pretty nm
            vty' = Crucible.ppMemType vty
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Found struct field name" <+> n' <+> "in struct with name" <+> snm' <> ".",
            "However, the offset of this field found in the debug information could not" <+>
                "be correlated with the computed LLVM type of the setup value.",
            "Field type:" <+> vty'
        ]
    LLVMNoBitfieldStruct n info ->
        let n' = PP.pretty n
            info' = case info of
               L.Unknown -> "Perhaps you need to compile with debug symbols enabled."
               _ -> prettyLLVMInfo ppopts info
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Unable to resolve struct bitfield name:" <+> n',
            "Could not resolve setup value debug information into a struct type.",
            info'
        ]
    LLVMNoBitfieldStructField n snm xs ->
        let n' = PP.pretty n
            snm' = case snm of
                Nothing -> "an anonymous struct"
                Just nm -> "a struct" <+> PP.pretty nm
            prettyX x = do
                bfi <- L.sfiBitfield x
                let name' = PP.pretty $ L.sfiName x
                let bfi' = prettyBitfieldInfo ppopts bfi
                pure $ "-" <+> name' <> ":" <+> bfi'
            xs' = PP.vsep $ mapMaybe prettyX xs
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Unable to resolve struct bitfield name:" <+> n',
            "Found" <+> snm' <+> "with these bitfield fields:",
            xs'
        ]
    LLVMBadOffsetBitfieldStructField n snm vty ->
        let n' = PP.pretty n
            snm' = case snm of
                Nothing -> "an anonymous struct"
                Just nm -> "a struct" <+> PP.pretty nm
            vty' = Crucible.ppMemType vty
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Found struct field name" <+> n' <+> "in struct with name" <+> snm' <> ".",
            "However, the offset of this field found in the debug information could not" <+>
                "be correlated with the computed LLVM type of the setup value," <+>
                "or that field is not a bitfield.",
            "Field type:" <+> vty'
        ]
    LLVMNoUnion n info ->
        let n' = PP.pretty n
            info' = case info of
                L.Unknown -> "Perhaps you need to compile with debug symbols enabled."
                _ -> prettyLLVMInfo ppopts info
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Unable to resolve union field name:" <+> n',
            "Could not resolve setup value debug information into a union type.",
            info'
        ]
    LLVMNoUnionField n unm xs ->
        let n' = PP.pretty n
            unm' = case unm of
                Nothing -> "an anonymous union"
                Just nm -> "a union" <+> PP.pretty nm
            xs' = PP.vsep $ map (\x -> "-" <+> PP.pretty (L.ufiName x)) xs
        in
        pure $ PPS.renderText ppopts $ PP.vsep [
            "Unable to resolve union field name:" <+> n',
            "Found" <+> unm' <+> "with these fields:",
            xs'
        ]
    LLVMNoGlobalDebugInfo name ->
        pure $ "Debug info for global name '" <> name <> "' not found."
    LLVMNoLocalTypeInfo i ->
        let i' = prettyAllocIndex i in
        pure $ PPS.renderText ppopts $
            "Type information not found for local allocation value:" <+> i'


exceptToFail :: (MonadFail m, MonadIO m) => SharedContext -> Except LLVMSetupError a -> m a
exceptToFail sc m = case runExcept m of
    Right result -> pure result
    Left err -> do
        ppopts <- liftIO $ scGetPPOpts sc
        msg <- liftIO $ ppLLVMSetupError sc ppopts err
        fail $ Text.unpack msg


------------------------------------------------------------
-- Everything else

-- | Attempt to look up LLVM debug metadata regarding the type of the
--   given setup value.  This is a best-effort procedure, as the
--   necessary debug information may not be avaliable. Even if this
--   procedure succeeds, the returned information may be partial, in
--   the sense that it may contain `Unknown` nodes.
resolveSetupValueInfo ::
  LLVMCrucibleContext wptr        {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec    {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch)          {- ^ pointer value -} ->
  Except LLVMSetupError L.Info   {- ^ debug type info of pointed-to type -}
resolveSetupValueInfo cc env nameEnv v =
  case v of
    SetupGlobal _ name ->
      case lookup (L.Symbol $ Text.unpack name) globalTys of
        Just (L.Alias alias) -> pure (L.guessAliasInfo mdMap alias)
        _ -> throwError $ LLVMNoGlobalDebugInfo name

    SetupVar i ->
      case Map.lookup i nameEnv of
        Just alias -> pure (L.guessAliasInfo mdMap alias)
        Nothing    ->
           -- TODO? is this a panic situation?
           throwError $ LLVMNoLocalTypeInfo i

    SetupCast (L.Alias alias) _ -> pure (L.guessAliasInfo mdMap alias)

    SetupField () a n ->
      do i <- resolveSetupValueInfo cc env nameEnv a
         case findStruct i of
           Nothing ->
             throwError $ LLVMNoStruct n i
           Just (snm, xs) ->
             let nstr = Text.unpack n in
             case [ i' | L.StructFieldInfo{L.sfiName = n', L.sfiInfo = i' } <- xs, nstr == n' ] of
               [] -> throwError $ LLVMNoStructField n snm xs
               i':_ -> pure i'

    SetupUnion () a u ->
      do i <- resolveSetupValueInfo cc env nameEnv a
         case findUnion i of
           Nothing ->
             throwError $ LLVMNoUnion u i
           Just (unm, xs) ->
             let ustr = Text.unpack u in
             case [ i' | L.UnionFieldInfo{L.ufiName = n', L.ufiInfo = i'} <- xs, ustr == n' ] of
               [] -> throwError $ LLVMNoUnionField u unm xs
               i':_ -> pure i'

    _ -> pure L.Unknown

  where
    globalTys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals (ccLLVMModuleAST cc) ]
    mdMap = Crucible.llvmMetadataMap (ccTypeCtx cc)

-- | Given DWARF type information that is expected to describe a
--   struct, find its name (if any) and information about its fields.
--   This procedure handles the common case where a typedef is used to
--   give a name to an anonymous struct. If a struct both has a direct
--   name and is included in a typedef, the direct name will be preferred.
findStruct :: L.Info -> Maybe (Maybe String, [L.StructFieldInfo])
findStruct = loop Nothing
 where loop _  (L.Typedef nm i)     = loop (Just nm) i
       loop nm (L.Structure nm' xs) = Just (nm' <> nm, xs)
       loop _ _ = Nothing

-- | Given DWARF type information that is expected to describe a
--   union, find its name (if any) and information about its fields.
--   This procedure handles the common case where a typedef is used to
--   give a name to an anonymous union. If a union both has a direct
--   name and is included in a typedef, the direct name will be preferred.
findUnion :: L.Info -> Maybe (Maybe String, [L.UnionFieldInfo])
findUnion = loop Nothing
  where loop _  (L.Typedef nm i) = loop (Just nm) i
        loop nm (L.Union nm' xs) = Just (nm' <> nm, xs)
        loop _ _ = Nothing

-- | Given LLVM debug information about a setup value, attempt to
--   find the corresponding @FieldInfo@ structure for the named
--   field.
recoverStructFieldInfo ::
  LLVMCrucibleContext arch      {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec  {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident {- ^ allocation type names -} ->
  SetupValue (LLVM arch)        {- ^ the value to examine -} ->
  L.Info                        {- ^ extracted LLVM debug information about the type of the value -} ->
  Text                        {- ^ the name of the field -} ->
  Except LLVMSetupError Crucible.FieldInfo
recoverStructFieldInfo cc env nameEnv v info n =
  case findStruct info of
    Nothing ->
      throwError $ LLVMNoStruct n info
    Just (snm,xs) ->
      let nstr = Text.unpack n in
      case [o | L.StructFieldInfo{L.sfiName = n', L.sfiOffset = o} <- xs, nstr == n' ] of
        [] -> throwError $ LLVMNoStructField n snm xs
        o:_ ->
          do vty <- typeOfSetupValue cc env nameEnv v
             case do Crucible.PtrType symTy <- pure vty
                     Crucible.StructType si <- let ?lc = ccTypeCtx cc
                                        in either (\_ -> Nothing) Just $ Crucible.asMemType symTy
                     V.find (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi) == fromIntegral o)
                            (Crucible.siFields si)
               of
               Nothing -> throwError $ LLVMBadOffsetStructField n snm vty
               Just fld -> return fld

-- | Attempt to turn type information from DWARF debug data back into
--   the corresponding LLVM type. This is a best-effort procedure, as
--   we may have to make educated guesses about names, and there might
--   not be enough data to succeed.
reverseDebugInfoType :: L.Info -> Maybe L.Type
reverseDebugInfoType = loop Nothing
  where
    loop n i = case i of
      L.Unknown ->
        case n of
          Just nm -> Just (L.Alias (L.Ident nm))
          Nothing -> Nothing

      L.Pointer i' -> L.PtrTo <$> loop Nothing i'

      L.Union n' _ ->
        case n' <> n of
          Just nm -> Just (L.Alias (L.Ident ("union."++ nm)))
          Nothing -> Nothing

      L.Structure n' xs ->
        case n' <> n of
          Just nm -> Just (L.Alias (L.Ident ("struct." ++ nm)))
          Nothing -> L.Struct <$> mapM (reverseDebugInfoType . L.sfiInfo) xs

      L.Typedef nm x -> loop (Just nm) x

      L.ArrInfo x -> L.Array 0 <$> loop Nothing x

      L.BaseType _nm bt -> reverseBaseTypeInfo bt

-- | Attempt to turn DWARF basic type information back into
--   LLVM type syntax.  This process is currently rather
--   ad-hoc, and may miss cases.
reverseBaseTypeInfo :: L.DIBasicType -> Maybe L.Type
reverseBaseTypeInfo dibt =
 case Dwarf.DW_ATE (fromIntegral (L.dibtEncoding dibt)) of
   Dwarf.DW_ATE_boolean -> Just $ L.PrimType $ L.Integer 1

   Dwarf.DW_ATE_float ->
     case L.dibtSize dibt of
       Just (L.ValMdValue (L.Typed _ (L.ValInteger sz))) ->
         case sz of
           16  -> Just $ L.PrimType $ L.FloatType $ L.Half
           32  -> Just $ L.PrimType $ L.FloatType $ L.Float
           64  -> Just $ L.PrimType $ L.FloatType $ L.Double
           80  -> Just $ L.PrimType $ L.FloatType $ L.X86_fp80
           128 -> Just $ L.PrimType $ L.FloatType $ L.Fp128
           _   -> Nothing
       _   -> Nothing

   Dwarf.DW_ATE_signed ->
     case L.dibtSize dibt of 
         Just (L.ValMdValue (L.Typed _ (L.ValInteger sz))) -> Just $ L.PrimType $ L.Integer (fromIntegral sz)
         _ -> Nothing

   Dwarf.DW_ATE_signed_char ->
     Just $ L.PrimType $ L.Integer 8

   Dwarf.DW_ATE_unsigned ->
     case L.dibtSize dibt of 
        Just (L.ValMdValue (L.Typed _ (L.ValInteger sz))) -> Just $ L.PrimType $ L.Integer (fromIntegral sz)
        _ -> Nothing

   Dwarf.DW_ATE_unsigned_char ->
     Just $ L.PrimType $ L.Integer 8

   _ -> Nothing



-- | Information about a field within a bitfield in a struct. For example,
-- given the following C struct:
--
-- @
-- struct s {
--   int32_t w;
--   uint8_t x1:1;
--   uint8_t x2:2;
--   uint8_t y:1;
--   int32_t z;
-- };
-- @
--
-- The 'BitfieldIndex'es for @x1@, @x2@, and @y@ are as follows:
--
-- @
-- -- x1
-- 'BitfieldIndex'
--   { 'biFieldSize' = 1
--   , 'biFieldOffset' = 0
--   , 'biBitfieldByteOffset' = 4
--   , 'biBitfieldType' = i8
--   }
--
-- -- x2
-- 'BitfieldIndex'
--   { 'biFieldSize' = 2
--   , 'biFieldOffset' = 1
--   , 'biBitfieldByteOffset' = 4
--   , 'biBitfieldType' = i8
--   }
--
-- -- y
-- 'BitfieldIndex'
--   { 'biFieldSize' = 1
--   , 'biFieldOffset' = 3
--   , 'biBitfieldByteOffset' = 4
--   , 'biBitfieldType' = i8
--   }
-- @
--
-- Note that the 'biFieldSize's and 'biFieldOffset's are specific to each
-- individual field, while the 'biBitfieldByteOffest's and 'biBitfieldType's are
-- all the same, as the latter two all describe the same bitfield.
data BitfieldIndex = BitfieldIndex
  { biFieldSize :: Word64
    -- ^ The size (in bits) of the field within the bitfield.
  , biFieldOffset :: Word64
    -- ^ The offset (in bits) of the field from the start of the bitfield,
    --   counting from the least significant bit.
  , biFieldByteOffset :: Crucible.Bytes
    -- ^ The offset (in bytes) of the struct member in which this bitfield resides.
  , biBitfieldType :: Crucible.MemType
    -- ^ The 'Crucible.MemType' of the overall bitfield.
  } deriving Show

-- | Given a pointer setup value and the name of a bitfield, attempt to
--   determine were in the struct that bitfield resides by examining
--   DWARF type metadata.
resolveSetupBitfield ::
  LLVMCrucibleContext arch {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident {- ^ allocation type names -} ->
  SetupValue (LLVM arch) {- ^ pointer to struct -} ->
  String {- ^ field name -} ->
  Except LLVMSetupError BitfieldIndex {- ^ information about bitfield -}
resolveSetupBitfield cc env nameEnv v n =
  do info <- resolveSetupValueInfo cc env nameEnv v
     case findStruct info of
       Nothing ->
         throwError $ LLVMNoBitfieldStruct (Text.pack n) info
       Just (snm, xs) ->
         case [ (fieldOffsetStartingFromStruct, bfInfo) | L.StructFieldInfo
                     { L.sfiName = n'
                     , L.sfiOffset = fieldOffsetStartingFromStruct
                     , L.sfiBitfield = Just bfInfo
                     } <- xs, n == n' ] of

           [] -> throwError $ LLVMNoBitfieldStructField (Text.pack n) snm xs

           ((fieldOffsetStartingFromStruct, bfInfo):_) ->
             do memTy <- typeOfSetupValue cc env nameEnv v
                case do Crucible.PtrType symTy <- pure memTy
                        Crucible.StructType si <- let ?lc = ccTypeCtx cc
                                                   in either (\_ -> Nothing) Just $ Crucible.asMemType symTy
                        fi <- V.find (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi)
                                                      == fromIntegral (L.biBitfieldOffset bfInfo))
                                      (Crucible.siFields si)
                        let fieldOffsetStartingFromBitfield =
                              fieldOffsetStartingFromStruct - L.biBitfieldOffset bfInfo
                        pure $ BitfieldIndex { biFieldSize       = L.biFieldSize bfInfo
                                             , biFieldOffset     = fieldOffsetStartingFromBitfield
                                             , biBitfieldType    = Crucible.fiType fi
                                             , biFieldByteOffset = Crucible.fiOffset fi
                                             }
                  of
                  Nothing ->
                    throwError $ LLVMBadOffsetBitfieldStructField (Text.pack n) snm memTy
                  Just bfi -> return bfi

-- | Attempt to compute the @MemType@ of a setup value.
typeOfSetupValue :: forall arch.
  LLVMCrucibleContext arch      {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec  {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident {- ^ allocation type names -} ->
  SetupValue (LLVM arch)        {- ^ value to compute the type of -} ->
  Except LLVMSetupError Crucible.MemType
typeOfSetupValue cc env nameEnv val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing ->
          throwError $ LLVMUnresolvedPrestateVar i
        Just spec ->
          return (Crucible.PtrType (Crucible.MemType (spec ^. allocSpecType)))

    SetupTerm tt ->
      case ttType tt of
        TypedTermSchema (Cryptol.Forall [] [] ty) ->
          case toLLVMType dl (Cryptol.evalValType mempty ty) of
            Left err -> throwError $ LLVMUnrepresentableType err
            Right memTy -> return memTy
        tp ->
          throwError $ LLVMUnexpectedPolymorphic tp

    SetupStruct packed vs ->
      do memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         let si = Crucible.mkStructInfo dl packed memTys
         return (Crucible.StructType si)

    SetupEnum empty ->
      absurd empty
    SetupTuple empty _ ->
      absurd empty
    SetupSlice empty ->
      absurd empty

    SetupArray () [] ->
      throwError LLVMEmptyArray
    SetupArray () (v : vs) ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         _memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         -- TODO XXX: check that all memTys are compatible with memTy
         return (Crucible.ArrayType (fromIntegral (length (v:vs))) memTy)

    SetupField () v n ->
      do info <- resolveSetupValueInfo cc env nameEnv v
         fld <- recoverStructFieldInfo cc env nameEnv v info n
         pure $ Crucible.PtrType $ Crucible.MemType $ Crucible.fiType fld

    SetupUnion () v n ->
      do info <- resolveSetupValueInfo cc env nameEnv (SetupUnion () v n)
         case reverseDebugInfoType info of
           Nothing -> throwError $ LLVMTypeFromDebugFailure info
           Just ltp -> typeOfSetupValue cc env nameEnv (SetupCast ltp v)

    SetupCast ltp v ->
      do memTy <- typeOfSetupValue cc env nameEnv v
         if Crucible.isPointerMemType memTy
           then
             case let ?lc = lc in Crucible.liftMemType (L.PtrTo ltp) of
               Left err -> throwError $ LLVMInvalidCast ltp err
               Right mt -> pure mt

           else
             throwError $ LLVMNonPointerCast memTy

    SetupElem () v i -> do
      do memTy <- typeOfSetupValue cc env nameEnv v
         case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in Crucible.asMemType symTy of
               Right memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     -- i == n is valid because pointers can point one-past-the-end of an array
                     -- also note that this relies on `fromIntegral` promoting i to unsigned
                     | fromIntegral i <= n -> return (Crucible.PtrType (Crucible.MemType memTy''))
                     | otherwise -> throwError $ LLVMArrayOutOfBounds i n
                   Crucible.StructType si ->
                     case Crucible.siFieldInfo si i of
                       Just fi -> return (Crucible.PtrType (Crucible.MemType (Crucible.fiType fi)))
                       Nothing -> throwError $ LLVMStructOutOfBounds i memTy'
                   _ -> throwError $ LLVMInvalidElem memTy Nothing
               Left err -> throwError $ LLVMInvalidElem memTy (Just err)
           _ -> throwError $ LLVMInvalidElem memTy Nothing

    SetupNull () ->
      -- We arbitrarily set the type of NULL to void*, because a) it
      -- is memory-compatible with any type that NULL can be used at,
      -- and b) it prevents us from doing a type-safe dereference
      -- operation.
      return (Crucible.PtrType Crucible.VoidType)

    -- A global and its initializer have the same type.
    SetupGlobal () name -> do
      let m = ccLLVMModuleAST cc
          tys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals m ] ++
                [ (L.decName d, L.decFunType d) | d <- L.modDeclares m ] ++
                [ (L.defName d, L.defFunType d) | d <- L.modDefines m ]
      case lookup (L.Symbol $ Text.unpack name) tys of
        Nothing -> throwError $ LLVMUnknownGlobal name
        Just ty ->
          case let ?lc = lc in Crucible.liftType ty of
            Left err -> throwError $ LLVMInvalidType ty err
            Right symTy -> return (Crucible.PtrType symTy)

    SetupGlobalInitializer () name -> do
      case Map.lookup (L.Symbol $ Text.unpack name) (view Crucible.globalInitMap $ ccLLVMModuleTrans cc) of
        Just (g, _) ->
          case let ?lc = lc in Crucible.liftMemType (L.globalType g) of
            Left err -> throwError $ LLVMInvalidType (L.globalType g) err
            Right memTy -> return memTy
        Nothing -> throwError $ LLVMUnknownGlobal name

    SetupMux empty _ _ _ ->
      absurd empty
  where
    lc = ccTypeCtx cc
    dl = Crucible.llvmDataLayout lc

-- | Given a pointer setup value that points to an aggregate
--   type (struct or array), attempt to compute  the byte offset of
--   the nth element of that aggregate structure.
resolveSetupElemOffset ::
  LLVMCrucibleContext arch        {- ^ crucible context  -} ->
  Map AllocIndex LLVMAllocSpec    {- ^ allocation types  -} ->
  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
  SetupValue (LLVM arch)          {- ^ base pointer -} ->
  Int                             {- ^ element index -} ->
  Except LLVMSetupError Crucible.Bytes  {- ^ element offset -}
resolveSetupElemOffset cc env nameEnv v i = do
  do memTy <- typeOfSetupValue cc env nameEnv v
     case memTy of
       Crucible.PtrType symTy ->
         case let ?lc = lc in Crucible.asMemType symTy of
           Right memTy' ->
             case memTy' of
               Crucible.ArrayType n memTy''
                 -- i == n is valid because pointers can point one-past-the-end of an array
                 | fromIntegral i <= n -> return (fromIntegral i * Crucible.memTypeSize dl memTy'')
               Crucible.StructType si ->
                 case Crucible.siFieldOffset si i of
                   Just d -> return d
                   Nothing -> throwError $ LLVMStructOutOfBounds i memTy'
               _ -> throwError $ LLVMInvalidElem memTy Nothing
           Left err -> throwError $ LLVMInvalidElem memTy (Just err)
       _ -> throwError $ LLVMInvalidElem memTy Nothing
  where
    lc = ccTypeCtx cc
    dl = Crucible.llvmDataLayout lc


-- | The tactic for What4 translation for SAWCore expressions during
-- Crucible symbolic execution. The boolean option specifies whether
-- non-user-defined symbols are translated. Note that ground constants are
-- always translated.
newtype W4EvalTactic = W4EvalTactic { doW4Eval :: Bool }
  deriving (Eq, Ord, Show)

-- | Translate a SetupValue into a Crucible LLVM value, resolving
--   references.
resolveSetupVal :: forall arch.
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  IO LLVMVal
resolveSetupVal cc mem env tyenv nameEnv val =
  ccWithBackend cc $ \bak ->
  let sym = backendGetSym bak
      lc = ccTypeCtx cc
      dl = Crucible.llvmDataLayout lc
  in
  case val of
    SetupVar i
      | Just ptr <- Map.lookup i env -> return (Crucible.ptrToPtrVal ptr)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
    -- NB, SetupCast values should always be pointers. Pointer casts have no
    -- effect on the actual computed LLVMVal.
    SetupCast _lty v -> resolveSetupVal cc mem env tyenv nameEnv v
    -- NB, SetupUnion values should always be pointers. Pointer casts have no
    -- effect on the actual computed LLVMVal.
    SetupUnion () v _n -> resolveSetupVal cc mem env tyenv nameEnv v
    SetupStruct packed vs -> do
      vals <- mapM (resolveSetupVal cc mem env tyenv nameEnv) vs
      let tps = map Crucible.llvmValStorableType vals
      let t = Crucible.mkStructType (V.fromList (mkFields packed dl Crucible.noAlignment 0 tps))
      let flds = case Crucible.storageTypeF t of
                   Crucible.Struct v -> v
                   _ -> error "impossible"
      return $ Crucible.LLVMValStruct (V.zip flds (V.fromList vals))
    SetupEnum empty ->
      absurd empty
    SetupTuple empty _ ->
      absurd empty
    SetupSlice empty ->
      absurd empty
    SetupArray () [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray () vs -> do
      vals <- V.mapM (resolveSetupVal cc mem env tyenv nameEnv) (V.fromList vs)
      let tp = Crucible.llvmValStorableType (V.head vals)
      return $ Crucible.LLVMValArray tp vals
    SetupField () v n -> do
         st <- sawCoreState sym
         let sc = saw_sc st
         fld <- exceptToFail sc $
                  do info <- resolveSetupValueInfo cc tyenv nameEnv v
                     recoverStructFieldInfo cc tyenv nameEnv v info n
         ptr <- resolveSetupVal cc mem env tyenv nameEnv v
         case ptr of
           Crucible.LLVMValInt blk off ->
             do delta <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) (Crucible.fiOffset fld))
                off'  <- W4.bvAdd sym off delta
                return (Crucible.LLVMValInt blk off')
           _ -> fail "resolveSetupVal: llvm_field requires pointer value"

    SetupElem () v i -> do
         st <- sawCoreState sym
         let sc = saw_sc st
         delta <- exceptToFail sc (resolveSetupElemOffset cc tyenv nameEnv v i)
         ptr <- resolveSetupVal cc mem env tyenv nameEnv v
         case ptr of
           Crucible.LLVMValInt blk off ->
             do delta' <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
                off' <- W4.bvAdd sym off delta'
                return (Crucible.LLVMValInt blk off')
           _ -> fail "resolveSetupVal: llvm_elem requires pointer value"
    SetupNull () ->
      Crucible.ptrToPtrVal <$> Crucible.mkNullPointer sym Crucible.PtrWidth
    SetupGlobal () name ->
      Crucible.ptrToPtrVal <$> Crucible.doResolveGlobal bak mem (L.Symbol $ Text.unpack name)
    SetupGlobalInitializer () name ->
      case Map.lookup (L.Symbol $ Text.unpack name)
                      (view Crucible.globalInitMap $ ccLLVMModuleTrans cc) of
        -- There was an error in global -> constant translation
        Just (_, Left e) -> fail e
        Just (_, Right (_, Just v)) ->
          let ?lc = lc
          in Crucible.constToLLVMVal @(Crucible.ArchWidth arch) bak mem v
        Just (_, Right (_, Nothing)) ->
          fail $ Text.unpack $ "resolveSetupVal: global has no initializer: " <> name
        Nothing ->
          fail $ Text.unpack $ "resolveSetupVal: global not found: " <> name
    SetupMux empty _ _ _ ->
      absurd empty


-- | Like 'resolveSetupVal', but specifically geared towards the needs of
-- fields within bitfields. This is very similar to calling 'resolveSetupVal'
-- on a 'SetupField', instead of computing an offset into the struct based off
-- of the /field's/ offset from the beginning of the struct, this computes an
-- offset based off of the overall /bitfield's/ offset from the beginning of
-- the struct. This is important because in order to impose conditions on
-- fields within bitfields, we must load/store the entire bitfield. The field's
-- offset may be larger than the bitfield's offset, so the former offset is not
-- suited for this purpose.
--
-- In addition to returning the resolved 'LLVMVal', this also returns the
-- 'BitfieldIndex' for the field within the bitfield. This ends up being useful
-- for call sites to this function so that they do not have to recompute it.
resolveSetupValBitfield ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Crucible.MemImpl Sym ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex LLVMAllocSpec ->
  Map AllocIndex Crucible.Ident ->
  SetupValue (LLVM arch) ->
  String ->
  IO (BitfieldIndex, LLVMVal)
resolveSetupValBitfield cc mem env tyenv nameEnv val fieldName =
  do let sym = cc^.ccSym
     st <- sawCoreState sym
     let sc = saw_sc st
     lval <- resolveSetupVal cc mem env tyenv nameEnv val
     bfIndex <- exceptToFail sc (resolveSetupBitfield cc tyenv nameEnv val fieldName)
     let delta = biFieldByteOffset bfIndex
     offsetLval <- case lval of
                     Crucible.LLVMValInt blk off ->
                       do deltaBV <- W4.bvLit sym (W4.bvWidth off) (Crucible.bytesToBV (W4.bvWidth off) delta)
                          off'    <- W4.bvAdd sym off deltaBV
                          return (Crucible.LLVMValInt blk off')
                     _ -> fail "resolveSetupValBitfield: expected a pointer value"
     return (bfIndex, offsetLval)

resolveTypedTerm ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  TypedTerm ->
  IO LLVMVal
resolveTypedTerm cc tm =
  case ttType tm of
    TypedTermSchema (Cryptol.Forall [] [] ty) ->
      resolveSAWTerm cc (Cryptol.evalValType mempty ty) (ttTerm tm)
    tp -> do
      let sym = cc ^. ccSym
      st <- sawCoreState sym
      let sc = saw_sc st
      ppOpts <- scGetPPOpts sc
      tp' <- prettyTypedTermType sc tp
      fail $ PPS.render ppOpts $ "resolveSetupVal: expected monomorphic" <+>
          "term; instead got term with type" <+> tp'

resolveSAWPred ::
  (?w4EvalTactic :: W4EvalTactic) =>
  LLVMCrucibleContext arch ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc =
  Common.resolveBoolTerm' (cc ^. ccSym) (cc ^. ccUninterp)
  Common.ResolveRewrite {
    Common.rrBasicSS = Just (cc ^. ccBasicSS),
    Common.rrWhat4Eval = doW4Eval ?w4EvalTactic
  }

resolveSAWSymBV ::
  (?w4EvalTactic :: W4EvalTactic, 1 <= w) =>
  LLVMCrucibleContext arch ->
  NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveSAWSymBV cc w =
  Common.resolveBitvectorTerm' (cc ^. ccSym) (cc ^. ccUninterp) w
  Common.ResolveRewrite {
    Common.rrBasicSS = Just (cc ^. ccBasicSS),
    Common.rrWhat4Eval = doW4Eval ?w4EvalTactic
  }

resolveSAWTerm ::
  (?w4EvalTactic :: W4EvalTactic, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  LLVMCrucibleContext arch ->
  Cryptol.TValue ->
  Term ->
  IO LLVMVal
resolveSAWTerm cc tp tm =
    case tp of
      Cryptol.TVBit ->
        fail "resolveSAWTerm: unimplemented type Bit (FIXME)"
      Cryptol.TVInteger ->
        fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
      Cryptol.TVIntMod _ ->
        fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
      Cryptol.TVFloat{} ->
        fail "resolveSAWTerm: unimplemented type Float e p (FIXME)"
      Cryptol.TVArray{} ->
        fail "resolveSAWTerm: unimplemented type Array a b (FIXME)"
      Cryptol.TVRational ->
        fail "resolveSAWTerm: unimplemented type Rational (FIXME)"

      Cryptol.TVSeq sz Cryptol.TVBit ->
        case someNat sz of
          Just (Some w)
            | Just LeqProof <- isPosNat w ->
              do v <- resolveSAWSymBV cc w tm
                 Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
          _ -> fail ("Invalid bitvector width: " ++ show sz)
      Cryptol.TVSeq sz tp' ->
        do st <- sawCoreState sym
           let sc = saw_sc st
           let cryenv = cc ^. ccCryptolEnv
           sz_tm <- scNat sc (fromIntegral sz)
           tp_tm <- translateType sc cryenv (Cryptol.tValTy tp')
           let f i = do i_tm <- scNat sc (fromIntegral i)
                        tm' <- scAt sc sz_tm tp_tm tm i_tm
                        resolveSAWTerm cc tp' tm'
           case toLLVMType dl tp' of
             Left e -> do
               ppopts <- scGetPPOpts sc
               fail $ PPS.render ppopts $
                   "In resolveSAWTerm:" <+> prettyToLLVMTypeErr e
             Right memTy -> do
               gt <- Crucible.toStorableType memTy
               Crucible.LLVMValArray gt . V.fromList <$> mapM f [ 0 .. (sz-1) ]
      Cryptol.TVStream _tp' ->
        fail "resolveSAWTerm: invalid infinite stream type"
      Cryptol.TVTuple tps ->
        do st <- sawCoreState sym
           let sc = saw_sc st
           ppopts <- scGetPPOpts sc
           tms <- mapM (scTupleSelector sc tm) [0 .. length tps - 1]
           vals <- zipWithM (resolveSAWTerm cc) tps tms
           storTy <-
             case toLLVMType dl tp of
               Left e ->
                   fail $ PPS.render ppopts $
                       "In resolveSAWTerm:" <+> prettyToLLVMTypeErr e
               Right memTy -> Crucible.toStorableType memTy
           fields <-
             case Crucible.storageTypeF storTy of
               Crucible.Struct fields -> return fields
               _ -> fail "resolveSAWTerm: impossible: expected struct"
           return (Crucible.LLVMValStruct (V.zip fields (V.fromList vals)))
      Cryptol.TVRec _flds ->
        fail "resolveSAWTerm: unimplemented record type (FIXME)"
      Cryptol.TVFun _ _ ->
        fail "resolveSAWTerm: invalid function type"
      Cryptol.TVNominal {} ->
        fail "resolveSAWTerm: invalid nominal type"
  where
    sym = cc^.ccSym
    dl = Crucible.llvmDataLayout (ccTypeCtx cc)

scPtrWidthBvNat ::
  (Crucible.HasPtrWidth (Crucible.ArchWidth arch), Integral a) =>
  LLVMCrucibleContext arch ->
  a ->
  IO Term
scPtrWidthBvNat cc n =
  do let sym = cc^.ccSym
     st <- sawCoreState sym
     let sc = saw_sc st
     w <- scNat sc $ natValue Crucible.PtrWidth
     scBvNat sc w =<< scNat sc (fromIntegral n)

data ToLLVMTypeErr = UnsupportedTranslation PPS.Doc | Impossible PPS.Doc

prettyToLLVMTypeErr :: ToLLVMTypeErr -> PPS.Doc
prettyToLLVMTypeErr =
  \case
    UnsupportedTranslation ty ->
        "SAW doesn't yet support translating Cryptol's" <+> ty <+>
            "type(s) into crucible-llvm's type system."
    Impossible ty ->
        "User error: It's impossible to store Cryptol" <+> ty <+>
            "values in crucible-llvm's memory model."

toLLVMType ::
  Crucible.DataLayout ->
  Cryptol.TValue ->
  Either ToLLVMTypeErr Crucible.MemType
toLLVMType dl tp =
  case tp of
    Cryptol.TVBit -> Left (UnsupportedTranslation "bit") -- FIXME
    Cryptol.TVInteger -> Left (UnsupportedTranslation "integer")
    Cryptol.TVIntMod _ -> Left (UnsupportedTranslation "integer-mod-n")
    Cryptol.TVFloat{} -> Left (UnsupportedTranslation "float")
    Cryptol.TVArray{} -> Left (UnsupportedTranslation "array")
    Cryptol.TVRational -> Left (UnsupportedTranslation "rational")

    Cryptol.TVSeq n Cryptol.TVBit
      | n > 0 -> Right (Crucible.IntType (fromInteger n))
      | otherwise -> Left (Impossible "infinite sequence")
    Cryptol.TVSeq n t -> do
      t' <- toLLVMType dl t
      let n' = fromIntegral n
      Right (Crucible.ArrayType n' t')
    Cryptol.TVStream _tp' -> Left (Impossible "stream")
    Cryptol.TVTuple tps -> do
      tps' <- mapM (toLLVMType dl) tps
      let si = Crucible.mkStructInfo dl False tps'
      return (Crucible.StructType si)
    Cryptol.TVRec _flds -> Left (UnsupportedTranslation "record")
    Cryptol.TVFun _ _ -> Left (Impossible "function")
    Cryptol.TVNominal {} -> Left (Impossible "nominal")

toLLVMStorageType ::
  forall w .
  Crucible.HasPtrWidth w =>
  PPS.Opts ->
  Crucible.DataLayout ->
  Cryptol.TValue ->
  IO Crucible.StorageType
toLLVMStorageType ppopts data_layout cryptol_type =
  case toLLVMType data_layout cryptol_type of
    Left e -> fail $ PPS.render ppopts $ prettyToLLVMTypeErr e
    Right memory_type -> Crucible.toStorableType @_ @w memory_type

-- FIXME: This struct-padding logic is already implemented in
-- crucible-llvm. Reimplementing it here is error prone and harder to
-- maintain.
mkFields ::
  Bool {- ^ @True@ = packed, @False@ = unpacked -} ->
  Crucible.DataLayout ->
  Crucible.Alignment ->
  Crucible.Bytes ->
  [Crucible.StorageType] ->
  [(Crucible.StorageType, Crucible.Bytes)]
mkFields _ _ _ _ [] = []
mkFields packed dl a off (ty : tys) =
  (ty, pad) : mkFields packed dl a' off' tys
  where
    end = off + Crucible.storageTypeSize ty
    off' = if packed then end else Crucible.padToAlignment end nextAlign
    pad = off' - end
    a' = max a (typeAlignment dl ty)
    nextAlign = case tys of
      [] -> a'
      (ty' : _) -> typeAlignment dl ty'


typeAlignment :: Crucible.DataLayout -> Crucible.StorageType -> Crucible.Alignment
typeAlignment dl ty =
  case Crucible.storageTypeF ty of
    Crucible.Bitvector bytes -> Crucible.integerAlignment dl (Crucible.bytesToBits bytes)
    Crucible.Float           -> fromJust (Crucible.floatAlignment dl 32)
    Crucible.Double          -> fromJust (Crucible.floatAlignment dl 64)
    Crucible.X86_FP80        -> fromJust (Crucible.floatAlignment dl 80)
    Crucible.Array _sz ty'   -> typeAlignment dl ty'
    Crucible.Struct flds     -> V.foldl max Crucible.noAlignment (fmap (typeAlignment dl . (^. Crucible.fieldVal)) flds)


equalValsPred ::
  LLVMCrucibleContext wptr ->
  LLVMVal ->
  LLVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 =
   fromMaybe (W4.falsePred sym) <$> Crucible.testEqual sym v1 v2

  where
  sym = cc^.ccSym


memArrayToSawCoreTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  LLVMCrucibleContext arch ->
  Crucible.EndianForm ->
  TypedTerm ->
  IO Term
memArrayToSawCoreTerm crucible_context endianess typed_term = do
  let sym = crucible_context ^. ccSym
  let data_layout = Crucible.llvmDataLayout $ ccTypeCtx crucible_context
  st <- sawCoreState sym
  let sc = saw_sc st
  ppopts <- scGetPPOpts sc
  let cryenv = crucible_context ^. ccCryptolEnv

  byte_type_term <- translateType sc cryenv $ Cryptol.tValTy $ Cryptol.TVSeq 8 Cryptol.TVBit
  offset_type_term <- scBitvector sc $ natValue ?ptrWidth

  let updateArray :: Natural -> Term -> StateT Term IO ()
      updateArray offset byte_term = do
        ptr_width_term <- liftIO $ scNat sc $ natValue ?ptrWidth
        offset_term <- liftIO $ scBvNat sc ptr_width_term =<< scNat sc offset
        array_term <- get
        updated_array_term <- liftIO $
          scArrayUpdate sc offset_type_term byte_type_term array_term offset_term byte_term
        put updated_array_term
      setBytes :: Cryptol.TValue -> Term -> Crucible.Bytes -> StateT Term IO ()
      setBytes cryptol_type saw_term offset = case cryptol_type of
        Cryptol.TVSeq size Cryptol.TVBit
          | (byte_count, 0) <- quotRem (fromInteger size) 8 ->
            if byte_count > 1
              then forM_ [0 .. (byte_count - 1)] $ \byte_index -> do
                bit_type_term <- liftIO $ translateType
                  sc
                  cryenv
                  (Cryptol.tValTy Cryptol.TVBit)
                byte_index_term <- liftIO $ scNat sc $ byte_index * 8
                byte_size_term <- liftIO $ scNat sc 8
                remaining_bits_size_term <- liftIO $ scNat sc $
                  (byte_count - byte_index - 1) * 8
                saw_byte_term <- liftIO $ scSlice
                  sc
                  bit_type_term
                  byte_index_term
                  byte_size_term
                  remaining_bits_size_term
                  saw_term

                let byte_storage_index = case endianess of
                      Crucible.BigEndian -> byte_index
                      Crucible.LittleEndian -> byte_count - byte_index - 1
                let byte_offset = ((fromIntegral offset) + (fromIntegral byte_storage_index))
                updateArray byte_offset saw_byte_term
            else
              updateArray (fromIntegral offset) saw_term
          | otherwise -> fail $ "unexpected bit count: " ++ show size

        Cryptol.TVSeq size element_cryptol_type -> do
          element_storage_size <- liftIO $
            Crucible.storageTypeSize <$> toLLVMStorageType ppopts
              data_layout
              element_cryptol_type

          forM_ [0 .. (size - 1)] $ \element_index -> do
            size_term <- liftIO $ scNat sc $ fromInteger size
            elem_type_term <- liftIO $ translateType
              sc
              cryenv
              (Cryptol.tValTy element_cryptol_type)
            index_term <- liftIO $ scNat sc $ fromInteger element_index
            inner_saw_term <- liftIO $ scAt
              sc
              size_term
              elem_type_term
              saw_term index_term
            setBytes
              element_cryptol_type
              inner_saw_term
              (offset + (fromInteger element_index) * element_storage_size)

        Cryptol.TVTuple tuple_element_cryptol_types -> do
          (Crucible.Struct field_storage_types) <- liftIO $
            Crucible.storageTypeF <$> toLLVMStorageType ppopts data_layout cryptol_type

          V.forM_ (V.izipWith (,,) field_storage_types (V.fromList tuple_element_cryptol_types)) $
            \(field_index, field_storage_type, tuple_element_cryptol_type) -> do
              inner_saw_term <- liftIO $ scTupleSelector
                sc
                saw_term
                field_index
              setBytes
                tuple_element_cryptol_type
                inner_saw_term
                (offset + (Crucible.fieldOffset field_storage_type))

        _ -> fail $ "unexpected cryptol type: " ++ show cryptol_type

  case ttType typed_term of
    TypedTermSchema (Cryptol.Forall [] [] cryptol_type) -> do
      let evaluated_type = Cryptol.evalValType mempty cryptol_type
      fresh_array_const <- scFreshVariable sc "arr"
        =<< scArrayType sc offset_type_term byte_type_term
      execStateT
        (setBytes evaluated_type (ttTerm typed_term) 0)
        fresh_array_const

    _ -> do
      typed_term' <- ppTypedTerm sc typed_term
      fail $ Text.unpack $ "Expected monomorphic typed term: " <> typed_term'
