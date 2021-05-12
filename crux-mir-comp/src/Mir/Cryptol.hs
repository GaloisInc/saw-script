{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language KindSignatures #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language PolyKinds #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language ViewPatterns #-}

module Mir.Cryptol
where

import Control.Lens (use, (^.), (^?), _Wrapped, ix)
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.Functor.Const
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text

import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC

import qualified What4.Expr.Builder as W4

import Cryptol.TypeCheck.AST as Cry
import Cryptol.Utils.Ident as Cry
import Cryptol.Utils.PP as Cry

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import Crux
import Crux.Types

import Mir.DefId
import Mir.Generator (CollectionState, collection, MirHandle(..))
import qualified Mir.Generator as M
import Mir.Intrinsics
import qualified Mir.Mir as M
import qualified Mir.PP as M
import Mir.Overrides (getString)

import qualified Verifier.SAW.Cryptol.Prelude as SAW
import qualified Verifier.SAW.CryptolEnv as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.TypedTerm as SAW

import Mir.Compositional.Convert

import Debug.Trace


cryptolOverrides ::
    forall sym p t st fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    Maybe (SomeOnlineSolver sym) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
cryptolOverrides _symOnline cs name cfg

  | (normDefId "crucible::cryptol::load" <> "::_inst") `Text.isPrefixOf` name
  , Empty
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      <- cfgArgTypes cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_load" (cfgReturnType cfg) $ do
        let tyArg = cs ^? collection . M.intrinsics . ix (textId name) .
                M.intrInst . M.inSubsts . _Wrapped . ix 0
        sig <- case tyArg of
            Just (M.TyFnPtr sig) -> return sig
            _ -> error $ "expected TyFnPtr argument, but got " ++ show tyArg

        RegMap (Empty :> RegEntry _tpr modulePathStr :> RegEntry _tpr' nameStr) <- getOverrideArgs
        cryptolLoad (cs ^. collection) sig (cfgReturnType cfg) modulePathStr nameStr

  | (normDefId "crucible::cryptol::override_" <> "::_inst") `Text.isPrefixOf` name
  , Empty
      :> UnitRepr
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      :> MirSliceRepr (BVRepr (testEquality (knownNat @8) -> Just Refl))
      <- cfgArgTypes cfg
  , UnitRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_override_" UnitRepr $ do
        let tyArg = cs ^? collection . M.intrinsics . ix (textId name) .
                M.intrInst . M.inSubsts . _Wrapped . ix 0
        fnDefId <- case tyArg of
            Just (M.TyFnDef defId) -> return defId
            _ -> error $ "expected TyFnDef argument, but got " ++ show tyArg
        mh <- case cs ^? M.handleMap . ix fnDefId of
            Just mh -> return mh
            _ -> error $ "failed to get function definition for " ++ show fnDefId

        RegMap (Empty
          :> RegEntry _ ()
          :> RegEntry _tpr modulePathStr
          :> RegEntry _tpr' nameStr) <- getOverrideArgs
        cryptolOverride (cs ^. collection) mh modulePathStr nameStr

  | otherwise = Nothing


cryptolLoad ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    M.Collection ->
    M.FnSig ->
    TypeRepr tp ->
    RegValue sym (MirSlice (BVType 8)) ->
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim (p sym) sym MIR rtp a r (RegValue sym tp)
cryptolLoad col sig (FunctionHandleRepr argsCtx retTpr) modulePathStr nameStr = do
    modulePath <- loadString modulePathStr "cryptol::load module path"
    name <- loadString nameStr "cryptol::load function name"
    LoadedCryptolFunc argShps retShp run <- loadCryptolFunc col sig modulePath name

    let argsCtx' = fmapFC shapeType argShps
    let retTpr' = shapeType retShp
    (Refl, Refl) <- case (testEquality argsCtx argsCtx', testEquality retTpr retTpr') of
        (Just x, Just y) -> return (x, y)
        _ -> fail $ "signature mismatch: " ++ show (argsCtx', retTpr') ++ " != " ++
            show (argsCtx, retTpr)

    halloc <- simHandleAllocator <$> use stateContext
    let fnName = "cryptol_" <> modulePath <> "_" <> name
    fh <- liftIO $ mkHandle' halloc (fromString $ Text.unpack fnName) argsCtx retTpr
    bindFnHandle fh $ UseOverride $ mkOverride' (handleName fh) (handleReturnType fh) $
        run

    return $ HandleFnVal fh

cryptolLoad _ _ tpr _ _ = fail $ "cryptol::load: bad function type " ++ show tpr

loadString ::
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    RegValue sym (MirSlice (BVType 8)) ->
    String ->
    OverrideSim (p sym) sym MIR rtp a r Text
loadString str desc = getString str >>= \x -> case x of
    Just s -> return s
    Nothing -> fail $ desc ++ " must not be symbolic"


cryptolOverride ::
    forall sym p t st fs rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    M.Collection ->
    MirHandle ->
    RegValue sym (MirSlice (BVType 8)) ->
    RegValue sym (MirSlice (BVType 8)) ->
    OverrideSim (p sym) sym MIR rtp a r ()
cryptolOverride col (MirHandle _ sig fh) modulePathStr nameStr = do
    modulePath <- loadString modulePathStr "cryptol::load module path"
    name <- loadString nameStr "cryptol::load function name"
    LoadedCryptolFunc argShps retShp run <- loadCryptolFunc col sig modulePath name

    let argsCtx = handleArgTypes fh
    let retTpr = handleReturnType fh
    let argsCtx' = fmapFC shapeType argShps
    let retTpr' = shapeType retShp
    (Refl, Refl) <- case (testEquality argsCtx argsCtx', testEquality retTpr retTpr') of
        (Just x, Just y) -> return (x, y)
        _ -> fail $ "signature mismatch: " ++ show (argsCtx', retTpr') ++ " != " ++
            show (argsCtx, retTpr)

    bindFnHandle fh $ UseOverride $ mkOverride' (handleName fh) (handleReturnType fh) $
        run


data LoadedCryptolFunc sym = forall args ret . LoadedCryptolFunc
    { _lcfArgs :: Assignment TypeShape args
    , _lcfRet :: TypeShape ret
    , _lcfRun :: forall p rtp r.
        HasModel p => OverrideSim (p sym) sym MIR rtp args r (RegValue sym ret)
    }

-- | Load a Cryptol function, returning an `OverrideSim` action that can be
-- used to run the function.
loadCryptolFunc ::
    forall sym p t st fs rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    M.Collection ->
    M.FnSig ->
    Text ->
    Text ->
    OverrideSim (p sym) sym MIR rtp a r (LoadedCryptolFunc sym)
loadCryptolFunc col sig modulePath name = do
    Some argShps <- return $ listToCtx $ map (tyToShape col) (sig ^. M.fsarg_tys)
    Some retShp <- return $ tyToShape col (sig ^. M.fsreturn_ty)

    -- TODO share a single SharedContext across all calls
    sc <- liftIO $ SAW.mkSharedContext
    liftIO $ SAW.scLoadPreludeModule sc
    liftIO $ SAW.scLoadCryptolModule sc
    let ?fileReader = BS.readFile
    ce <- liftIO $ SAW.initCryptolEnv sc
    let modName = Cry.textToModName modulePath
    ce' <- liftIO $ SAW.importModule sc ce (Right modName) Nothing SAW.PublicAndPrivate Nothing
    -- (m, _ce') <- liftIO $ SAW.loadCryptolModule sc ce (Text.unpack modulePath)
    -- tt <- liftIO $ SAW.lookupCryptolModule m (Text.unpack name)
    tt <- liftIO $ SAW.parseTypedTerm sc ce' $
        SAW.InputText (Text.unpack name) "<string>" 1 1

    case typecheckFnSig sig (toListFC Some argShps) (Some retShp) (SAW.ttSchema tt) of
        Left err -> fail $ "error loading " ++ show name ++ ": " ++ err
        Right () -> return ()

    let fnName = "cryptol_" <> modulePath <> "_" <> name
    return $ LoadedCryptolFunc argShps retShp $
        cryptolRun sc (Text.unpack fnName) argShps retShp (SAW.ttTerm tt)

  where
    listToCtx :: forall k (f :: k -> *). [Some f] -> Some (Assignment f)
    listToCtx xs = go xs (Some Empty)
      where
        go :: forall k (f :: k -> *). [Some f] -> Some (Assignment f) -> Some (Assignment f)
        go [] acc = acc
        go (Some x : xs) (Some acc) = go xs (Some $ acc :> x)

{-
    halloc <- simHandleAllocator <$> use stateContext
    let fnName = "cryptol_" ++ modulePath ++ "_" ++ name
    fh <- liftIO $ mkHandle' halloc (fromString fnName) argsCtx retTpr
    bindFnHandle fh $ UseOverride $ mkOverride' (handleName fh) (handleReturnType fh) $
-}



cryptolRun ::
    forall sym p t st fs rtp r args ret .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs, HasModel p) =>
    SAW.SharedContext ->
    String ->
    Assignment TypeShape args ->
    TypeShape ret ->
    SAW.Term ->
    OverrideSim (p sym) sym MIR rtp args r (RegValue sym ret)
cryptolRun sc name argShps retShp funcTerm = do
    sym <- getSymInterface

    w4VarMapRef <- liftIO $ newIORef (Map.empty :: Map SAW.VarIndex (Some (W4.Expr t)))

    RegMap argsCtx <- getOverrideArgs
    argTermsCtx <- Ctx.zipWithM
        (\shp (RegEntry _ val) ->
            Const <$> regToTerm sym sc name w4VarMapRef shp val)
        argShps argsCtx
    let argTerms = toListFC getConst argTermsCtx
    appTerm <- liftIO $ SAW.scApplyAll sc funcTerm argTerms

    w4VarMap <- liftIO $ readIORef w4VarMapRef
    rv <- liftIO $ termToReg sym sc w4VarMap appTerm retShp
    return rv


typecheckFnSig ::
    M.FnSig ->
    [Some TypeShape] ->
    Some TypeShape ->
    Cry.Schema ->
    Either String ()
typecheckFnSig fnSig argShps retShp sch@(Cry.Forall [] [] ty) = go 0 argShps ty
  where
    go :: Int -> [Some TypeShape] -> Cry.Type -> Either String ()
    go _ [] ty | Some retShp' <- retShp = goOne "return value" retShp' ty
    go i (Some argShp : argShps) (Cry.tNoUser -> Cry.TCon (Cry.TC Cry.TCFun) [argTy, ty']) = do
        goOne ("argument " ++ show i) argShp argTy
        go (i + 1) argShps ty'
    go i argShps _ = Left $
        "not enough arguments: Cryptol function signature " ++ show (Cry.pp sch) ++
        " has " ++ show i ++ " arguments, but Rust signature " ++ M.fmt fnSig ++
        " requires " ++ show (i + length argShps)

    goOne :: forall tp. String -> TypeShape tp -> Cry.Type -> Either String ()
    goOne desc shp ty = case (shp, ty) of
        (_, Cry.TUser _ _ ty') -> goOne desc shp ty'
        (UnitShape _, Cry.TCon (Cry.TC (Cry.TCTuple 0)) []) -> Right ()
        (PrimShape _ BaseBoolRepr, Cry.TCon (Cry.TC Cry.TCBit) []) -> Right ()
        (PrimShape _ (BaseBVRepr w),
            Cry.TCon (Cry.TC Cry.TCSeq) [
                Cry.tNoUser -> Cry.TCon (Cry.TC (Cry.TCNum n)) [],
                Cry.tNoUser -> Cry.TCon (Cry.TC Cry.TCBit) []])
          | fromIntegral (intValue w) == n -> Right ()
          | otherwise -> typeErr desc shp ty $
            "bitvector width " ++ show n ++ " does not match " ++ show (intValue w)
        (TupleShape _ _ flds, Cry.TCon (Cry.TC (Cry.TCTuple n)) tys)
          | Ctx.sizeInt (Ctx.size flds) == n -> do
            let flds' = toListFC Some flds
            zipWithM_ (\(Some fld) ty -> goOneField desc fld ty) flds' tys
          | otherwise -> typeErr desc shp ty $
            "tuple size " ++ show n ++ " does not match " ++ show (Ctx.sizeInt $ Ctx.size flds)
        (ArrayShape (M.TyArray _ n) _ shp,
            Cry.TCon (Cry.TC Cry.TCSeq) [
                Cry.tNoUser -> Cry.TCon (Cry.TC (Cry.TCNum n')) [],
                ty'])
          | fromIntegral n == n' -> goOne desc shp ty'
          | otherwise -> typeErr desc shp ty $
            "array length " ++ show n' ++ " does not match " ++ show n
        _ -> typeErr desc shp ty ""

    typeErr :: forall tp. String -> TypeShape tp -> Cry.Type -> String -> Either String ()
    typeErr desc shp ty extra = Left $
            "type mismatch in " ++ desc ++ ": Cryptol type " ++ show (Cry.pp ty) ++
            " does not match Rust type " ++ M.fmt (shapeMirTy shp) ++
            (if not (null extra) then ": " ++ extra else "")

    goOneField :: forall tp. String -> FieldShape tp -> Cry.Type -> Either String ()
    goOneField desc (OptField shp) ty = goOne desc shp ty
    goOneField desc (ReqField shp) ty = goOne desc shp ty

typecheckFnSig _ _ _ sch = Left $
    "polymorphic Cryptol functions are not supported (got signature: " ++
        show (Cry.pp sch) ++ ")"
