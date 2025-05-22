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
{-# Language TypeOperators #-}
{-# Language ViewPatterns #-}

module Mir.Cryptol
where

import Control.Lens (use, (^.), (^?), _Wrapped, ix)
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Data.Functor.Const
import Data.IORef
import qualified Data.Kind as Kind
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
import qualified What4.Partial as W4

import Cryptol.TypeCheck.AST as Cry
import Cryptol.Utils.Ident as Cry
import Cryptol.Utils.PP as Cry

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import Crux

import Mir.DefId
import Mir.Generator (CollectionState, collection, MirHandle(..))
import qualified Mir.Generator as M
import Mir.Intrinsics
import qualified Mir.Mir as M
import qualified Mir.PP as M
import Mir.Overrides (getString)

import qualified CryptolSAWCore.Prelude as SAW
import qualified CryptolSAWCore.CryptolEnv as SAW
import qualified SAWCore.SharedTerm as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW
import qualified SAWCore.Recognizer as SAW (asExtCns)
import qualified CryptolSAWCore.TypedTerm as SAW

import SAWCentral.Crucible.MIR.TypeShape

import Mir.Compositional.Convert
import Mir.Compositional.DefId (hasInstPrefix)


cryptolOverrides ::
    forall sym bak p t st fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    Maybe (SomeOnlineSolver sym bak) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
cryptolOverrides _symOnline cs name cfg

  | hasInstPrefix ["crucible", "cryptol", "load"] explodedName
  , Empty :> MirSliceRepr :> MirSliceRepr
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

  | hasInstPrefix ["crucible", "cryptol", "override_"] explodedName
  , Empty :> UnitRepr :> MirSliceRepr :> MirSliceRepr <- cfgArgTypes cfg
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

  | hasInstPrefix ["crucible", "cryptol", "munge"] explodedName
  , Empty :> tpr <- cfgArgTypes cfg
  , tpr' <- cfgReturnType cfg
  , Just Refl <- testEquality tpr tpr'
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_munge" tpr $ do
        let tyArg = cs ^? collection . M.intrinsics . ix (textId name) .
                M.intrInst . M.inSubsts . _Wrapped . ix 0
        shp <- case tyArg of
            Just ty -> return $ tyToShapeEq (cs ^. collection) ty tpr
            _ -> error $ "impossible: missing type argument for cryptol::munge()"

        sym <- getSymInterface
        RegMap (Empty :> RegEntry _ rv) <- getOverrideArgs
        liftIO $ munge sym shp rv

  | otherwise = Nothing
  where
    explodedName = textIdKey name

cryptolLoad ::
    forall sym p t st fs rtp a r tp .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection ->
    M.FnSig ->
    TypeRepr tp ->
    RegValue sym MirSlice ->
    RegValue sym MirSlice ->
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
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    RegValue sym MirSlice ->
    String ->
    OverrideSim (p sym) sym MIR rtp a r Text
loadString str desc = getString str >>= \x -> case x of
    Just s -> return s
    Nothing -> fail $ desc ++ " must not be symbolic"


cryptolOverride ::
    forall sym p t st fs rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    M.Collection ->
    MirHandle ->
    RegValue sym MirSlice ->
    RegValue sym MirSlice ->
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
        OverrideSim (p sym) sym MIR rtp args r (RegValue sym ret)
    }

-- | Load a Cryptol function, returning an `OverrideSim` action that can be
-- used to run the function.
loadCryptolFunc ::
    forall sym p t st fs rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
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
        SAW.InputText name "<string>" 1 1

    case typecheckFnSig sig (toListFC Some argShps) (Some retShp) (SAW.ttType tt) of
        Left err -> fail $ "error loading " ++ show name ++ ": " ++ err
        Right () -> return ()

    let fnName = "cryptol_" <> modulePath <> "_" <> name
    return $ LoadedCryptolFunc argShps retShp $
        cryptolRun sc (Text.unpack fnName) argShps retShp (SAW.ttTerm tt)

  where
    listToCtx :: forall k0 (f0 :: k0 -> Kind.Type). [Some f0] -> Some (Assignment f0)
    listToCtx xs0 = go xs0 (Some Empty)
      where
        go :: forall k (f :: k -> Kind.Type). [Some f] -> Some (Assignment f) -> Some (Assignment f)
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
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
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
    liftIO $ termToReg sym sc w4VarMap appTerm retShp

munge :: forall sym t st fs tp0.
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    sym -> TypeShape tp0 -> RegValue sym tp0 -> IO (RegValue sym tp0)
munge sym shp0 rv0 = do
    sc <- SAW.mkSharedContext
    SAW.scLoadPreludeModule sc

    scs <- SAW.newSAWCoreState sc
    visitCache <- W4.newIdxCache
    w4VarMapRef <- newIORef Map.empty

    let eval' :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval' x = SAW.toSC sym scs x
        eval :: forall tp. W4.Expr t tp -> IO SAW.Term
        eval x = do
            -- When translating W4 vars to SAW `ExtCns`s, also record the
            -- reverse mapping into `w4VarMapRef` so the reverse translation
            -- can be done later on.
            visitExprVars visitCache x $ \var -> do
                let expr = W4.BoundVarExpr var
                term <- eval' expr
                ec <- case SAW.asExtCns term of
                    Just ec -> return ec
                    Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
                modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some expr)
            eval' x
        uneval :: TypeShape (BaseToType btp) -> SAW.Term -> IO (W4.Expr t btp)
        uneval shp t = do
            w4VarMap <- readIORef w4VarMapRef
            termToReg sym sc w4VarMap t shp

    let go :: forall tp. TypeShape tp -> RegValue sym tp -> IO (RegValue sym tp)
        go (UnitShape _) () = return ()
        go shp@(PrimShape _ _) expr = eval expr >>= uneval shp
        go (TupleShape _ _ flds) rvs = goFields flds rvs
        go (ArrayShape _ _ shp) vec = case vec of
            MirVector_Vector v -> MirVector_Vector <$> mapM (go shp) v
            MirVector_PartialVector pv -> do
                pv' <- forM pv $ \p -> do
                    rv <- readMaybeType sym "vector element" (shapeType shp) p
                    W4.justPartExpr sym <$> go shp rv
                return $ MirVector_PartialVector pv'
            MirVector_Array _ -> error $ "munge: MirVector_Array NYI"
        go (StructShape _ _ flds) (AnyValue tpr rvs)
            | StructRepr ctx <- tpr
            , Just Refl <- testEquality (fmapFC fieldShapeType flds) ctx =
                AnyValue tpr <$> goFields flds rvs
            | otherwise = error $  "munge: StructShape AnyValue with NYI TypeRepr " ++ show tpr
        go (TransparentShape _ shp) rv = go shp rv
        go (EnumShape _ _ _ _ _) _ =
            error "Enums not currently supported in overrides"
        go (FnPtrShape _ _ _) _ =
            error "Function pointers not currently supported in overrides"
        -- TODO: RefShape
        go (SliceShape _ ty mutbl tpr) (Ctx.Empty Ctx.:> RV ref Ctx.:> RV len) = do
            let (refShp, lenShp) = sliceShapeParts ty mutbl tpr
            ref' <- go refShp ref
            len' <- go lenShp len
            pure $ Ctx.Empty Ctx.:> RV ref' Ctx.:> RV len'
        go shp _ = error $ "munge: " ++ show (shapeType shp) ++ " NYI"

        goFields :: forall ctx.
            Assignment FieldShape ctx ->
            Assignment (RegValue' sym) ctx ->
            IO (Assignment (RegValue' sym) ctx)
        goFields Empty Empty = return Empty
        goFields (flds :> fld) (rvs :> RV rv) = do
            rvs' <- goFields flds rvs
            rv' <- goField fld rv
            return $ rvs' :> RV rv'

        goField :: forall tp. FieldShape tp -> RegValue sym tp -> IO (RegValue sym tp)
        goField (ReqField shp) rv = go shp rv
        goField (OptField shp) rv = do
            rv' <- readMaybeType sym "field" (shapeType shp) rv
            W4.justPartExpr sym <$> go shp rv'

    go shp0 rv0


typecheckFnSig ::
    M.FnSig ->
    [Some TypeShape] ->
    Some TypeShape ->
    SAW.TypedTermType ->
    Either String ()
typecheckFnSig fnSig argShps0 retShp (SAW.TypedTermSchema sch@(Cry.Forall [] [] ty0)) =
    go 0 argShps0 ty0
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
            zipWithM_ (\(Some fld) ty' -> goOneField desc fld ty') flds' tys
          | otherwise -> typeErr desc shp ty $
            "tuple size " ++ show n ++ " does not match " ++ show (Ctx.sizeInt $ Ctx.size flds)
        (ArrayShape (M.TyArray _ n) _ shp',
            Cry.TCon (Cry.TC Cry.TCSeq) [
                Cry.tNoUser -> Cry.TCon (Cry.TC (Cry.TCNum n')) [],
                ty'])
          | fromIntegral n == n' -> goOne desc shp' ty'
          | otherwise -> typeErr desc shp' ty $
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

typecheckFnSig _ _ _ (SAW.TypedTermSchema sch) = Left $
    "polymorphic Cryptol functions are not supported (got signature: " ++
        show (Cry.pp sch) ++ ")"

typecheckFnSig _ _ _ ttt = Left $
    "internal error: unsupported TypedTermType variant: " ++ show ttt
