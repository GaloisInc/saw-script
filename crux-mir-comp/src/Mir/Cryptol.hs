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
import Data.IORef
import qualified Data.Kind as Kind
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Set as Set
import Data.Functor.Const

import Data.Parameterized.Context (pattern Empty, pattern (:>), Assignment)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.TraversableFC

import qualified What4.Expr.Builder as W4
import qualified What4.Partial as W4
import qualified What4.Interface as W4
import qualified Data.BitVector.Sized as BV

import Cryptol.TypeCheck.AST as Cry
import qualified Cryptol.TypeCheck.Subst as Cry
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

import qualified CryptolSAWCore.CryptolEnv as SAW
import qualified SAWCore.SharedTerm as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW
import qualified SAWCore.Recognizer as SAW (asVariable)
import qualified CryptolSAWCore.TypedTerm as SAW

import SAWCentral.Crucible.MIR.TypeShape

import Mir.Compositional.Convert
import Mir.Compositional.DefId (hasInstPrefix)
import Mir.Compositional.State


cryptolOverrides ::
    forall sym bak p t fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
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

  | ["crucible","cryptol","uninterp"] == explodedName
  , Empty :> MirSliceRepr <- cfgArgTypes cfg
  , UnitRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "cryptol_uninterp" UnitRepr $
    do RegMap (Empty :> RegEntry _tpr' nameStr) <- getOverrideArgs
       fun <- loadString nameStr "cryptol::uninterp function name"
       sym <- getSymInterface
       let state = sym ^. W4.userState
       liftIO (modifyIORef (mirKeepUninterp state) (Set.insert fun))


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
    forall sym p t fs rtp a r tp .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
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
    (IsSymInterface sym, sym ~ MirSym t fs) =>
    RegValue sym MirSlice ->
    String ->
    OverrideSim (p sym) sym MIR rtp a r Text
loadString str desc = getString str >>= \x -> case x of
    Just s -> return s
    Nothing -> fail $ desc ++ " must not be symbolic"


cryptolOverride ::
    forall sym p t fs rtp a r .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
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
    forall sym p t fs rtp a r .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
    M.Collection ->
    M.FnSig ->
    Text ->
    Text ->
    OverrideSim (p sym) sym MIR rtp a r (LoadedCryptolFunc sym)
loadCryptolFunc col sig modulePath name = do
    Some argShps <- return $ listToCtx $ map (tyToShape col) (sig ^. M.fsarg_tys)
    Some retShp <- return $ tyToShape col (sig ^. M.fsreturn_ty)

    sym <- getSymInterface
    let mirState = sym ^. W4.userState
    let sc = mirSharedContext mirState
    let ?fileReader = BS.readFile
    ce <- liftIO (readIORef (mirCryEnv mirState))
    let modName = Cry.textToModName modulePath
    ce' <- liftIO $ SAW.importModule sc ce (Right modName) Nothing SAW.PublicAndPrivate Nothing
    liftIO (writeIORef (mirCryEnv mirState) ce')
    -- (m, _ce') <- liftIO $ SAW.loadCryptolModule sc ce (Text.unpack modulePath)
    -- tt <- liftIO $ SAW.extractDefFromCryptolModule m (Text.unpack name)
    tt <- liftIO $ SAW.parseTypedTerm sc ce' $
        SAW.InputText name "<string>" 1 1

    args <-
      case typecheckFnSig sig argShps (Some retShp) (SAW.ttType tt) of
        Left err -> fail $ "error loading " ++ show name ++ ": " ++ err
        Right ok -> pure ok

    let fnName = "cryptol_" <> modulePath <> "_" <> name
    return $ LoadedCryptolFunc argShps retShp $
        cryptolRun (Text.unpack fnName) args retShp (SAW.ttTerm tt)

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
    forall sym p t fs rtp r args ret .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
    String ->
    CryFunArgs args ->
    TypeShape ret ->
    SAW.Term ->
    OverrideSim (p sym) sym MIR rtp args r (RegValue sym ret)
cryptolRun name (CryFunArgs (CryFunArgs' tpArgs ctrs normArgs)) retShp funcTerm = do
    let tpArgsSize      = Ctx.size tpArgs
        normArgsSize    = Ctx.size normArgs

    sym <- getSymInterface

    w4VarMapRef <- liftIO $ newIORef (Map.empty :: Map SAW.VarIndex (Some (W4.Expr t)))

    RegMap argsCtx <- getOverrideArgs
    let sc = mirSharedContext (sym ^. W4.userState)
    let
      getSizeArg ::
        forall ty. CryFunTArg ty -> RegEntry sym ty ->
        OverrideSim (p sym) sym MIR rtp args r (Const ((Cry.TParam, Cry.Type), SAW.Term) ty)
      getSizeArg (CryFunTArg tp) (RegEntry _ val) =
        case BV.asUnsigned <$> W4.asBV val of
          Just conc ->
            liftIO $
              do
                i    <- SAW.scNat sc (fromInteger conc)
                term <- SAW.scGlobalApply sc "Cryptol.TCNum" [i]
                pure (Const ((tp, Cry.tNum conc), term))
          Nothing ->
            do
              let nm = show (maybe "?" pp (Cry.tpName tp)) -- the "?" shouldn't happen
              fail ("Size parameter " ++ nm ++ " is not a concrete number")

    (tpBinds,tpTerms) <-
      unzip . toListFC getConst <$>
      Ctx.zipWithM getSizeArg tpArgs (Ctx.take tpArgsSize normArgsSize argsCtx)
    let su     = Cry.listParamSubst tpBinds
        bad    = filter (not . Cry.pIsTrue . Cry.apSubst su) ctrs
    unless (null bad) $ fail $ unlines $
      "Unsatisfied size parameter constraints:" :
      [ "  " ++ show (pp b) | b <- bad ]

    let 
      getNormArg ::
        forall ty. CryFunArg ty -> RegEntry sym ty ->
        OverrideSim (p sym) sym MIR rtp args r (Const SAW.Term ty)
      getNormArg (CryFunArg ada shp) (RegEntry _ val) =
        case traverse (Cry.tIsNum . Cry.apSubst su) ada of
          Just adaI -> Const <$> regToTermWithAdapt sym sc name w4VarMapRef adaI shp val
          Nothing   -> fail "Invalid size parameter" -- Shouldn't happen

    argTerms <-
      toListFC getConst <$>
      Ctx.zipWithM getNormArg normArgs (Ctx.drop tpArgsSize normArgsSize argsCtx)


    let allTerms = tpTerms ++ argTerms
    appTerm  <- liftIO (SAW.scApplyAll sc funcTerm allTerms)
    w4VarMap <- liftIO (readIORef w4VarMapRef)
    liftIO $ termToReg sym w4VarMap appTerm retShp

munge :: forall sym t fs tp0.
    (IsSymInterface sym, sym ~ MirSym t fs) =>
    sym -> TypeShape tp0 -> RegValue sym tp0 -> IO (RegValue sym tp0)
munge sym shp0 rv0 = do
    let scs = mirSAWCoreState (sym ^. W4.userState)

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
                ec <- case SAW.asVariable term of
                    Just ec -> return ec
                    Nothing -> error "eval on BoundVarExpr produced non-ExtCns?"
                modifyIORef w4VarMapRef $ Map.insert (SAW.ecVarIndex ec) (Some expr)
            eval' x
        uneval :: TypeShape (BaseToType btp) -> SAW.Term -> IO (W4.Expr t btp)
        uneval shp t = do
            w4VarMap <- readIORef w4VarMapRef
            termToReg sym w4VarMap t shp

    let go :: forall tp. TypeShape tp -> RegValue sym tp -> IO (RegValue sym tp)
        go (UnitShape _) () = return ()
        go shp@(PrimShape _ _) expr = eval expr >>= uneval shp
        go (TupleShape _ elems) ag =
            traverseMirAggregate sym elems ag $ \_off _sz shp rv -> go shp rv
        go (ArrayShape _ _ shp) vec = case vec of
            MirVector_Vector v -> MirVector_Vector <$> mapM (go shp) v
            MirVector_PartialVector pv -> do
                pv' <- forM pv $ \p -> do
                    let rv = readMaybeType sym "vector element" (shapeType shp) p
                    W4.justPartExpr sym <$> go shp rv
                return $ MirVector_PartialVector pv'
            MirVector_Array _ -> error $ "munge: MirVector_Array NYI"
        go (StructShape _ _ flds) rvs = goFields flds rvs
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
            let rv' = readMaybeType sym "field" (shapeType shp) rv
            W4.justPartExpr sym <$> go shp rv'

    go shp0 rv0


-- | Information about a typechecked Cyrptol import
data CryFunArgs args where
  CryFunArgs :: CryFunArgs' tps ps -> CryFunArgs (tps <+> ps)

-- | Information about a typechecked Cyrptol import
data CryFunArgs' tps ps where
  CryFunArgs' ::
    Assignment CryFunTArg tps {- ^ Size polymorphic parameters needed by the function -} ->
    [Cry.Prop] {- ^ Constraints on the parameters -} ->
    Assignment CryFunArg ps {- ^ Dynamic checks to perform on the ordinary function arguments -} ->
    CryFunArgs' tps ps


noCryFunArgs :: [Cry.Prop] -> CryFunArgs' EmptyCtx EmptyCtx
noCryFunArgs ctrs = CryFunArgs' Ctx.empty ctrs Ctx.empty

addCryFunTArg ::
  CryFunArgs' tps ps -> CryFunTArg t -> CryFunArgs' (tps ::> t) ps
addCryFunTArg (CryFunArgs' tps cs as) tp = CryFunArgs' (tps :> tp) cs as

addCryFunArg :: CryFunArgs' tps ps -> CryFunArg t -> CryFunArgs' tps (ps ::> t)
addCryFunArg (CryFunArgs' tps cs as) a = CryFunArgs' tps cs (as :> a)

data CryFunTArg t where
  CryFunTArg :: 1 <= n => Cry.TParam -> CryFunTArg (BVType n)

data CryFunArg t = CryFunArg (CryTermAdaptor Cry.Type) (TypeShape t)

data SplitAssign f ctx where
  SplitAssign :: Assignment f a -> Assignment f b -> SplitAssign f (a <+> b) 

-- | Split an assignment into two parts.  The @Int@ is the length of
-- of the *right* component
splitAssign :: Int -> Assignment f ctx -> Maybe (SplitAssign f ctx)
splitAssign n asgn
  | n < 0  = Nothing
  | n == 0 = Just (SplitAssign asgn Ctx.empty)
  | otherwise =
    do
      Ctx.AssignExtend more a <- pure (Ctx.viewAssign asgn)
      SplitAssign left right  <- splitAssign (n-1) more
      pure (SplitAssign left (right Ctx.:> a))
      


-- | Check if the Rust type matches the Cryptol override.
typecheckFnSig ::
    forall args.
    M.FnSig ->
    Assignment TypeShape args ->
    Some TypeShape ->
    SAW.TypedTermType ->
    Either String (CryFunArgs args)
typecheckFnSig fnSig argShps0 (Some retShp) (SAW.TypedTermSchema sch@(Cry.Forall sizePs ps ty0))
  | not (null badTPs) =
    Left $ unlines [
      "Cryptol functions with non-numeric generic arguments are not supported:",
      "Cryptol type:",
      "  " ++ show (pp sch)
      ]

  | Just (SplitAssign tpShps normArgShps) <- splitAssign normArgNum argShps0 =
    case cryArgs normArgNum [] ty0 of
      Left as ->
        Left $ unlines [
          "Too many arguments:", 
          "  Expected: " ++ show (length as),
          "  Provided: " ++ show normArgNum ++ 
             (case tpArgNum of
                0 -> ""
                1 -> " (and 1 size argument)"
                _ -> " (and " ++ show tpArgNum ++ " size arguments)"
              ),
          "Cryptol type:",
          "  " ++ show (Cry.pp sch),
          "Rust type:",
          "  " ++ M.fmt fnSig
        ]
      Right (as,b) ->
        CryFunArgs <$> go (reverse sizePs) tpShps normArgNum as normArgShps b
  
  | otherwise =
    Left $ unlines [
      "Not enough size arguments:",
      "  Expected: " ++ show tpArgNum,
      "  Provided: " ++ show haveArgNum,
      "Cryptol type:",
      "  " ++ show (Cry.pp sch),
      "Rust type:",
      "  " ++ M.fmt fnSig
    ]


  where
    badTPs      = filter ((Cry.KNum /=) . Cry.kindOf) sizePs
    tpArgNum    = length sizePs
    haveArgNum  = Ctx.sizeInt (Ctx.size argShps0)
    normArgNum  = haveArgNum - tpArgNum

    cryArgs n args ty
      | n < 0  = Left args
      | n == 0 = Right (args,ty)
      | Just (a,b) <- Cry.tIsFun ty = cryArgs (n-1) (a : args) b
      | otherwise = Left args   

    go ::
      forall tpNum normNum.
      [Cry.TParam] ->
      Assignment TypeShape tpNum ->
      Int ->
      [Cry.Type] ->
      Assignment TypeShape normNum ->
      Cry.Type ->
      Either String (CryFunArgs' tpNum normNum)
    go tps tpArgs argNum normsR normArgs retTy =
      case Ctx.viewAssign tpArgs of
        Ctx.AssignEmpty ->
          case Ctx.viewAssign normArgs of
            Ctx.AssignEmpty ->
              noCryFunArgs ps <$ goOne False "return value" retShp retTy
            Ctx.AssignExtend normArgs' tyShp ->
              case normsR of
                ty : normsR' ->
                    do ada <- goOne True ("argument " ++ show argNum) tyShp ty
                       rest <- go tps tpArgs (argNum - 1) normsR' normArgs' retTy
                       pure (addCryFunArg rest (CryFunArg ada tyShp))
                _ -> error "Bug: assignment/type mismatch for normal arguments"
        
        Ctx.AssignExtend tpArgs' tpShp ->
          case (tpShp, tps) of
            (PrimShape _ (BaseBVRepr _), tp : tps') ->
              do
                rest <- go tps' tpArgs' argNum normsR normArgs retTy
                pure (addCryFunTArg rest (CryFunTArg tp))
            _ -> Left $ unlines [
              "Invalid size argument:",
              "  Expected: an unsigned numeric type",
              "  Actual: " ++ M.fmt (shapeMirTy tpShp)
              ] 
    
    goOne :: forall tp. Bool -> String -> TypeShape tp -> Cry.Type -> Either String (CryTermAdaptor Cry.Type)
    goOne isArg desc shp ty = case (shp, ty) of
        (_, Cry.TUser _ _ ty') -> goOne isArg desc shp ty'
        (UnitShape _, Cry.TCon (Cry.TC (Cry.TCTuple 0)) []) -> Right NoAdapt
        (PrimShape _ BaseBoolRepr, Cry.TCon (Cry.TC Cry.TCBit) []) -> Right NoAdapt
        (PrimShape _ (BaseBVRepr w),
            Cry.TCon (Cry.TC Cry.TCSeq) [
                Cry.tNoUser -> Cry.TCon (Cry.TC (Cry.TCNum n)) [],
                Cry.tNoUser -> Cry.TCon (Cry.TC Cry.TCBit) []])
          | fromIntegral (intValue w) == n -> Right NoAdapt
          | otherwise -> typeErr desc shp ty $
            "bitvector width " ++ show n ++ " does not match " ++ show (intValue w)
        (TupleShape _ elems, Cry.TCon (Cry.TC (Cry.TCTuple n)) tys)
          | length elems == n ->
            adaptTuple <$>
              forM (zip elems tys)
                (\(AgElemShape _off _sz shp', ty') -> goOne isArg desc shp' ty')
          | otherwise -> typeErr desc shp ty $
            "tuple size " ++ show n ++ " does not match " ++ show (length elems)
        (ArrayShape (M.TyArray _ n) _ shp',
            Cry.TCon (Cry.TC Cry.TCSeq) [
                Cry.tNoUser -> Cry.TCon (Cry.TC (Cry.TCNum n')) [],
                ty'])
          | fromIntegral n == n' -> adaptArray <$> goOne isArg desc shp' ty'
          | otherwise -> typeErr desc shp' ty $
            "array length " ++ show n' ++ " does not match " ++ show n
        (SliceShape _refTy elTy M.Immut elTyRepr, _)
           | not isArg -> typeErr desc shp ty "Slice references may appear only in parameters"
           | Just (len,cryEl) <- Cry.tIsSeq ty ->
            case asBaseType elTyRepr of
              AsBaseType bt -> AdaptDerefSlice len <$ goOne isArg desc (PrimShape elTy bt) cryEl
              _ -> typeErr desc shp ty
                   "slices to references only support elements of base types"

        _ -> typeErr desc shp ty ""

    typeErr :: forall tp. String -> TypeShape tp -> Cry.Type -> String -> Either String (CryTermAdaptor Cry.Type)
    typeErr desc shp ty extra = Left $
            "type mismatch in " ++ desc ++ ": Cryptol type " ++ show (Cry.pp ty) ++
            " does not match Rust type " ++ M.fmt (shapeMirTy shp) ++
            (if not (null extra) then ": " ++ extra else "")

typecheckFnSig _ _ _ ttt = Left $
    "internal error: unsupported TypedTermType variant: " ++ show ttt
