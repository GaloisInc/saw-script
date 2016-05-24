{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMUtils where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Lens
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import Verifier.LLVM.Backend
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Codebase hiding (Global)
import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals
import Verifier.SAW.SharedTerm
import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.LLVMExpr
import SAWScript.Utils

type SpecBackend = SAWBackend SAWCtx
type SpecPathState = Path SpecBackend
type SpecLLVMValue = SharedTerm SAWCtx

resolveType :: Codebase s -> MemType -> MemType
resolveType cb (PtrType ty) = PtrType $ resolveSymType cb ty
resolveType _ ty = ty

resolveSymType :: Codebase s -> SymType -> SymType
resolveSymType cb (MemType mt) = MemType $ resolveType cb mt
resolveSymType cb ty@(Alias i) =
  fromMaybe ty $ lookupAlias i where ?lc = cbLLVMContext cb
resolveSymType _ ty = ty

scLLVMValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scLLVMValue sc ty name = scFreshGlobal sc name ty

addrPlusOffsetSim :: (Monad m, MonadIO m) =>
                     SpecLLVMValue -> Offset
                  -> Simulator SpecBackend m SpecLLVMValue
addrPlusOffsetSim a o = do
  sbe <- gets symBE
  dl <- getDL
  liftIO $ addrPlusOffset sbe dl a o

addrPlusOffset :: SBE SpecBackend
               -> DataLayout
               -> SpecLLVMValue
               -> Offset
               -> IO SpecLLVMValue
addrPlusOffset sbe dl a o = do
  let w = fromIntegral (ptrBitwidth dl)
  ot <- sbeRunIO sbe $ termInt sbe w (fromIntegral o)
  sbeRunIO sbe $ applyTypedExpr sbe (PtrAdd a ot)

structFieldAddr :: (Functor m, MonadIO m) =>
                   StructInfo -> Int -> SpecLLVMValue
                -> Simulator SpecBackend m SpecLLVMValue
structFieldAddr si idx base =
  case siFieldOffset si idx of
    Just off -> addrPlusOffsetSim base off
    Nothing -> fail $ "Struct field index " ++ show idx ++ " out of bounds"

storePathState :: SBE SpecBackend
               -> SharedTerm SAWCtx
               -> MemType
               -> SharedTerm SAWCtx
               -> SpecPathState
               -> IO SpecPathState
storePathState sbe dst tp val ps = do
  -- TODO: alignment?
  (c, m') <- sbeRunIO sbe (memStore sbe (ps ^. pathMem) dst tp val 0)
  ps' <- addAssertion sbe c ps
  return (ps' & pathMem .~ m')

loadPathState :: SBE SpecBackend
              -> SharedTerm SAWCtx
              -> MemType
              -> SpecPathState
              -> IO (SpecLLVMValue, SpecLLVMValue)
loadPathState sbe src tp ps =
  -- TODO: alignment?
  sbeRunIO sbe (memLoad sbe (ps ^. pathMem) tp src 0)

loadGlobal :: SBE SpecBackend
           -> GlobalMap SpecBackend
           -> Symbol
           -> MemType
           -> SpecPathState
           -> IO (SpecLLVMValue, SpecLLVMValue)
loadGlobal sbe gm sym tp ps = do
  case Map.lookup sym gm of
    Just addr -> loadPathState sbe addr tp ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

storeGlobal :: SBE SpecBackend
            -> GlobalMap SpecBackend
            -> Symbol
            -> MemType
            -> SpecLLVMValue
            -> SpecPathState
            -> IO SpecPathState
storeGlobal sbe gm sym tp v ps = do
  case Map.lookup sym gm of
    Just addr -> storePathState sbe addr tp v ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

-- | Add assertion for predicate to path state.
addAssertion :: SBE SpecBackend -> SharedTerm SAWCtx -> SpecPathState -> IO SpecPathState
addAssertion sbe x p = do
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

allocSome :: (Functor sbe, Functor m, MonadIO m) =>
             SBE sbe
          -> DataLayout
          -> Integer
          -> MemType
          -> Simulator sbe m (SBETerm sbe)
allocSome sbe dl n ty = do
  let aw = ptrBitwidth dl
  sz <- liftSBE (termInt sbe aw n)
  malloc ty aw sz

-- LLVM memory operations

readLLVMTermAddrPS :: (Functor m, Monad m, MonadIO m) =>
                      SpecPathState -> [SpecLLVMValue] -> LLVMExpr
                   -> Simulator SpecBackend m (SpecLLVMValue)
readLLVMTermAddrPS ps args (Term e) =
  case e of
    Arg _ _ _ -> fail "Can't read address of argument"
    Global s _ -> evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
    Deref ae _ -> readLLVMTermPS ps args ae 1
    StructField ae si idx _ ->
      structFieldAddr si idx =<< readLLVMTermPS ps args ae 1
    StructDirectField ve si idx _ ->
      structFieldAddr si idx =<< readLLVMTermAddrPS ps args ve
    ReturnValue _ -> fail "Can't read address of return value"

readLLVMTermPS :: (Functor m, Monad m, MonadIO m) =>
                  SpecPathState -> [SpecLLVMValue] -> LLVMExpr -> Integer
               -> Simulator SpecBackend m (SpecLLVMValue)
readLLVMTermPS ps args et@(Term e) cnt =
  case e of
    Arg n _ _ -> return (args !! n)
    ReturnValue _ -> do
      rslt <- getProgramReturnValue -- NB: this is always in the current state
      case rslt of
        (Just v) -> return v
        Nothing -> fail "Program did not return a value"
    _ -> do
      let ty = lssTypeOfLLVMExpr et
      addr <- readLLVMTermAddrPS ps args et
      let ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
              | otherwise = ty
      -- Type should be type of value, not type of ptr
      sbe <- gets symBE
      (_c, v) <- liftIO $ loadPathState sbe addr ty' ps
      -- TODO: use c
      return v

readLLVMTermAddr :: (Functor m, Monad m, MonadIO m) =>
                    [SpecLLVMValue] -> LLVMExpr
                 -> Simulator SpecBackend m SpecLLVMValue
readLLVMTermAddr args e = do
  ps <- fromMaybe (error "readLLVMTermAddr") <$> getPath
  readLLVMTermAddrPS ps args e

writeLLVMTerm :: (Functor m, Monad m, MonadIO m) =>
                 [SpecLLVMValue]
              -> (LLVMExpr, SpecLLVMValue, Integer)
              -> Simulator SpecBackend m ()
writeLLVMTerm args (e, t, cnt) = do
  addr <- readLLVMTermAddr args e
  let ty = lssTypeOfLLVMExpr e
      ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
          | otherwise = ty
  dl <- getDL
  store ty' t addr (memTypeAlign dl ty')

readLLVMTerm :: (Functor m, Monad m, MonadIO m) =>
                [SpecLLVMValue]
             -> LLVMExpr
             -> Integer
             -> Simulator SpecBackend m (SpecLLVMValue)
readLLVMTerm args e cnt = do
  ps <- fromMaybe (error "readLLVMTermAddr") <$> getPath
  readLLVMTermPS ps args e cnt

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."

addrBounds :: (SBETerm m ~ SharedTerm s) =>
              SharedContext s
           -> SBE m
           -> DataLayout
           -> SharedTerm s
           -> SymType
           -> IO (SharedTerm s, SharedTerm s)
addrBounds sc sbe dl addrTm sty@(MemType (PtrType (MemType mty))) = do
    let aw = fromIntegral (ptrBitwidth dl)
        maxAddr :: Integer
        maxAddr = (2 ^ aw) - 1
        aw' = fromIntegral (ptrBitwidth dl)
    nullPtr <- sbeRunIO sbe $ applyTypedExpr sbe (SValNull sty)
    let maxFittingAddr = maxAddr - fromIntegral (memTypeSize dl mty)
    mpTerm <- scBvConst sc aw maxFittingAddr
    awTerm <- scNat sc aw
    maxPtr <- sbeRunIO sbe $ applyTypedExpr sbe (IntToPtr undefined aw' mpTerm sty)
    minTerm <- scBvUGt sc awTerm addrTm nullPtr
    maxTerm <- scBvULt sc awTerm addrTm maxPtr
    return (minTerm, maxTerm)
addrBounds _ _ _ _ ty =
    fail $ "Invalid type passed to addrBounds: " ++ show (ppSymType ty)
