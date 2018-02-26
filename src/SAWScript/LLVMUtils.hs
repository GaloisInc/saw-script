{- |
Module      : SAWScript.LLVMUtils
Description : Miscellaneous utilities for LLVM.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
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
import qualified SAWScript.CongruenceClosure as CC
import SAWScript.LLVMExpr

type SpecBackend = SAWBackend
type SpecPathState = Path SpecBackend
type SpecLLVMValue = Term

missingSymMsg :: String -> Symbol -> String
missingSymMsg file (Symbol func) =
  "Bitcode file " ++ file ++ " does not contain symbol `" ++ func ++ "`."

resolveType :: Codebase s -> MemType -> MemType
resolveType cb (PtrType ty) = PtrType $ resolveSymType cb ty
resolveType _ ty = ty

resolveSymType :: Codebase s -> SymType -> SymType
resolveSymType cb (MemType mt) = MemType $ resolveType cb mt
resolveSymType cb ty@(Alias i) =
  fromMaybe ty $ lookupAlias i where ?lc = cbLLVMContext cb
resolveSymType _ ty = ty

scLLVMValue :: SharedContext -> Term -> String -> IO Term
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

storePathState :: (MonadIO m, Functor m) =>
                  Term
               -> MemType
               -> Term
               -> SpecPathState
               -> Simulator SpecBackend m SpecPathState
storePathState dst tp val ps = do
  sbe <- gets symBE
  dst' <- simplifyAddr dst
  -- TODO: alignment?
  (c, m') <- liftSBE $ memStore sbe (ps ^. pathMem) dst' tp val 0
  ps' <- liftIO $ addAssertion sbe c ps
  return (ps' & pathMem .~ m')

loadPathState :: (MonadIO m, Functor m) =>
                 Term
              -> MemType
              -> SpecPathState
              -> Simulator SpecBackend m (SpecLLVMValue, SpecLLVMValue)
loadPathState src tp ps = do
  sbe <- gets symBE
  src' <- simplifyAddr src
  -- TODO: alignment?
  liftSBE $ memLoad sbe (ps ^. pathMem) tp src' 0

allocPathState :: (MonadIO m, Functor m) =>
                  MemType
               -> SpecPathState
               -> Simulator SpecBackend m (SpecLLVMValue, SpecPathState)
allocPathState tp ps = do
  sbe <- gets symBE
  dl <- getDL
  let aw = ptrBitwidth dl
  n <- liftSBE $ termInt sbe aw 1
  r <- liftSBE $ heapAlloc sbe (ps ^. pathMem) tp aw n 0
  case r of
    AResult c p m' -> do
      ps' <- liftIO $ addAssertion sbe c ps
      return (p, ps' & pathMem .~ m')
    AError msg -> errorPath msg

loadGlobal :: (MonadIO m, Functor m) =>
              GlobalMap SpecBackend
           -> Symbol
           -> MemType
           -> SpecPathState
           -> Simulator SpecBackend m (SpecLLVMValue, SpecLLVMValue)
loadGlobal gm sym tp ps = do
  case Map.lookup sym gm of
    Just addr -> loadPathState addr tp ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

storeGlobal :: (MonadIO m, Functor m) =>
               GlobalMap SpecBackend
            -> Symbol
            -> MemType
            -> SpecLLVMValue
            -> SpecPathState
            -> Simulator SpecBackend m SpecPathState
storeGlobal gm sym tp v ps = do
  case Map.lookup sym gm of
    Just addr -> storePathState addr tp v ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

-- | Add assertion for predicate to path state.
addAssertion :: SBE SpecBackend -> Term -> SpecPathState -> IO SpecPathState
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
                      SpecPathState
                   -> Maybe SpecLLVMValue
                   -> [SpecLLVMValue]
                   -> LLVMExpr
                   -> Simulator SpecBackend m SpecLLVMValue
readLLVMTermAddrPS ps mrv args (CC.Term e) =
  case e of
    Arg _ _ _ -> fail "Can't read address of argument"
    Global s _ -> evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
    Deref ae _ -> readLLVMTermPS ps mrv args ae 1
    StructField ae si idx _ ->
      structFieldAddr si idx =<< readLLVMTermPS ps mrv args ae 1
    StructDirectField ve si idx _ ->
      structFieldAddr si idx =<< readLLVMTermAddrPS ps mrv args ve
    ReturnValue _ -> fail "Can't read address of return value"

readLLVMTermPS :: (Functor m, Monad m, MonadIO m) =>
                  SpecPathState
               -> Maybe SpecLLVMValue -- ^ To use instead of current state.
               -> [SpecLLVMValue]
               -> LLVMExpr
               -> Integer
               -> Simulator SpecBackend m SpecLLVMValue
readLLVMTermPS ps mrv args et@(CC.Term e) cnt =
  case e of
    Arg n _ _ -> return (args !! n)
    ReturnValue _ -> do
      rslt <- getProgramReturnValue
      case (mrv, rslt) of
        (Just v, _) -> return v
        (_, Just v) -> return v
        (Nothing, Nothing) -> fail "Program did not return a value"
    _ -> do
      let ty = lssTypeOfLLVMExpr et
      addr <- readLLVMTermAddrPS ps mrv args et
      let ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
              | otherwise = ty
      -- Type should be type of value, not type of ptr
      (_c, v) <- loadPathState addr ty' ps
      -- TODO: use c
      return v

readLLVMTermAddr :: (Functor m, Monad m, MonadIO m) =>
                    Maybe SpecLLVMValue -> [SpecLLVMValue] -> LLVMExpr
                 -> Simulator SpecBackend m SpecLLVMValue
readLLVMTermAddr mrv args e = do
  ps <- fromMaybe (error "readLLVMTermAddr") <$> getPath
  readLLVMTermAddrPS ps mrv args e

writeLLVMTerm :: (Functor m, Monad m, MonadIO m) =>
                 Maybe SpecLLVMValue
              -> [SpecLLVMValue]
              -> (LLVMExpr, SpecLLVMValue, Integer)
              -> Simulator SpecBackend m ()
writeLLVMTerm mrv args (e, t, cnt) = do
  addr <- readLLVMTermAddr mrv args e
  let ty = lssTypeOfLLVMExpr e
      ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
          | otherwise = ty
  dl <- getDL
  store ty' t addr (memTypeAlign dl ty')

readLLVMTerm :: (Functor m, Monad m, MonadIO m) =>
                Maybe SpecLLVMValue
             -> [SpecLLVMValue]
             -> LLVMExpr
             -> Integer
             -> Simulator SpecBackend m SpecLLVMValue
readLLVMTerm mrv args e cnt = do
  ps <- fromMaybe (error "readLLVMTermAddr") <$> getPath
  readLLVMTermPS ps mrv args e cnt

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."

llvmNullPtr :: (SBETerm m ~ Term) =>
               SBE m
            -> SymType
            -> IO Term
llvmNullPtr sbe sty = sbeRunIO sbe $ applyTypedExpr sbe (SValNull sty)

addrBounds :: (SBETerm m ~ Term) =>
              SharedContext
           -> SBE m
           -> DataLayout
           -> Term
           -> SymType
           -> IO (Term, Term)
addrBounds sc sbe dl addrTm sty@(MemType (PtrType (MemType mty))) = do
    let aw = fromIntegral (ptrBitwidth dl)
        maxAddr :: Integer
        maxAddr = (2 ^ aw) - 1
        aw' = fromIntegral (ptrBitwidth dl)
    nullPtr <- llvmNullPtr sbe sty
    let maxFittingAddr = maxAddr - fromIntegral (memTypeSize dl mty)
    mpTerm <- scBvConst sc aw maxFittingAddr
    awTerm <- scNat sc aw
    maxPtr <- sbeRunIO sbe $ applyTypedExpr sbe (IntToPtr undefined aw' mpTerm sty)
    minTerm <- scBvUGt sc awTerm addrTm nullPtr
    maxTerm <- scBvULt sc awTerm addrTm maxPtr
    return (minTerm, maxTerm)
addrBounds _ _ _ _ ty =
    fail $ "Invalid type passed to addrBounds: " ++ show (ppSymType ty)
