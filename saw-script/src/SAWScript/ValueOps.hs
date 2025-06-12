{- |
Module      : SAWScript.ValueOps
Description : Operations on the SAWScript Value datatype, plus other code from Value.hs
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- XXX: the String and [] instances of IsValue and FromValue overlap.
-- This should be fixed by removing the String instance. (There's
-- already a Text instance.)
{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE OverlappingInstances #-}

module SAWScript.ValueOps (
    -- used by SAWScript.Interpreter
    isVUnit,
    -- used by SAWScript.Interpreter
    -- XXX: name overlaps with unrelated fn from Data.Parameterized.Nonce
    --      and should be changed
    indexValue,
    -- used by SAWScript.Interpreter
    lookupValue,
    -- used by SAWScript.Interpreter
    tupleLookupValue,
    -- used by SAWScript.Interpreter
    toplevelSubshell,
    -- used by SAWScript.Interpreter
    proofScriptSubshell,
    -- XXX apparently unused
    thenValue,
    -- used by SAWScript.Interpreter
    bindValue,
    -- used by SAWScript.Interpreter
    forValue,
    -- used by SAWScript.Interpreter
    emptyLocal,
    -- used by SAWScript.Interpreter
    extendLocal,
    -- used by SAWScript.Interpreter
    bracketTopLevel,
    -- unused but that probably won't stay that way
    TopLevelCheckpoint(..),
    -- used by SAWScript.REPL.Monad
    makeCheckpoint,
    -- used by SAWScript.REPL.Monad
    restoreCheckpoint,
    -- used by SAWScript.Interpreter
    checkpoint,
    -- used by SAWScript.Interpreter
    proof_checkpoint,
    -- used by SAWScript.Interpreter and locally in topLevelSubshell
    withLocalEnv,
    -- used locally in proofScriptSubshell
    withLocalEnvProof,
    -- used in SAWScript.Interpreter
    withOptions,
    -- used in SAWScript.Interpreter
    withStackTraceFrame,
    -- used in SAWScript.Interpreter
    toValueCase,
    -- used in SAWScript.Interpreter
    caseProofResultPrim,
    -- used in SAWScript.Interpreter
    caseSatResultPrim,
    -- used by SAWScript.REPL.Monad, SAWScript.Interpreter
    IsValue(..),
    -- used by SAWScript.Interpreter
    FromValue(..),
 ) where

import Prelude hiding (fail)

import Control.Monad.Catch (MonadThrow(..), try)
import Control.Monad.State (get, gets, modify, put)
import qualified Control.Exception as X
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Control.Monad.Reader (ask, local)

import Data.Text (Text)
import qualified Data.Text as Text (unpack)
--import Data.Map ( Map )
import qualified Data.Map as M
--import Data.Set ( Set )

import Data.Parameterized.Some

import qualified Text.LLVM.AST as LLVM (Type)

import qualified Lang.JVM.Codebase as JSS

import qualified Cryptol.TypeCheck.AST as Cryptol

import qualified Lang.Crucible.JVM as CJ
import Lang.Crucible.LLVM.ArraySizeProfile (FunctionProfile)
import Mir.Intrinsics (MIR)
import Mir.Generator (RustModule)
import qualified Mir.Mir as MIR

import SAWCore.FiniteValue (FirstOrderValue(..))
import SAWCore.SharedTerm

import CryptolSAWCore.CryptolEnv as CEnv
import CryptolSAWCore.TypedTerm

import qualified SAWCentral.AST as SS
import qualified SAWCentral.Position as SS
--import qualified SAWCentral.Crucible.JVM.MethodSpecIR ()
--import qualified SAWCentral.Crucible.MIR.MethodSpecIR ()
import SAWCentral.Options (Options, Verbosity(..))

import SAWCentral.Proof (ProofResult(..), Theorem)
import SAWCentral.Bisimulation (BisimTheorem)
import SAWCentral.JavaExpr (JavaType(..))
import qualified SAWCentral.Crucible.Common.MethodSpec as CMS
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMSLLVM
import SAWCentral.Crucible.LLVM.Skeleton (ModuleSkeleton, FunctionSkeleton)
import qualified SAWCentral.Yosys as Yo (YosysIR)
import qualified SAWCentral.Yosys.State as Yo (YosysSequential)
import qualified SAWCentral.Yosys.Theorem as Yo (YosysImport, YosysTheorem)

import SAWCentral.Value



isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

indexValue :: Value -> Value -> Value
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value -> Text -> Value
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ Text.unpack name
      Just x -> x
lookupValue _ _ = error "lookupValue"

tupleLookupValue :: Value -> Integer -> Value
tupleLookupValue (VTuple vs) i
  | 0 <= i && fromIntegral i < length vs = vs !! fromIntegral i
  | otherwise = error $ "no such tuple index: " ++ show i
tupleLookupValue _ _ = error "tupleLookupValue"

toplevelSubshell :: Value
toplevelSubshell = VLambda $ \_ ->
  do m <- roSubshell <$> ask
     env <- getLocalEnv
     return (VTopLevel (toValue <$> withLocalEnv env m))

proofScriptSubshell :: Value
proofScriptSubshell = VLambda $ \_ ->
  do m <- roProofSubshell <$> ask
     env <- getLocalEnv
     return (VProofScript (toValue <$> withLocalEnvProof env m))

applyValue :: Value -> Value -> TopLevel Value
applyValue (VLambda f) x = f x
applyValue _ _ = throwTopLevel "applyValue"

thenValue :: SS.Pos -> Value -> Value -> Value
thenValue pos v1 v2 = VBind pos v1 (VLambda (const (return v2)))

bindValue :: SS.Pos -> Value -> Value -> TopLevel Value
bindValue pos v1 v2 = return (VBind pos v1 v2)

forValue :: [Value] -> Value -> TopLevel Value
forValue [] _ = return $ VReturn (VArray [])
forValue (x : xs) f =
  do m1 <- applyValue f x
     m2 <- forValue xs f
     bindValue (SS.PosInternal "<for>") m1 (VLambda $ \v1 ->
       bindValue (SS.PosInternal "<for>") m2 (VLambda $ \v2 ->
         return $ VReturn (VArray (v1 : fromValue v2))))

emptyLocal :: LocalEnv
emptyLocal = []

extendLocal :: SS.LName -> SS.Schema -> Maybe String -> Value -> LocalEnv -> LocalEnv
extendLocal x ty md v env = LocalLet x ty md v : env

-- | A version of 'Control.Exception.bracket' specialized to 'TopLevel'. We
-- can't use 'Control.Monad.Catch.bracket' because it requires 'TopLevel' to
-- implement 'Control.Monad.Catch.MonadMask', which it can't do.
bracketTopLevel :: TopLevel a -> (a -> TopLevel b) -> (a -> TopLevel c) -> TopLevel c
bracketTopLevel acquire release action =
  do  resource <- acquire
      try (action resource) >>= \case
        Left (bad :: X.SomeException) -> release resource >> throwM bad
        Right good -> release resource >> pure good

combineRW :: TopLevelCheckpoint -> TopLevelRW -> IO TopLevelRW
combineRW (TopLevelCheckpoint chk scc) rw =
  do cenv' <- CEnv.combineCryptolEnv (rwCryptol chk) (rwCryptol rw)
     sc' <- restoreSharedContext scc (rwSharedContext rw)
     return chk{ rwCryptol = cenv'
               , rwSharedContext = sc'
               }

-- | Represents the mutable state of the TopLevel monad
--   that can later be restored.
data TopLevelCheckpoint =
  TopLevelCheckpoint
    TopLevelRW
    SharedContextCheckpoint

makeCheckpoint :: TopLevelRW -> IO TopLevelCheckpoint
makeCheckpoint rw =
  do scc <- checkpointSharedContext (rwSharedContext rw)
     return (TopLevelCheckpoint rw scc)

restoreCheckpoint :: TopLevelCheckpoint -> TopLevel ()
restoreCheckpoint chk =
  do rw <- getTopLevelRW
     rw' <- io (combineRW chk rw)
     putTopLevelRW rw'

-- | Capture the current state of the TopLevel monad
--   and return an action that, if invoked, resets
--   the state back to that point.
checkpoint :: TopLevel (() -> TopLevel ())
checkpoint = TopLevel_ $
  do chk <- liftIO . makeCheckpoint =<< get
     return $ \_ ->
       do printOutLnTop Info "Restoring state from checkpoint"
          restoreCheckpoint chk

-- | Capture the current proof state and return an
--   action that, if invoked, resets the state back to that point.
proof_checkpoint :: ProofScript (() -> ProofScript ())
proof_checkpoint =
  do ps <- get
     return $ \_ ->
       do scriptTopLevel (printOutLnTop Info "Restoring proof state from checkpoint")
          put ps

withLocalEnv :: LocalEnv -> TopLevel a -> TopLevel a
withLocalEnv env m = do
  prevEnv <- gets rwLocalEnv
  modify (\rw -> rw { rwLocalEnv = env })
  result <- m
  modify (\rw -> rw { rwLocalEnv = prevEnv })
  return result

withLocalEnvProof :: LocalEnv -> ProofScript a -> ProofScript a
withLocalEnvProof env (ProofScript m) = do
  ProofScript (underExceptT (underStateT (withLocalEnv env)) m)

withOptions :: (Options -> Options) -> TopLevel a -> TopLevel a
withOptions f (TopLevel_ m) =
  TopLevel_ (local (\x -> x {roOptions = f (roOptions x)}) m)

-- | Implement stack tracing by adding error handlers that rethrow
-- user errors, prepended with the given string.
withStackTraceFrame :: String -> Value -> Value
withStackTraceFrame str val =
  let doTopLevel :: TopLevel a -> TopLevel a
      doTopLevel action = do
        trace <- gets rwStackTrace
        modify (\rw -> rw { rwStackTrace = str : trace })
        result <- action
        modify (\rw -> rw { rwStackTrace = trace })
        return result
      doProofScript :: ProofScript a -> ProofScript a
      doProofScript (ProofScript m) =
        let m' =
              underExceptT (underStateT doTopLevel) m
        in
        ProofScript m'
      doLLVM :: LLVMCrucibleSetupM a -> LLVMCrucibleSetupM a
      doLLVM (LLVMCrucibleSetupM m) =
        LLVMCrucibleSetupM (underReaderT (underStateT doTopLevel) m)
      doJVM :: JVMSetupM a -> JVMSetupM a
      doJVM (JVMSetupM m) =
        JVMSetupM (underReaderT (underStateT doTopLevel) m)
      doMIR :: MIRSetupM a -> MIRSetupM a
      doMIR (MIRSetupM m) =
        MIRSetupM (underReaderT (underStateT doTopLevel) m)
  in
  case val of
    VLambda f ->
      let wrap x =
            withStackTraceFrame str `fmap` doTopLevel (f x)
      in
      VLambda wrap
    VTopLevel m ->
      let m' =
            withStackTraceFrame str `fmap` doTopLevel m
      in
      VTopLevel m'
    VProofScript m ->
      let m' =
            withStackTraceFrame str `fmap` doProofScript m
      in
      VProofScript m'
    VBind pos v1 v2 ->
      let v1' = withStackTraceFrame str v1
          v2' = withStackTraceFrame str v2
      in
      VBind pos v1' v2'
    VLLVMCrucibleSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doLLVM m
      in
      VLLVMCrucibleSetup m'
    VJVMSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doJVM m
      in
      VJVMSetup m'
    VMIRSetup m ->
      let m' =
            withStackTraceFrame str `fmap` doMIR m
      in
      VMIRSetup m'
    _ ->
      val

toValueCase :: (FromValue b) =>
               (b -> Value -> Value -> TopLevel Value)
            -> Value
toValueCase prim =
  VLambda $ \b -> return $
  VLambda $ \v1 -> return $
  VLambda $ \v2 ->
  prim (fromValue b) v1 v2

caseProofResultPrim ::
  ProofResult ->
  Value {- ^ valid case -} ->
  Value {- ^ invalid/unknown case -} ->
  TopLevel Value
caseProofResultPrim pr vValid vInvalid = do
  sc <- getSharedContext
  case pr of
    ValidProof _ thm ->
      applyValue vValid (toValue thm)
    InvalidProof _ pairs _pst -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue vInvalid (toValue tt)
    UnfinishedProof _ -> do
      tt <- io $ typedTermOfFirstOrderValue sc (FOVTuple [])
      applyValue vInvalid (toValue tt)

caseSatResultPrim ::
  SatResult ->
  Value {- ^ unsat case -} ->
  Value {- ^ sat/unknown case -} ->
  TopLevel Value
caseSatResultPrim sr vUnsat vSat = do
  sc <- getSharedContext
  case sr of
    Unsat _ -> return vUnsat
    Sat _ pairs -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue vSat (toValue tt)
    SatUnknown -> do
      let fov = FOVTuple []
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue vSat (toValue tt)


------------------------------------------------------------
-- IsValue and FromValue

-- | Used for encoding primitive operations in the Value type.
class IsValue a where
    toValue :: a -> Value

class FromValue a where
    fromValue :: Value -> a

instance (FromValue a, IsValue b) => IsValue (a -> b) where
    toValue f = VLambda (\v -> return (toValue (f (fromValue v))))

instance (IsValue a, FromValue b) => FromValue (a -> TopLevel b) where
    fromValue (VLambda f) = \x -> fromValue <$> f (toValue x)
    fromValue _ = error "fromValue (->)"

instance FromValue Value where
    fromValue x = x

instance IsValue Value where
    toValue x = x

instance IsValue () where
    toValue _ = VTuple []

instance FromValue () where
    fromValue _ = ()

instance (IsValue a, IsValue b) => IsValue (a, b) where
    toValue (x, y) = VTuple [toValue x, toValue y]

instance (FromValue a, FromValue b) => FromValue (a, b) where
    fromValue (VTuple [x, y]) = (fromValue x, fromValue y)
    fromValue _ = error "fromValue (,)"

instance (IsValue a, IsValue b, IsValue c) => IsValue (a, b, c) where
    toValue (x, y, z) = VTuple [toValue x, toValue y, toValue z]

instance (FromValue a, FromValue b, FromValue c) => FromValue (a, b, c) where
    fromValue (VTuple [x, y, z]) = (fromValue x, fromValue y, fromValue z)
    fromValue _ = error "fromValue (,,)"

instance IsValue a => IsValue [a] where
    toValue xs = VArray (map toValue xs)


instance FromValue a => FromValue [a] where
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue a => IsValue (IO a) where
    toValue action = toValue (io action)

instance IsValue a => IsValue (Maybe a) where
  toValue (Just x) = VMaybe . Just $ toValue x
  toValue Nothing = VMaybe Nothing

instance FromValue a => FromValue (Maybe a) where
  fromValue (VMaybe (Just v)) = Just $ fromValue v
  fromValue (VMaybe Nothing) = Nothing
  fromValue _ = error "fromValue Maybe"

instance IsValue a => IsValue (TopLevel a) where
    toValue action = VTopLevel (fmap toValue action)

instance FromValue a => FromValue (TopLevel a) where
    fromValue (VTopLevel action) = fmap fromValue action
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = do
      savepos <- pushPosition pos
      v1 <- fromValue m1
      popPosition savepos
      m2 <- applyValue v2 v1
      fromValue m2
    fromValue v = error $ "fromValue TopLevel:" <> show v

instance IsValue a => IsValue (ProofScript a) where
    toValue m = VProofScript (fmap toValue m)

instance FromValue a => FromValue (ProofScript a) where
    fromValue (VProofScript m) = fmap fromValue m
    -- Inject top-level computations automatically into proof scripts.
    -- This should really only possible in interactive subshell mode; otherwise
    --  the type system should keep this from happening.
    fromValue (VTopLevel m) = ProofScript (lift (lift (fmap fromValue m)))
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = ProofScript $ do
      savepos <- lift $ lift $ pushPosition pos
      v1 <- unProofScript (fromValue m1)
      lift $ lift $ popPosition savepos
      m2 <- lift $ lift $ applyValue v2 v1
      unProofScript (fromValue m2)
    fromValue _ = error "fromValue ProofScript"

instance IsValue a => IsValue (LLVMCrucibleSetupM a) where
    toValue m = VLLVMCrucibleSetup (fmap toValue m)

instance FromValue a => FromValue (LLVMCrucibleSetupM a) where
    fromValue (VLLVMCrucibleSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = LLVMCrucibleSetupM $ do
      -- TODO: Should both of these be run with the new position?
      savepos <- lift $ lift $ pushPosition pos
      v1 <- runLLVMCrucibleSetupM (fromValue m1)
      lift $ lift $ popPosition savepos
      m2 <- lift $ lift $ applyValue v2 v1
      runLLVMCrucibleSetupM (fromValue m2)
    fromValue _ = error "fromValue CrucibleSetup"

instance IsValue a => IsValue (JVMSetupM a) where
    toValue m = VJVMSetup (fmap toValue m)

instance FromValue a => FromValue (JVMSetupM a) where
    fromValue (VJVMSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = JVMSetupM $ do
      savepos <- lift $ lift $ pushPosition pos
      v1 <- runJVMSetupM (fromValue m1)
      lift $ lift $ popPosition savepos
      m2 <- lift $ lift $ applyValue v2 v1
      runJVMSetupM (fromValue m2)
    fromValue _ = error "fromValue JVMSetup"

instance IsValue a => IsValue (MIRSetupM a) where
    toValue m = VMIRSetup (fmap toValue m)

instance FromValue a => FromValue (MIRSetupM a) where
    fromValue (VMIRSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = MIRSetupM $ do
      savepos <- lift $ lift $ pushPosition pos
      v1 <- runMIRSetupM (fromValue m1)
      lift $ lift $ popPosition savepos
      m2 <- lift $ lift $ applyValue v2 v1
      runMIRSetupM (fromValue m2)
    fromValue _ = error "fromValue MIRSetup"

instance IsValue (CMSLLVM.AllLLVM CMS.SetupValue) where
  toValue = VLLVMCrucibleSetupValue

instance FromValue (CMSLLVM.AllLLVM CMS.SetupValue) where
  fromValue (VLLVMCrucibleSetupValue v) = v
  fromValue _ = error "fromValue Crucible.SetupValue"

instance IsValue (CMS.SetupValue CJ.JVM) where
  toValue v = VJVMSetupValue v

instance FromValue (CMS.SetupValue CJ.JVM) where
  fromValue (VJVMSetupValue v) = v
  fromValue _ = error "fromValue Crucible.SetupValue"

instance IsValue (CMS.SetupValue MIR) where
  toValue v = VMIRSetupValue v

instance FromValue (CMS.SetupValue MIR) where
  fromValue (VMIRSetupValue v) = v
  fromValue _ = error "fromValue Crucible.SetupValue"

instance IsValue SAW_CFG where
    toValue t = VCFG t

instance FromValue SAW_CFG where
    fromValue (VCFG t) = t
    fromValue _ = error "fromValue CFG"

instance IsValue (CMSLLVM.SomeLLVM CMS.ProvedSpec) where
    toValue mir = VLLVMCrucibleMethodSpec mir

instance FromValue (CMSLLVM.SomeLLVM CMS.ProvedSpec) where
    fromValue (VLLVMCrucibleMethodSpec mir) = mir
    fromValue _ = error "fromValue ProvedSpec LLVM"

instance IsValue (CMS.ProvedSpec CJ.JVM) where
    toValue t = VJVMMethodSpec t

instance FromValue (CMS.ProvedSpec CJ.JVM) where
    fromValue (VJVMMethodSpec t) = t
    fromValue _ = error "fromValue ProvedSpec JVM"

instance IsValue (CMS.ProvedSpec MIR) where
    toValue t = VMIRMethodSpec t

instance FromValue (CMS.ProvedSpec MIR) where
    fromValue (VMIRMethodSpec t) = t
    fromValue _ = error "fromValue ProvedSpec MIR"

instance IsValue ModuleSkeleton where
    toValue s = VLLVMModuleSkeleton s

instance FromValue ModuleSkeleton where
    fromValue (VLLVMModuleSkeleton s) = s
    fromValue _ = error "fromValue ModuleSkeleton"

instance IsValue FunctionSkeleton where
    toValue s = VLLVMFunctionSkeleton s

instance FromValue FunctionSkeleton where
    fromValue (VLLVMFunctionSkeleton s) = s
    fromValue _ = error "fromValue FunctionSkeleton"

instance IsValue SkeletonState where
    toValue s = VLLVMSkeletonState s

instance FromValue SkeletonState where
    fromValue (VLLVMSkeletonState s) = s
    fromValue _ = error "fromValue SkeletonState"

instance IsValue FunctionProfile where
    toValue s = VLLVMFunctionProfile s

instance FromValue FunctionProfile where
    fromValue (VLLVMFunctionProfile s) = s
    fromValue _ = error "fromValue FunctionProfile"

instance IsValue (AIGNetwork) where
    toValue t = VAIG t

instance FromValue (AIGNetwork) where
    fromValue (VAIG t) = t
    fromValue _ = error "fromValue AIGNetwork"

instance IsValue TypedTerm where
    toValue t = VTerm t

instance FromValue TypedTerm where
    fromValue (VTerm t) = t
    fromValue _ = error "fromValue TypedTerm"

instance FromValue Term where
    fromValue (VTerm t) = ttTerm t
    fromValue _ = error "fromValue SharedTerm"

instance IsValue Cryptol.Schema where
    toValue s = VType s

instance FromValue Cryptol.Schema where
    fromValue (VType s) = s
    fromValue _ = error "fromValue Schema"

instance IsValue Text where
    toValue n = VString n

instance FromValue Text where
    fromValue (VString n) = n
    fromValue _ = error "fromValue Text"

instance IsValue Integer where
    toValue n = VInteger n

instance FromValue Integer where
    fromValue (VInteger n) = n
    fromValue _ = error "fromValue Integer"

instance IsValue Int where
    toValue n = VInteger (toInteger n)

instance FromValue Int where
    fromValue (VInteger n)
      | toInteger (minBound :: Int) <= n &&
        toInteger (maxBound :: Int) >= n = fromIntegral n
    fromValue _ = error "fromValue Int"

instance IsValue Bool where
    toValue b = VBool b

instance FromValue Bool where
    fromValue (VBool b) = b
    fromValue _ = error "fromValue Bool"

instance IsValue SAWSimpset where
    toValue ss = VSimpset ss

instance FromValue SAWSimpset where
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue SAWRefnset where
    toValue rs = VRefnset rs

instance FromValue SAWRefnset where
    fromValue (VRefnset rs) = rs
    fromValue _ = error "fromValue Refnset"

instance IsValue Theorem where
    toValue t = VTheorem t

instance FromValue Theorem where
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

instance IsValue BisimTheorem where
    toValue = VBisimTheorem

instance FromValue BisimTheorem where
    fromValue (VBisimTheorem t) = t
    fromValue _ = error "fromValue BisimTheorem"

instance IsValue JavaType where
    toValue t = VJavaType t

instance FromValue JavaType where
    fromValue (VJavaType t) = t
    fromValue _ = error "fromValue JavaType"

instance IsValue LLVM.Type where
    toValue t = VLLVMType t

instance FromValue LLVM.Type where
    fromValue (VLLVMType t) = t
    fromValue _ = error "fromValue LLVMType"

instance IsValue MIR.Ty where
    toValue t = VMIRType t

instance FromValue MIR.Ty where
    fromValue (VMIRType t) = t
    fromValue _ = error "fromValue MIRType"

instance IsValue Uninterp where
    toValue me = VUninterp me

instance FromValue Uninterp where
    fromValue (VUninterp me) = me
    fromValue _ = error "fromValue Uninterp"

instance IsValue CryptolModule where
    toValue m = VCryptolModule m

instance FromValue CryptolModule where
    fromValue (VCryptolModule m) = m
    fromValue _ = error "fromValue ModuleEnv"

instance IsValue JSS.Class where
    toValue c = VJavaClass c

instance FromValue JSS.Class where
    fromValue (VJavaClass c) = c
    fromValue _ = error "fromValue JavaClass"

instance IsValue (Some CMSLLVM.LLVMModule) where
    toValue m = VLLVMModule m

instance IsValue (CMSLLVM.LLVMModule arch) where
    toValue m = VLLVMModule (Some m)

instance FromValue (Some CMSLLVM.LLVMModule) where
    fromValue (VLLVMModule m) = m
    fromValue _ = error "fromValue CMSLLVM.LLVMModule"

instance IsValue RustModule where
    toValue m = VMIRModule m

instance FromValue RustModule where
    fromValue (VMIRModule m) = m
    fromValue _ = error "fromValue RustModule"

instance IsValue MIR.Adt where
    toValue adt = VMIRAdt adt

instance FromValue MIR.Adt where
    fromValue (VMIRAdt adt) = adt
    fromValue _ = error "fromValue Adt"

instance IsValue HeapsterEnv where
    toValue m = VHeapsterEnv m

instance FromValue HeapsterEnv where
    fromValue (VHeapsterEnv m) = m
    fromValue _ = error "fromValue HeapsterEnv"

instance IsValue ProofResult where
   toValue r = VProofResult r

instance FromValue ProofResult where
   fromValue (VProofResult r) = r
   fromValue v = error $ "fromValue ProofResult: " ++ show v

instance IsValue SatResult where
   toValue r = VSatResult r

instance FromValue SatResult where
   fromValue (VSatResult r) = r
   fromValue v = error $ "fromValue SatResult: " ++ show v

instance IsValue CMS.GhostGlobal where
  toValue = VGhostVar

instance FromValue CMS.GhostGlobal where
  fromValue (VGhostVar r) = r
  fromValue v = error ("fromValue GlobalVar: " ++ show v)

instance IsValue Yo.YosysIR where
  toValue = VYosysModule

instance FromValue Yo.YosysIR where
  fromValue (VYosysModule ir) = ir
  fromValue v = error ("fromValue YosysIR: " ++ show v)

instance IsValue Yo.YosysImport where
  toValue = VYosysImport

instance FromValue Yo.YosysImport where
  fromValue (VYosysImport i) = i
  fromValue v = error ("fromValue YosysImport: " ++ show v)

instance IsValue Yo.YosysSequential where
  toValue = VYosysSequential

instance FromValue Yo.YosysSequential where
  fromValue (VYosysSequential s) = s
  fromValue v = error ("fromValue YosysSequential: " ++ show v)

instance IsValue Yo.YosysTheorem where
  toValue = VYosysTheorem

instance FromValue Yo.YosysTheorem where
  fromValue (VYosysTheorem thm) = thm
  fromValue v = error ("fromValue YosysTheorem: " ++ show v)
