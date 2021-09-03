{- |
Module      : SAWScript.Value
Description : Value datatype for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWScript.Value where

import Prelude hiding (fail)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif
import Control.Lens
import Control.Monad.Fail (MonadFail(..))
import Control.Monad.Catch (MonadThrow(..), MonadMask(..),
                            MonadCatch(..), catches, Handler(..))
import Control.Monad.Except (ExceptT(..), runExceptT, MonadError(..))
import Control.Monad.Reader (MonadReader)
import qualified Control.Exception as X
import qualified System.IO.Error as IOError
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT(..), ask, asks, local)
import Control.Monad.State (MonadState(..), StateT(..), get, gets, put)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Data.IORef
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Set ( Set )
import Data.Text (Text, pack, unpack)
import Data.Parameterized.Some
import Data.Typeable
import GHC.Generics (Generic, Generic1)
import qualified Prettyprinter as PP

import qualified Data.AIG as AIG

import qualified SAWScript.AST as SS
import qualified SAWScript.Exceptions as SS
import qualified SAWScript.Position as SS
import qualified SAWScript.Crucible.Common.Setup.Type as Setup
import qualified SAWScript.Crucible.Common.MethodSpec as CMS
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as Crucible
import qualified SAWScript.Crucible.JVM.MethodSpecIR ()
import qualified Lang.JVM.Codebase as JSS
import qualified Text.LLVM.AST as LLVM (Type)
import qualified Text.LLVM.PP as LLVM (ppType)
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.JavaPretty (prettyClass)
import SAWScript.Options (Options(printOutFn),printOutLn,Verbosity)
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Crucible.LLVM.Skeleton
import SAWScript.X86 (X86Unsupported(..), X86Error(..))

import Verifier.SAW.Name (toShortName)
import Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.FiniteValue (FirstOrderValue, ppFirstOrderValue)
import Verifier.SAW.Rewriter (Simpset, lhsRewriteRule, rhsRewriteRule, listRules)
import Verifier.SAW.SharedTerm hiding (PPOpts(..), defaultPPOpts,
                                       ppTerm, scPrettyTerm)
import qualified Verifier.SAW.SharedTerm as SAWCorePP (PPOpts(..), defaultPPOpts,
                                                       ppTerm, scPrettyTerm)
import Verifier.SAW.TypedTerm
import Verifier.SAW.Term.Functor (ModuleName)

import qualified Verifier.SAW.Simulator.Concrete as Concrete
import qualified Cryptol.Eval as C
import qualified Cryptol.Eval.Concrete as C
import Verifier.SAW.Cryptol (exportValueWithSchema)
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.Logger as C (quietLogger)
import qualified Cryptol.Utils.Ident as T (packIdent, packModName)
import Cryptol.Utils.PP (pretty)

import qualified Lang.Crucible.CFG.Core as Crucible (AnyCFG)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)

import           Lang.Crucible.JVM (JVM)
import qualified Lang.Crucible.JVM as CJ

import Lang.Crucible.LLVM.ArraySizeProfile

import           What4.ProgramLoc (ProgramLoc(..))

import Verifier.SAW.Heapster.Permissions

-- Values ----------------------------------------------------------------------

data Value
  = VBool Bool
  | VString Text
  | VInteger Integer
  | VArray [Value]
  | VTuple [Value]
  | VMaybe (Maybe Value)
  | VRecord (Map SS.Name Value)
  | VLambda (Value -> TopLevel Value)
  | VTerm TypedTerm
  | VType Cryptol.Schema
  | VReturn Value -- Returned value in unspecified monad
  | VBind SS.Pos Value Value
    -- ^ Monadic bind in unspecified monad. Requires a source position because
    -- operations in these monads can fail at runtime.
  | VTopLevel (TopLevel Value)
  | VProofScript (ProofScript Value)
  | VSimpset SAWSimpset
  | VTheorem Theorem
  -----
  | VLLVMCrucibleSetup !(LLVMCrucibleSetupM Value)
  | VLLVMCrucibleMethodSpec (CMSLLVM.SomeLLVM CMS.ProvedSpec)
  | VLLVMCrucibleSetupValue (CMSLLVM.AllLLVM CMS.SetupValue)
  -----
  | VJVMSetup !(JVMSetupM Value)
  | VJVMMethodSpec !(CMS.ProvedSpec CJ.JVM)
  | VJVMSetupValue !(CMS.SetupValue CJ.JVM)
  -----
  | VLLVMModuleSkeleton ModuleSkeleton
  | VLLVMFunctionSkeleton FunctionSkeleton
  | VLLVMSkeletonState SkeletonState
  | VLLVMFunctionProfile FunctionProfile
  -----
  | VJavaType JavaType
  | VLLVMType LLVM.Type
  | VCryptolModule CryptolModule
  | VJavaClass JSS.Class
  | VLLVMModule (Some CMSLLVM.LLVMModule)
  | VHeapsterEnv HeapsterEnv
  | VSatResult SatResult
  | VProofResult ProofResult
  | VUninterp Uninterp
  | VAIG AIGNetwork
  | VCFG SAW_CFG
  | VGhostVar CMS.GhostGlobal

type SAWSimpset = Simpset TheoremNonce

data AIGNetwork where
  AIGNetwork :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Network l g -> AIGNetwork

data AIGProxy where
  AIGProxy :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Proxy l g -> AIGProxy

data SAW_CFG where
  LLVM_CFG :: Crucible.AnyCFG Crucible.LLVM -> SAW_CFG
  JVM_CFG :: Crucible.AnyCFG JVM -> SAW_CFG

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext
                                     , biBasicSS       :: SAWSimpset
                                     }
  deriving Generic

-- | All the context maintained by Heapster
data HeapsterEnv = HeapsterEnv {
  heapsterEnvSAWModule :: ModuleName,
  -- ^ The SAW module containing all our Heapster definitions
  heapsterEnvPermEnvRef :: IORef PermEnv,
  -- ^ The current permissions environment
  heapsterEnvLLVMModules :: [Some CMSLLVM.LLVMModule],
  -- ^ The list of underlying 'LLVMModule's that we are translating
  heapsterEnvDebugLevel :: IORef DebugLevel
  }

showHeapsterEnv :: HeapsterEnv -> String
showHeapsterEnv env =
  concat $ intersperse "\n\n" $
  map (\some_lm -> case some_lm of
          Some lm -> CMSLLVM.showLLVMModule lm) $
  heapsterEnvLLVMModules env

data SatResult
  = Unsat SolverStats
  | Sat SolverStats [(ExtCns Term, FirstOrderValue)]
  | SatUnknown
    deriving (Show)

isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

data PPOpts = PPOpts
  { ppOptsAnnotate :: Bool
  , ppOptsAscii :: Bool
  , ppOptsBase :: Int
  , ppOptsColor :: Bool
  , ppOptsMinSharing :: Int
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts False False 10 False 2

cryptolPPOpts :: PPOpts -> C.PPOpts
cryptolPPOpts opts =
  C.defaultPPOpts
    { C.useAscii = ppOptsAscii opts
    , C.useBase = ppOptsBase opts
    }

sawPPOpts :: PPOpts -> SAWCorePP.PPOpts
sawPPOpts opts =
  SAWCorePP.defaultPPOpts
    { SAWCorePP.ppBase = ppOptsBase opts
    , SAWCorePP.ppColor = ppOptsColor opts
    , SAWCorePP.ppMinSharing = ppOptsMinSharing opts
    }

quietEvalOpts :: C.EvalOpts
quietEvalOpts = C.EvalOpts C.quietLogger C.defaultPPOpts

commaSep :: [ShowS] -> ShowS
commaSep ss = foldr (.) id (intersperse (showString ",") ss)

showBrackets :: ShowS -> ShowS
showBrackets s = showString "[" . s . showString "]"

showBraces :: ShowS -> ShowS
showBraces s = showString "{" . s . showString "}"

showsProofResult :: PPOpts -> ProofResult -> ShowS
showsProofResult opts r =
  case r of
    ValidProof _ _ -> showString "Valid"
    InvalidProof _ ts _ -> showString "Invalid: [" . showMulti "" ts
    UnfinishedProof st  -> showString "Unfinished: " . shows (length (psGoals st)) . showString " goals remaining"
  where
    opts' = sawPPOpts opts
    showVal t = shows (ppFirstOrderValue opts' t)
    showEqn (x, t) = showEC x . showString " = " . showVal t
    showEC ec = showString (unpack (toShortName (ecName ec)))

    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns


showsSatResult :: PPOpts -> SatResult -> ShowS
showsSatResult opts r =
  case r of
    Unsat _ -> showString "Unsat"
    Sat _ ts -> showString "Sat: [" . showMulti "" ts
    SatUnknown  -> showString "Unknown"
  where
    opts' = sawPPOpts opts
    showVal t = shows (ppFirstOrderValue opts' t)
    showEC ec = showString (unpack (toShortName (ecName ec)))
    showEqn (x, t) = showEC x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showSimpset :: PPOpts -> Simpset a -> String
showSimpset opts ss =
  unlines ("Rewrite Rules" : "=============" : map (show . ppRule) (listRules ss))
  where
    ppRule r =
      PP.pretty '*' PP.<+>
      (PP.nest 2 $ PP.fillSep
       [ ppTerm (lhsRewriteRule r)
       , PP.pretty '=' PP.<+> ppTerm (rhsRewriteRule r) ])
    ppTerm t = SAWCorePP.ppTerm opts' t
    opts' = sawPPOpts opts

showsPrecValue :: PPOpts -> Int -> Value -> ShowS
showsPrecValue opts p v =
  case v of
    VBool True -> showString "true"
    VBool False -> showString "false"
    VString s -> shows s
    VInteger n -> shows n
    VArray vs -> showBrackets $ commaSep $ map (showsPrecValue opts 0) vs
    VTuple vs -> showParen True $ commaSep $ map (showsPrecValue opts 0) vs
    VMaybe (Just v') -> showString "(Just " . showsPrecValue opts 0 v' . showString ")"
    VMaybe Nothing -> showString "Nothing"
    VRecord m -> showBraces $ commaSep $ map showFld (M.toList m)
                   where
                     showFld (n, fv) =
                       showString n . showString "=" . showsPrecValue opts 0 fv

    VLambda {} -> showString "<<function>>"
    VTerm t -> showString (SAWCorePP.scPrettyTerm opts' (ttTerm t))
    VType sig -> showString (pretty sig)
    VReturn {} -> showString "<<monadic>>"
    VBind {} -> showString "<<monadic>>"
    VTopLevel {} -> showString "<<TopLevel>>"
    VSimpset ss -> showString (showSimpset opts ss)
    VProofScript {} -> showString "<<proof script>>"
    VTheorem thm ->
      showString "Theorem " .
      showParen True (showString (prettyProp opts' (thmProp thm)))
    VLLVMCrucibleSetup{} -> showString "<<Crucible Setup>>"
    VLLVMCrucibleSetupValue{} -> showString "<<Crucible SetupValue>>"
    VLLVMCrucibleMethodSpec{} -> showString "<<Crucible MethodSpec>>"
    VLLVMModuleSkeleton s -> shows s
    VLLVMFunctionSkeleton s -> shows s
    VLLVMSkeletonState _ -> showString "<<Skeleton state>>"
    VLLVMFunctionProfile _ -> showString "<<Array sizes for function>>"
    VJavaType {} -> showString "<<Java type>>"
    VLLVMType t -> showString (show (LLVM.ppType t))
    VCryptolModule m -> showString (showCryptolModule m)
    VLLVMModule (Some m) -> showString (CMSLLVM.showLLVMModule m)
    VHeapsterEnv env -> showString (showHeapsterEnv env)
    VJavaClass c -> shows (prettyClass c)
    VProofResult r -> showsProofResult opts r
    VSatResult r -> showsSatResult opts r
    VUninterp u -> showString "Uninterp: " . shows u
    VAIG _ -> showString "<<AIG>>"
    VCFG (LLVM_CFG g) -> showString (show g)
    VCFG (JVM_CFG g) -> showString (show g)
    VGhostVar x -> showParen (p > 10)
                 $ showString "Ghost " . showsPrec 11 x
    VJVMSetup _      -> showString "<<JVM Setup>>"
    VJVMMethodSpec _ -> showString "<<JVM MethodSpec>>"
    VJVMSetupValue x -> shows x
  where
    opts' = sawPPOpts opts

instance Show Value where
    showsPrec p v = showsPrecValue defaultPPOpts p v

indexValue :: Value -> Value -> Value
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value -> String -> Value
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ name
      Just x -> x
lookupValue _ _ = error "lookupValue"

tupleLookupValue :: Value -> Integer -> Value
tupleLookupValue (VTuple vs) i
  | 0 <= i && fromIntegral i < length vs = vs !! fromIntegral i
  | otherwise = error $ "no such tuple index: " ++ show i
tupleLookupValue _ _ = error "tupleLookupValue"

evaluate :: SharedContext -> Term -> IO Concrete.CValue
evaluate sc t =
  (\modmap -> Concrete.evalSharedTerm modmap mempty mempty t) <$>
  scGetModuleMap sc

evaluateTypedTerm :: SharedContext -> TypedTerm -> IO C.Value
evaluateTypedTerm sc (TypedTerm (TypedTermSchema schema) trm) =
  C.runEval mempty . exportValueWithSchema schema =<< evaluate sc trm
evaluateTypedTerm _sc (TypedTerm tp _) =
  fail $ unlines [ "Could not evaluate term with type"
                 , show (CMS.ppTypedTermType tp)
                 ]

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

-- TopLevel Monad --------------------------------------------------------------

-- | Position in the life cycle of a primitive.
data PrimitiveLifecycle
  = Current         {- ^ Currently available in all modes. -}
  | Deprecated      {- ^ Will be removed soon, and available only when
                         requested. -}
  | Experimental    {- ^ Will be made @Current@ soon, but available only by
                         request at the moment. -}
  deriving (Eq, Ord, Show)

-- | TopLevel Read-Only Environment.
data TopLevelRO =
  TopLevelRO
  { roSharedContext :: SharedContext
  , roJavaCodebase  :: JSS.Codebase
  , roOptions       :: Options
  , roHandleAlloc   :: Crucible.HandleAllocator
  , roPosition      :: SS.Pos
  , roProxy         :: AIGProxy
  , roInitWorkDir   :: FilePath
  , roBasicSS       :: SAWSimpset
  , roTheoremDB     :: TheoremDB
  }

data TopLevelRW =
  TopLevelRW
  { rwValues  :: Map SS.LName Value
  , rwTypes   :: Map SS.LName SS.Schema
  , rwTypedef :: Map SS.Name SS.Type
  , rwDocs    :: Map SS.Name String
  , rwCryptol :: CEnv.CryptolEnv
  , rwProofs  :: [Value] {- ^ Values, generated anywhere, that represent proofs. -}
  , rwPPOpts  :: PPOpts
  -- , rwCrucibleLLVMCtx :: Crucible.LLVMContext
  , rwJVMTrans :: CJ.JVMContext
  -- ^ crucible-jvm: Handles and info for classes that have already been translated
  , rwPrimsAvail :: Set PrimitiveLifecycle
  , rwSMTArrayMemoryModel :: Bool
  , rwCrucibleAssertThenAssume :: Bool
  , rwProfilingFile :: Maybe FilePath
  , rwLaxArith :: Bool
  , rwLaxPointerOrdering :: Bool
  , rwDebugIntrinsics :: Bool

  -- FIXME: These might be better split into "simulator hash-consing" and "tactic hash-consing"
  , rwWhat4HashConsing :: Bool
  , rwWhat4HashConsingX86 :: Bool

  , rwPreservedRegs :: [String]
  , rwStackBaseAlign :: Integer
  }

newtype TopLevel a =
  TopLevel (ReaderT TopLevelRO (ReaderT (IORef TopLevelRW) IO) a)
  deriving (Applicative, Functor, Generic, Generic1, Monad, MonadIO, MonadThrow, MonadCatch, MonadMask)

deriving instance MonadReader TopLevelRO TopLevel

instance MonadState TopLevelRW TopLevel where
  get = TopLevel (lift (ReaderT readIORef))
  put s = TopLevel (lift (ReaderT (flip writeIORef s)))
  state f = TopLevel (lift (ReaderT (flip atomicModifyIORef (swap . f))))
    where swap (x, y) = (y, x)

instance Wrapped (TopLevel a) where

instance MonadFail TopLevel where
  fail = throwTopLevel

runTopLevel :: TopLevel a -> TopLevelRO -> IORef TopLevelRW -> IO a
runTopLevel (TopLevel m) ro ref =
  runReaderT (runReaderT m ro) ref

io :: IO a -> TopLevel a
io f = liftIO f
       `catches`
       [ Handler (\(ex :: X86Unsupported) -> handleX86Unsupported ex)
       , Handler (\(ex :: X86Error) -> handleX86Error ex)
       ]
  where
    handleX86Unsupported (X86Unsupported s) =
      throwTopLevel $ "Unsupported x86 feature: " ++ s
    handleX86Error (X86Error s) =
      throwTopLevel $ "Error in x86 code: " ++ s

throwTopLevel :: String -> TopLevel a
throwTopLevel msg = do
  pos <- getPosition
  X.throw $ SS.TopLevelException pos msg

withPosition :: SS.Pos -> TopLevel a -> TopLevel a
withPosition pos (TopLevel m) = TopLevel (local (\ro -> ro{ roPosition = pos }) m)

getPosition :: TopLevel SS.Pos
getPosition = TopLevel (asks roPosition)

getSharedContext :: TopLevel SharedContext
getSharedContext = TopLevel (asks roSharedContext)

getJavaCodebase :: TopLevel JSS.Codebase
getJavaCodebase = TopLevel (asks roJavaCodebase)

getOptions :: TopLevel Options
getOptions = TopLevel (asks roOptions)

getProxy :: TopLevel AIGProxy
getProxy = TopLevel (asks roProxy)

getBasicSS :: TopLevel SAWSimpset
getBasicSS = TopLevel (asks roBasicSS)

localOptions :: (Options -> Options) -> TopLevel a -> TopLevel a
localOptions f (TopLevel m) = TopLevel (local (\x -> x {roOptions = f (roOptions x)}) m)

printOutLnTop :: Verbosity -> String -> TopLevel ()
printOutLnTop v s =
    do opts <- getOptions
       io $ printOutLn opts v s

printOutTop :: Verbosity -> String -> TopLevel ()
printOutTop v s =
    do opts <- getOptions
       io $ printOutFn opts v s

getHandleAlloc :: TopLevel Crucible.HandleAllocator
getHandleAlloc = TopLevel (asks roHandleAlloc)

getTopLevelRO :: TopLevel TopLevelRO
getTopLevelRO = TopLevel ask

getTopLevelRW :: TopLevel TopLevelRW
getTopLevelRW = get

putTopLevelRW :: TopLevelRW -> TopLevel ()
putTopLevelRW rw = put rw

returnProof :: IsValue v => v -> TopLevel v
returnProof v = recordProof v >> return v

recordProof :: IsValue v => v -> TopLevel ()
recordProof v =
  do rw <- getTopLevelRW
     putTopLevelRW rw { rwProofs = toValue v : rwProofs rw }

-- | Access the current state of Java Class translation
getJVMTrans :: TopLevel CJ.JVMContext
getJVMTrans = gets rwJVMTrans

-- | Access the current state of Java Class translation
putJVMTrans :: CJ.JVMContext -> TopLevel ()
putJVMTrans jc =
  do rw <- getTopLevelRW
     putTopLevelRW rw { rwJVMTrans = jc }

-- | Add a newly translated class to the translation
addJVMTrans :: CJ.JVMContext -> TopLevel ()
addJVMTrans trans = do
  rw <- getTopLevelRW
  let jvmt = rwJVMTrans rw
  putTopLevelRW ( rw { rwJVMTrans = trans <> jvmt })

maybeInsert :: Ord k => k -> Maybe a -> Map k a -> Map k a
maybeInsert _ Nothing m = m
maybeInsert k (Just x) m = M.insert k x m

extendEnv ::
  SharedContext ->
  SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> TopLevelRW -> IO TopLevelRW
extendEnv sc x mt md v rw =
  do ce' <-
       case v of
         VTerm t ->
           pure $ CEnv.bindTypedTerm (ident, t) ce
         VType s ->
           pure $ CEnv.bindType (ident, s) ce
         VInteger n ->
           pure $ CEnv.bindInteger (ident, n) ce
         VCryptolModule m ->
           pure $ CEnv.bindCryptolModule (modname, m) ce
         VString s ->
           do tt <- typedTermOfString sc (unpack s)
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         VBool b ->
           do tt <- typedTermOfBool sc b
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         _ ->
           pure ce
     pure $
      rw { rwValues  = M.insert name v (rwValues rw)
         , rwTypes   = maybeInsert name mt (rwTypes rw)
         , rwDocs    = maybeInsert (SS.getVal name) md (rwDocs rw)
         , rwCryptol = ce'
         }
  where
    name = x
    ident = T.packIdent (SS.getOrig x)
    modname = T.packModName [pack (SS.getOrig x)]
    ce = rwCryptol rw

typedTermOfString :: SharedContext -> String -> IO TypedTerm
typedTermOfString sc str =
  do let schema = Cryptol.tMono (Cryptol.tString (length str))
     bvNat <- scGlobalDef sc "Prelude.bvNat"
     bvNat8 <- scApply sc bvNat =<< scNat sc 8
     byteT <- scBitvector sc 8
     let scChar c = scApply sc bvNat8 =<< scNat sc (fromIntegral (fromEnum c))
     ts <- traverse scChar str
     trm <- scVector sc byteT ts
     pure (TypedTerm (TypedTermSchema schema) trm)

typedTermOfBool :: SharedContext -> Bool -> IO TypedTerm
typedTermOfBool sc b =
  do let schema = Cryptol.tMono Cryptol.tBit
     trm <- scBool sc b
     pure (TypedTerm (TypedTermSchema schema) trm)


-- Other SAWScript Monads ------------------------------------------------------

type CrucibleSetup ext = Setup.CrucibleSetupT ext TopLevel

-- | 'CrucibleMethodSpecIR' requires a specific syntax extension, but our method
--   specifications should be polymorphic in the underlying architecture
-- type LLVMCrucibleMethodSpecIR = CMSLLVM.AllLLVM CMS.CrucibleMethodSpecIR

newtype LLVMCrucibleSetupM a =
  LLVMCrucibleSetupM
    { runLLVMCrucibleSetupM ::
        forall arch.
        (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
        CrucibleSetup (CMSLLVM.LLVM arch) a
    }
  deriving Functor

instance Applicative LLVMCrucibleSetupM where
  pure x = LLVMCrucibleSetupM (pure x)
  LLVMCrucibleSetupM f <*> LLVMCrucibleSetupM m = LLVMCrucibleSetupM (f <*> m)

instance Monad LLVMCrucibleSetupM where
  return = pure
  LLVMCrucibleSetupM m >>= f =
    LLVMCrucibleSetupM (m >>= runLLVMCrucibleSetupM . f)

throwCrucibleSetup :: ProgramLoc -> String -> CrucibleSetup ext a
throwCrucibleSetup loc msg = X.throw $ SS.CrucibleSetupException loc msg

throwLLVM :: ProgramLoc -> String -> LLVMCrucibleSetupM a
throwLLVM loc msg = LLVMCrucibleSetupM $ throwCrucibleSetup loc msg

-- | This gets more accurate locations than @lift (lift getPosition)@ because
--   of the @local@ in the @fromValue@ instance for @CrucibleSetup@
getW4Position :: Text -> CrucibleSetup arch ProgramLoc
getW4Position s = SS.toW4Loc s <$> lift (asks roPosition)

--

type JVMSetup = CrucibleSetup CJ.JVM

newtype JVMSetupM a = JVMSetupM { runJVMSetupM :: JVMSetup a }
  deriving (Applicative, Functor, Monad)

--
newtype ProofScript a = ProofScript { unProofScript :: ExceptT (SolverStats, CEX) (StateT ProofState TopLevel) a }
 deriving (Functor, Applicative, Monad)

runProofScript :: ProofScript a -> ProofGoal -> Maybe ProgramLoc -> Text -> TopLevel ProofResult
runProofScript (ProofScript m) gl ploc rsn =
  do pos <- getPosition
     ps <- io (startProof gl pos ploc rsn)
     (r,pstate) <- runStateT (runExceptT m) ps
     case r of
       Left (stats,cex) -> return (SAWScript.Proof.InvalidProof stats cex pstate)
       Right _ ->
         do sc <- getSharedContext
            db <- roTheoremDB <$> getTopLevelRO
            io (finishProof sc db pstate)

scriptTopLevel :: TopLevel a -> ProofScript a
scriptTopLevel m = ProofScript (lift (lift m))

instance MonadIO ProofScript where
  liftIO m = ProofScript (liftIO m)

instance MonadFail ProofScript where
  fail msg = ProofScript (fail msg)

instance MonadState ProofState ProofScript where
  get = ProofScript get
  put x = ProofScript (put x)

instance MonadError (SolverStats, CEX) ProofScript where
  throwError cex = ProofScript (throwError cex)
  catchError (ProofScript m) f = ProofScript (catchError m (unProofScript . f))

-- IsValue class ---------------------------------------------------------------

-- | Used for encoding primitive operations in the Value type.
class IsValue a where
    toValue :: a -> Value

class FromValue a where
    fromValue :: Value -> a

instance (FromValue a, IsValue b) => IsValue (a -> b) where
    toValue f = VLambda (\v -> return (toValue (f (fromValue v))))

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
    fromValue (VBind _pos m1 v2) = do
      v1 <- fromValue m1
      m2 <- applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue TopLevel"

instance IsValue a => IsValue (ProofScript a) where
    toValue m = VProofScript (fmap toValue m)

instance FromValue a => FromValue (ProofScript a) where
    fromValue (VProofScript m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind _pos m1 v2) = do
      v1 <- fromValue m1
      m2 <- scriptTopLevel $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue ProofScript"

---------------------------------------------------------------------------------
instance IsValue a => IsValue (LLVMCrucibleSetupM a) where
    toValue m = VLLVMCrucibleSetup (fmap toValue m)

instance FromValue a => FromValue (LLVMCrucibleSetupM a) where
    fromValue (VLLVMCrucibleSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind pos m1 v2) = LLVMCrucibleSetupM $ do
      -- TODO: Should both of these be run with the new position?
      v1 <- underStateT (withPosition pos) (runLLVMCrucibleSetupM (fromValue m1))
      m2 <- lift $ applyValue v2 v1
      underStateT (withPosition pos) (runLLVMCrucibleSetupM (fromValue m2))
    fromValue _ = error "fromValue CrucibleSetup"

instance IsValue a => IsValue (JVMSetupM a) where
    toValue m = VJVMSetup (fmap toValue m)

instance FromValue a => FromValue (JVMSetupM a) where
    fromValue (VJVMSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind _pos m1 v2) = JVMSetupM $ do
      v1 <- runJVMSetupM (fromValue m1)
      m2 <- lift $ applyValue v2 v1
      runJVMSetupM (fromValue m2)
    fromValue _ = error "fromValue JVMSetup"

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

-----------------------------------------------------------------------------------


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

instance IsValue String where
    toValue n = VString (pack n)

instance FromValue String where
    fromValue (VString n) = unpack n
    fromValue _ = error "fromValue String"

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

instance IsValue Theorem where
    toValue t = VTheorem t

instance FromValue Theorem where
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

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

-- Error handling --------------------------------------------------------------

underStateT :: (forall b. m b -> m b) -> StateT s m a -> StateT s m a
underStateT doUnder action = StateT $ \s -> doUnder (runStateT action s)

underReaderT :: (forall b. m b -> m b) -> ReaderT s m a -> ReaderT s m a
underReaderT doUnder action = ReaderT $ \env -> doUnder (runReaderT action env)

underExceptT :: (forall b. m b -> m b) -> ExceptT s m a -> ExceptT s m a
underExceptT doUnder action = ExceptT $ doUnder (runExceptT action)

-- | Implement stack tracing by adding error handlers that rethrow
-- user errors, prepended with the given string.
addTrace :: String -> Value -> Value
addTrace str val =
  case val of
    VLambda        f -> VLambda        (\x -> addTrace str `fmap` addTraceTopLevel str (f x))
    VTopLevel      m -> VTopLevel      (addTrace str `fmap` addTraceTopLevel str m)
    VProofScript   m -> VProofScript   (addTrace str `fmap` addTraceProofScript str m)
    VBind pos v1 v2  -> VBind pos      (addTrace str v1) (addTrace str v2)
    VLLVMCrucibleSetup (LLVMCrucibleSetupM m) -> VLLVMCrucibleSetup $ LLVMCrucibleSetupM $
        addTrace str `fmap` underStateT (addTraceTopLevel str) m
    _                -> val

-- | Wrap an action with a handler that catches and rethrows user
-- errors with an extended message.
addTraceIO :: forall a. String -> IO a -> IO a
addTraceIO str action = X.catches action
  [ X.Handler handleTopLevel
  , X.Handler handleTrace
  , X.Handler handleIO
  ]
  where
    rethrow msg = X.throwIO . SS.TraceException $ mconcat [str, ":\n", msg]
    handleTopLevel :: SS.TopLevelException -> IO a
    handleTopLevel e = rethrow $ show e
    handleTrace (SS.TraceException msg) = rethrow msg
    handleIO :: X.IOException -> IO a
    handleIO e
      | IOError.isUserError e = rethrow . init . drop 12 $ show e
      | otherwise = X.throwIO e

-- | Similar to 'addTraceIO', but for state monads built from 'TopLevel'.
addTraceStateT :: String -> StateT s TopLevel a -> StateT s TopLevel a
addTraceStateT str = underStateT (addTraceTopLevel str)

addTraceProofScript :: String -> ProofScript a -> ProofScript a
addTraceProofScript str (ProofScript m) = ProofScript (underExceptT (underStateT (addTraceTopLevel str)) m)

-- | Similar to 'addTraceIO', but for reader monads built from 'TopLevel'.
addTraceReaderT :: String -> ReaderT s TopLevel a -> ReaderT s TopLevel a
addTraceReaderT str = underReaderT (addTraceTopLevel str)

-- | Similar to 'addTraceIO', but for the 'TopLevel' monad.
addTraceTopLevel :: String -> TopLevel a -> TopLevel a
addTraceTopLevel str action = action & _Wrapped' %~
  underReaderT (underReaderT (liftIO . addTraceIO str))

data SkeletonState = SkeletonState
  { _skelArgs :: [(Maybe TypedTerm, Maybe (CMSLLVM.AllLLVM CMS.SetupValue), Maybe Text)]
  }
makeLenses ''SkeletonState
