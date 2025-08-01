{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module SAWServer.SAWServer
  ( module SAWServer.SAWServer
  ) where

import Prelude hiding (mod)
import Control.Lens ( Lens', view, lens, over )
import Data.Aeson (FromJSON(..), ToJSON(..), withText)
import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Parameterized.Pair ( Pair(..) )
import Data.Parameterized.Some ( Some(..) )
import Data.Text (Text)
import qualified Data.Text as T
import qualified Crypto.Hash as Hash
--import qualified Crypto.Hash.Conduit as Hash
import System.Directory (getCurrentDirectory)
import System.Environment (lookupEnv)
import System.IO.Silently (silence)

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema)
#if USE_BUILTIN_ABC
import qualified Data.ABC.GIA as GIA
#else
import qualified Data.AIG as AIG
#endif
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator, newHandleAllocator)
import qualified Lang.Crucible.JVM as CJ
import qualified Lang.JVM.Codebase as JSS
import Mir.Generator (RustModule)
import Mir.Intrinsics (MIR)
import Mir.Mir (Adt)

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import qualified SAWCentral.Trace as Trace (empty)

--import qualified CryptolSAWCore.CryptolEnv as CryptolEnv
import SAWCore.Module (emptyModule)
import SAWCore.SharedTerm (mkSharedContext, scLoadModule, scGetModuleMap)
import SAWCore.Term.Functor (mkModuleName)
import CryptolSAWCore.TypedTerm (TypedTerm, CryptolModule)

import SAWCentral.Crucible.LLVM.X86 (defaultStackBaseAlign)
import qualified SAWCentral.Crucible.Common as CC (defaultSAWCoreBackendTimeout, PathSatSolver(..))
import qualified SAWCentral.Crucible.Common.MethodSpec as CMS (ProvedSpec, GhostGlobal)
import SAWCentral.Crucible.Common.Setup.Builtins (CheckPointsToType)
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMS (SomeLLVM, LLVMModule)
import SAWCentral.Options (processEnv, defaultOptions)
import SAWCentral.Position (Pos(..))
import SAWCentral.Prover.Rewrite (basic_ss)
import SAWCentral.Proof (emptyTheoremDB)
import SAWCentral.Value (AIGProxy(..), BuiltinContext(..), JVMSetupM, LLVMCrucibleSetupM, TopLevelRO(..), TopLevelRW(..), SAWSimpset,JavaCodebase(..))
import SAWCentral.Yosys.State (YosysSequential)
import SAWCentral.Yosys.Theorem (YosysImport, YosysTheorem)
import qualified CryptolSAWCore.Prelude as CryptolSAW
import CryptolSAWCore.CryptolEnv (initCryptolEnv, bindTypedTerm)
import qualified Cryptol.Utils.Ident as Cryptol
import CryptolSAWCore.Monadify (defaultMonEnv)
import SAWCentral.Prover.MRSolver (emptyMREnv)
import SAWCentral.SolverCache (lazyOpenSolverCache)

import qualified Argo
--import qualified CryptolServer (validateServerState, ServerState(..))
--import qualified CryptolServer (validateServerState, ServerState(..))
--import qualified CryptolServer (validateServerState, ServerState(..))
--import qualified CryptolServer (validateServerState, ServerState(..))
import SAWServer.Exceptions
    ( serverValNotFound,
      notAnLLVMModule,
      notAnLLVMSetup,
      notAnLLVMMethodSpecIR,
      notASimpset,
      notATerm,
      notAJVMClass,
      notAJVMMethodSpecIR,
      notAYosysImport,
      notAYosysTheorem, notAYosysSequential,
      notAMIRModule, notAMIRMethodSpecIR, notAMIRAdt
    )

type SAWCont = (SAWEnv, SAWTask)

type CryptolAST = P.Expr P.PName

data SAWTask
  = ProofScriptTask
  | LLVMCrucibleSetup ServerName
  | JVMSetup ServerName
  | MIRSetup ServerName

instance Show SAWTask where
  show ProofScriptTask = "ProofScript"
  show (LLVMCrucibleSetup n) = "(LLVMCrucibleSetup" ++ show n ++ ")"
  show (JVMSetup n) = "(JVMSetup" ++ show n ++ ")"
  show (MIRSetup n) = "(MIRSetup" ++ show n ++ ")"


data CrucibleSetupVal ty e
  = NullValue
  | ArrayValue (Maybe ty) [CrucibleSetupVal ty e]
  | StructValue (Maybe ServerName) [CrucibleSetupVal ty e]
    -- ^ The @'Maybe' 'ServerName'@ value represents a possible MIR
    -- ADT. This should always be 'Just' with MIR verification and
    -- 'Nothing' with LLVM or JVM verification.
  | EnumValue ServerName Text [CrucibleSetupVal ty e]
  | TupleValue [CrucibleSetupVal ty e]
  | SliceValue (CrucibleSetupVal ty e)
  | SliceRangeValue (CrucibleSetupVal ty e) Int Int
  | StrSliceValue (CrucibleSetupVal ty e)
  | StrSliceRangeValue (CrucibleSetupVal ty e) Int Int
  -- | RecordValue [(String, CrucibleSetupVal e)]
  | FieldLValue (CrucibleSetupVal ty e) Text
  | CastLValue (CrucibleSetupVal ty e) ty
  | UnionLValue (CrucibleSetupVal ty e) Text
  | ElementLValue (CrucibleSetupVal ty e) Int
  | GlobalInitializer Text
  | GlobalLValue Text
  | NamedValue ServerName
  | CryptolExpr e
  | FreshExpandedValue Text ty
  deriving stock (Foldable, Functor, Traversable)

data SetupStep ty
  = SetupReturn (CrucibleSetupVal ty CryptolAST) -- ^ The return value
  | SetupFresh ServerName Text ty -- ^ Server name to save in, debug name, fresh variable type
  | SetupAlloc ServerName ty Bool (Maybe Int) -- ^ Server name to save in, type of allocation, mutability, alignment
  | SetupGhostValue ServerName Text CryptolAST -- ^ Variable, term
  | SetupPointsTo (CrucibleSetupVal ty CryptolAST)
                  (CrucibleSetupVal ty CryptolAST)
                  (Maybe (CheckPointsToType ty))
                  (Maybe CryptolAST)
                  -- ^ The source, the target, the type to check the target,
                  --   and the condition that must hold in order for the source to point to the target
  | SetupPointsToBitfield (CrucibleSetupVal ty CryptolAST)
                          Text
                          (CrucibleSetupVal ty CryptolAST)
                          -- ^ The source bitfield,
                          --   the name of the field within the bitfield,
                          --   and the target.
  | SetupExecuteFunction [CrucibleSetupVal ty CryptolAST] -- ^ Function's arguments
  | SetupPrecond CryptolAST -- ^ Function's precondition
  | SetupPostcond CryptolAST -- ^ Function's postcondition

instance Show (SetupStep ty) where
  show _ = "⟨SetupStep⟩" -- TODO

instance ToJSON SAWTask where
  toJSON = toJSON . show

data SAWState =
  SAWState
    { _sawEnv :: SAWEnv
    , _sawBIC :: BuiltinContext
    , _sawTask :: [(SAWTask, SAWEnv)]
    , _sawTopLevelRO :: TopLevelRO
    , _sawTopLevelRW :: TopLevelRW
    , _trackedFiles :: Map FilePath (Hash.Digest Hash.SHA256)
    }

instance Show SAWState where
  show (SAWState e _ t _ _ tf) = "(SAWState " ++ show e ++ " _sc_ " ++ show t ++ " _ro_ _rw" ++ show tf ++ ")"

sawEnv :: Lens' SAWState SAWEnv
sawEnv = lens _sawEnv (\v e -> v { _sawEnv = e })

sawBIC :: Lens' SAWState BuiltinContext
sawBIC = lens _sawBIC (\v bic -> v { _sawBIC = bic })

sawTask :: Lens' SAWState [(SAWTask, SAWEnv)]
sawTask = lens _sawTask (\v t -> v { _sawTask = t })

sawTopLevelRO :: Lens' SAWState TopLevelRO
sawTopLevelRO = lens _sawTopLevelRO (\v ro -> v { _sawTopLevelRO = ro })

sawTopLevelRW :: Lens' SAWState TopLevelRW
sawTopLevelRW = lens _sawTopLevelRW (\v rw -> v { _sawTopLevelRW = rw })

trackedFiles :: Lens' SAWState (Map FilePath (Hash.Digest Hash.SHA256))
trackedFiles = lens _trackedFiles (\v tf -> v { _trackedFiles = tf })


pushTask :: SAWTask -> Argo.Command SAWState ()
pushTask t = Argo.modifyState mod
  where mod (SAWState env bic stack ro rw tf) =
          SAWState env bic ((t, env) : stack) ro rw tf

dropTask :: Argo.Command SAWState ()
dropTask = Argo.modifyState mod
  where mod (SAWState _ _ [] _ _ _) = error "Internal error - stack underflow"
        mod (SAWState _ sc ((_t, env):stack) ro rw tf) =
          SAWState env sc stack ro rw tf

getHandleAlloc :: Argo.Command SAWState Crucible.HandleAllocator
getHandleAlloc = roHandleAlloc . view sawTopLevelRO <$> Argo.getState

initialState :: (FilePath -> IO ByteString) -> IO SAWState
initialState readFileFn =
  let ?fileReader = readFileFn in
  -- silence prevents output on stdout, which suppresses defaulting
  -- warnings from the Cryptol type checker
  silence $
  do sc <- mkSharedContext
     opts <- processEnv defaultOptions
     CryptolSAW.scLoadPreludeModule sc
     CryptolSAW.scLoadCryptolModule sc
     let mn = mkModuleName ["SAWScript"]
     mm <- scGetModuleMap sc
     scLoadModule sc (emptyModule mn)
     ss <- basic_ss sc
     let bic = BuiltinContext { biSharedContext = sc
                              , biBasicSS = ss
                              }
     cenv <- initCryptolEnv sc
     halloc <- Crucible.newHandleAllocator
     jvmTrans <- CJ.mkInitialJVMContext halloc
     cwd <- getCurrentDirectory
     mb_cache <- lookupEnv "SAW_SOLVER_CACHE_PATH" >>= \case
       Just path | not (null path) -> Just <$> lazyOpenSolverCache path
       _ -> return Nothing
     let ro = TopLevelRO
                { roOptions = opts
                , roHandleAlloc = halloc
#if USE_BUILTIN_ABC
                , roProxy = AIGProxy GIA.proxy
#else
                , roProxy = AIGProxy AIG.basicProxy
#endif
                , roInitWorkDir = cwd
                , roBasicSS = ss
                , roSubshell = fail "SAW server does not support subshells."
                , roProofSubshell = fail "SAW server does not support subshells."
                }
         rw = TopLevelRW
                { rwValueInfo = mempty
                , rwTypeInfo = mempty
                , rwDocs = mempty
                , rwCryptol = cenv
                , rwPosition = PosInternal "SAWServer"
                , rwStackTrace = Trace.empty
                , rwLocalEnv = []
                , rwMonadify = let ?mm = mm in defaultMonEnv
                , rwMRSolverEnv = emptyMREnv
                , rwPPOpts = PPS.defaultOpts
                , rwSolverCache = mb_cache
                , rwTheoremDB = emptyTheoremDB
                , rwSharedContext = sc
                , rwJVMTrans = jvmTrans
                , rwPrimsAvail = mempty
                , rwSMTArrayMemoryModel = False
                , rwProfilingFile = Nothing
                , rwCrucibleAssertThenAssume = False
                , rwLaxArith = False
                , rwLaxPointerOrdering = False
                , rwLaxLoadsAndStores = False
                , rwDebugIntrinsics = True
                , rwWhat4HashConsing = False
                , rwWhat4HashConsingX86 = False
                , rwWhat4Eval = False
                , rwStackBaseAlign = defaultStackBaseAlign
                , rwProofs = []
                , rwPreservedRegs = []
                , rwAllocSymInitCheck = True
                , rwWhat4PushMuxOps = False
                , rwNoSatisfyingWriteFreshConstant = True
                , rwCrucibleTimeout = CC.defaultSAWCoreBackendTimeout
                , rwPathSatSolver = CC.PathSat_Z3
                , rwSkipSafetyProofs = False
                , rwSingleOverrideSpecialCase = False
                , rwSequentGoals = False
                , rwJavaCodebase = JavaUninitialized
                }
     return (SAWState emptyEnv bic [] ro rw M.empty)

-- NOTE: KWF: 2020-04-22: This function could introduce a race condition: if a
-- file changes on disk after its hash is computed by validateSAWState, but
-- before the function returns and its result is used to inform whether to
-- recompute a cached result, the cached result may be used even if it is
-- associated with stale filesystem state. See the discussion of this issue at:
-- https://github.com/GaloisInc/argo/pull/70#discussion_r412462908

-- validateSAWState :: SAWState -> IO Bool
-- validateSAWState sawState =
--   checkAll
--     [ CryptolServer.validateServerState cryptolState
--     , checkAll $ map (uncurry checkHash) (M.assocs (view trackedFiles sawState))
--     ]
--   where
--     checkAll [] = pure True
--     checkAll (c : cs) =
--       do result <- c
--          if result
--            then checkAll cs
--            else pure False

--     checkHash path hash =
--       do currentHash <- Hash.hashFile path
--          pure (currentHash == hash)

--     cryptolState =
--       CryptolServer.ServerState Nothing
--         (CryptolEnv.eModuleEnv . rwCryptol . view sawTopLevelRW $ sawState)


newtype SAWEnv =
  SAWEnv { sawEnvBindings :: Map ServerName ServerVal }
  deriving stock Show

emptyEnv :: SAWEnv
emptyEnv = SAWEnv M.empty

newtype ServerName = ServerName Text
  deriving stock (Eq, Show, Ord)

instance ToJSON ServerName where
  toJSON (ServerName n) = toJSON n

instance FromJSON ServerName where
  parseJSON = withText "name" (pure . ServerName)

data CrucibleSetupTypeRepr :: Type -> Type where
  UnitRepr :: CrucibleSetupTypeRepr ()
  TypedTermRepr :: CrucibleSetupTypeRepr TypedTerm

data ServerVal
  = VTerm TypedTerm
  | VSimpset SAWSimpset
  | VType Cryptol.Schema
  | VCryptolModule CryptolModule -- from SAW, includes Term mappings
  | VJVMClass JSS.Class
  | VJVMCrucibleSetup (Pair CrucibleSetupTypeRepr JVMSetupM)
  | VLLVMCrucibleSetup (Pair CrucibleSetupTypeRepr LLVMCrucibleSetupM)
  | VLLVMModule (Some CMS.LLVMModule)
  | VMIRModule RustModule
  | VMIRAdt Adt
  | VJVMMethodSpecIR (CMS.ProvedSpec CJ.JVM)
  | VLLVMMethodSpecIR (CMS.SomeLLVM CMS.ProvedSpec)
  | VMIRMethodSpecIR (CMS.ProvedSpec MIR)
  | VGhostVar CMS.GhostGlobal
  | VYosysImport YosysImport
  | VYosysTheorem YosysTheorem
  | VYosysSequential YosysSequential

instance Show ServerVal where
  show (VTerm t) = "(VTerm " ++ show t ++ ")"
  show (VSimpset ss) = "(VSimpset " ++ show ss ++ ")"
  show (VType t) = "(VType " ++ show t ++ ")"
  show (VCryptolModule _) = "VCryptolModule"
  show (VJVMClass _) = "VJVMClass"
  show (VJVMCrucibleSetup _) = "VJVMCrucibleSetup"
  show (VLLVMCrucibleSetup _) = "VLLVMCrucibleSetup"
  show (VLLVMModule (Some _)) = "VLLVMModule"
  show (VMIRModule _) = "VMIRModule"
  show (VMIRAdt _) = "VMIRAdt"
  show (VLLVMMethodSpecIR _) = "VLLVMMethodSpecIR"
  show (VJVMMethodSpecIR _) = "VJVMMethodSpecIR"
  show (VMIRMethodSpecIR _) = "VMIRMethodSpecIR"
  show (VGhostVar x) = "(VGhostVar " ++ show x ++ ")"
  show (VYosysImport _) = "VYosysImport"
  show (VYosysTheorem _) = "VYosysTheorem"
  show (VYosysSequential _) = "VYosysSequential"

class IsServerVal a where
  toServerVal :: a -> ServerVal

instance IsServerVal TypedTerm where
  toServerVal = VTerm

instance IsServerVal SAWSimpset where
  toServerVal = VSimpset

instance IsServerVal Cryptol.Schema where
  toServerVal = VType

instance IsServerVal CryptolModule where
  toServerVal = VCryptolModule

instance IsServerVal (CMS.ProvedSpec CJ.JVM) where
  toServerVal = VJVMMethodSpecIR

instance IsServerVal (CMS.SomeLLVM CMS.ProvedSpec) where
  toServerVal = VLLVMMethodSpecIR

instance IsServerVal (CMS.ProvedSpec MIR) where
  toServerVal = VMIRMethodSpecIR

instance IsServerVal JSS.Class where
  toServerVal = VJVMClass

instance IsServerVal CMS.GhostGlobal where
  toServerVal = VGhostVar

instance IsServerVal YosysImport where
  toServerVal = VYosysImport

instance IsServerVal YosysTheorem where
  toServerVal = VYosysTheorem

instance IsServerVal YosysSequential where
  toServerVal = VYosysSequential

class KnownCrucibleSetupType a where
  knownCrucibleSetupRepr :: CrucibleSetupTypeRepr a

instance KnownCrucibleSetupType () where
  knownCrucibleSetupRepr = UnitRepr

instance KnownCrucibleSetupType TypedTerm where
  knownCrucibleSetupRepr = TypedTermRepr

instance KnownCrucibleSetupType a => IsServerVal (LLVMCrucibleSetupM a) where
  toServerVal x = VLLVMCrucibleSetup (Pair knownCrucibleSetupRepr x)

instance IsServerVal (Some CMS.LLVMModule) where
  toServerVal = VLLVMModule

instance IsServerVal RustModule where
  toServerVal = VMIRModule

instance IsServerVal Adt where
  toServerVal = VMIRAdt

setServerVal :: IsServerVal val => ServerName -> val -> Argo.Command SAWState ()
setServerVal name val =
  do Argo.debugLog $ "Saving " <> (T.pack (show name))
     Argo.modifyState $
       over sawEnv $
       \(SAWEnv env) ->
         SAWEnv (M.insert name (toServerVal val) env)
     Argo.debugLog $ "Saved " <> (T.pack (show name))
     st <- Argo.getState @SAWState
     Argo.debugLog $ "State is " <> T.pack (show st)


getServerVal :: ServerName -> Argo.Command SAWState ServerVal
getServerVal n =
  do sawenv <- view sawEnv <$> Argo.getState
     st <- Argo.getState @SAWState
     Argo.debugLog $ "Looking up " <> T.pack (show n) <> " in " <> T.pack (show st)
     case getServerValEither sawenv n of
       Left ex -> Argo.raise ex
       Right val -> return val

getServerValEither :: SAWEnv -> ServerName -> Either Argo.JSONRPCException ServerVal
getServerValEither (SAWEnv serverEnv) n =
  case M.lookup n serverEnv of
    Nothing -> Left (serverValNotFound n)
    Just val -> Right val

bindCryptolVar :: Text -> TypedTerm -> Argo.Command SAWState ()
bindCryptolVar x t =
  do Argo.modifyState $ over sawTopLevelRW $ \rw ->
       rw { rwCryptol = bindTypedTerm (Cryptol.mkIdent x, t) (rwCryptol rw) }

getJVMClass :: ServerName -> Argo.Command SAWState JSS.Class
getJVMClass n =
  do v <- getServerVal n
     case v of
       VJVMClass c -> return c
       _other -> Argo.raise (notAJVMClass n)

getJVMMethodSpecIR :: ServerName -> Argo.Command SAWState (CMS.ProvedSpec CJ.JVM)
getJVMMethodSpecIR n =
  do v <- getServerVal n
     case v of
       VJVMMethodSpecIR ir -> return ir
       _other -> Argo.raise (notAJVMMethodSpecIR n)

getLLVMModule :: ServerName -> Argo.Command SAWState (Some CMS.LLVMModule)
getLLVMModule n =
  do v <- getServerVal n
     case v of
       VLLVMModule m -> return m
       _other -> Argo.raise (notAnLLVMModule n)

getMIRMethodSpecIR :: ServerName -> Argo.Command SAWState (CMS.ProvedSpec MIR)
getMIRMethodSpecIR n =
  do v <- getServerVal n
     case v of
       VMIRMethodSpecIR ir -> return ir
       _other -> Argo.raise (notAMIRMethodSpecIR n)

getMIRModule :: ServerName -> Argo.Command SAWState RustModule
getMIRModule n =
  do v <- getServerVal n
     case v of
       VMIRModule m -> return m
       _other -> Argo.raise (notAMIRModule n)

getMIRAdt :: ServerName -> Argo.Command SAWState Adt
getMIRAdt n =
  do v <- getServerVal n
     case mirAdtEither n v of
       Left ex -> Argo.raise ex
       Right adt -> pure adt

getMIRAdtEither :: SAWEnv -> ServerName -> Either Argo.JSONRPCException Adt
getMIRAdtEither sawenv n =
  do v <- getServerValEither sawenv n
     mirAdtEither n v

mirAdtEither :: ServerName -> ServerVal -> Either Argo.JSONRPCException Adt
mirAdtEither n v =
  case v of
    VMIRAdt adt -> Right adt
    _other -> Left (notAMIRAdt n)

getLLVMSetup :: ServerName -> Argo.Command SAWState (Pair CrucibleSetupTypeRepr LLVMCrucibleSetupM)
getLLVMSetup n =
  do v <- getServerVal n
     case v of
       VLLVMCrucibleSetup setup -> return setup
       _other -> Argo.raise (notAnLLVMSetup n)

getLLVMMethodSpecIR :: ServerName -> Argo.Command SAWState (CMS.SomeLLVM CMS.ProvedSpec)
getLLVMMethodSpecIR n =
  do v <- getServerVal n
     case v of
       VLLVMMethodSpecIR ir -> return ir
       _other -> Argo.raise (notAnLLVMMethodSpecIR n)

getSimpset :: ServerName -> Argo.Command SAWState SAWSimpset
getSimpset n =
  do v <- getServerVal n
     case v of
       VSimpset ss -> return ss
       _other -> Argo.raise (notASimpset n)

getTerm :: ServerName -> Argo.Command SAWState TypedTerm
getTerm n =
  do v <- getServerVal n
     case v of
       VTerm t -> return t
       _other -> Argo.raise (notATerm n)

getGhost :: ServerName -> Argo.Command SAWState CMS.GhostGlobal
getGhost n =
  do v <- getServerVal n
     case v of
       VGhostVar x -> return x
       _other -> error "TODO" -- raise (notAGhostVariable n) -- TODO

getGhosts :: Argo.Command SAWState [(ServerName, CMS.GhostGlobal)]
getGhosts =
  do SAWEnv serverEnv <- view sawEnv <$> Argo.getState
     return [ (n, g) | (n, VGhostVar g) <- M.toList serverEnv ]

getYosysImport :: ServerName -> Argo.Command SAWState YosysImport
getYosysImport n =
  do v <- getServerVal n
     case v of
       VYosysImport t -> return t
       _other -> Argo.raise (notAYosysImport n)

getYosysTheorem :: ServerName -> Argo.Command SAWState YosysTheorem
getYosysTheorem n =
  do v <- getServerVal n
     case v of
       VYosysTheorem t -> return t
       _other -> Argo.raise (notAYosysTheorem n)

getYosysSequential :: ServerName -> Argo.Command SAWState YosysSequential
getYosysSequential n =
  do v <- getServerVal n
     case v of
       VYosysSequential t -> return t
       _other -> Argo.raise (notAYosysSequential n)
