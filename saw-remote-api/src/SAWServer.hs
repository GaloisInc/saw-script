{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module SAWServer
  ( module SAWServer
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
import qualified Crypto.Hash.Conduit as Hash
import System.Directory (getCurrentDirectory)
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
import qualified Text.LLVM.AST as LLVM
import qualified Lang.JVM.Codebase as JSS
import qualified Verifier.SAW.CryptolEnv as CryptolEnv
import Verifier.SAW.Module (emptyModule)
import Verifier.SAW.SharedTerm (mkSharedContext, scLoadModule)
import Verifier.SAW.Term.Functor (mkModuleName)
import Verifier.SAW.TypedTerm (TypedTerm, CryptolModule)


import SAWScript.Crucible.LLVM.Builtins (CheckPointsToType)
import SAWScript.Crucible.LLVM.X86 (defaultStackBaseAlign)
import qualified SAWScript.Crucible.Common.MethodSpec as CMS (CrucibleMethodSpecIR, GhostGlobal)
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CMS (SomeLLVM, LLVMModule)
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Options (defaultOptions)
import SAWScript.Position (Pos(..))
import SAWScript.Prover.Rewrite (basic_ss)
import SAWScript.Value (AIGProxy(..), BuiltinContext(..), JVMSetupM, LLVMCrucibleSetupM, TopLevelRO(..), TopLevelRW(..), defaultPPOpts)
import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW
import Verifier.SAW.CryptolEnv (initCryptolEnv, bindTypedTerm)
import Verifier.SAW.Rewriter (Simpset)
import qualified Cryptol.Utils.Ident as Cryptol

import qualified Argo
import qualified CryptolServer (validateServerState, ServerState(..))
import SAWServer.Exceptions
    ( serverValNotFound,
      notAnLLVMModule,
      notAnLLVMSetup,
      notAnLLVMMethodSpecIR,
      notASimpset,
      notATerm,
      notAJVMClass,
      notAJVMMethodSpecIR )

type SAWCont = (SAWEnv, SAWTask)

type CryptolAST = P.Expr P.PName

data SAWTask
  = ProofScriptTask
  | LLVMCrucibleSetup ServerName
  | JVMSetup ServerName

instance Show SAWTask where
  show ProofScriptTask = "ProofScript"
  show (LLVMCrucibleSetup n) = "(LLVMCrucibleSetup" ++ show n ++ ")"
  show (JVMSetup n) = "(JVMSetup" ++ show n ++ ")"


data CrucibleSetupVal e
  = NullValue
  | ArrayValue [CrucibleSetupVal e]
  | TupleValue [CrucibleSetupVal e]
  -- | RecordValue [(String, CrucibleSetupVal e)]
  | FieldLValue (CrucibleSetupVal e) String
  | ElementLValue (CrucibleSetupVal e) Int
  | GlobalInitializer String
  | GlobalLValue String
  | NamedValue ServerName
  | CryptolExpr e
  deriving stock (Foldable, Functor, Traversable)

data SetupStep ty
  = SetupReturn (CrucibleSetupVal CryptolAST) -- ^ The return value
  | SetupFresh ServerName Text ty -- ^ Server name to save in, debug name, fresh variable type
  | SetupAlloc ServerName ty Bool (Maybe Int) -- ^ Server name to save in, type of allocation, mutability, alignment
  | SetupGhostPointsTo ServerName CryptolAST -- ^ Variable, term
  | SetupPointsTo (CrucibleSetupVal CryptolAST)
                  (CrucibleSetupVal CryptolAST)
                  (Maybe (CheckPointsToType ty))
                  (Maybe CryptolAST)
                  -- ^ The source, the target, the type to check the target,
                  --   and the condition that must hold in order for the source to point to the target
  | SetupExecuteFunction [CrucibleSetupVal CryptolAST] -- ^ Function's arguments
  | SetupPrecond CryptolAST -- ^ Function's precondition
  | SetupPostcond CryptolAST -- ^ Function's postcondition
  deriving stock (Foldable, Functor, Traversable)

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
     CryptolSAW.scLoadPreludeModule sc
     CryptolSAW.scLoadCryptolModule sc
     let mn = mkModuleName ["SAWScript"]
     scLoadModule sc (emptyModule mn)
     ss <- basic_ss sc
     let jarFiles = []
         classPaths = []
         javaBinDirs = []
     jcb <- JSS.loadCodebase jarFiles classPaths javaBinDirs
     let bic = BuiltinContext { biSharedContext = sc
                              , biBasicSS = ss
                              }
     cenv <- initCryptolEnv sc
     halloc <- Crucible.newHandleAllocator
     jvmTrans <- CJ.mkInitialJVMContext halloc
     cwd <- getCurrentDirectory
     let ro = TopLevelRO
                { roSharedContext = sc
                , roJavaCodebase = jcb
                , roOptions = defaultOptions
                , roHandleAlloc = halloc
                , roPosition = PosInternal "SAWServer"
#if USE_BUILTIN_ABC
                , roProxy = AIGProxy GIA.proxy
#else
                , roProxy = AIGProxy AIG.basicProxy
#endif
                , roInitWorkDir = cwd
                , roBasicSS = ss
                }
         rw = TopLevelRW
                { rwValues = mempty
                , rwTypes = mempty
                , rwTypedef = mempty
                , rwDocs = mempty
                , rwCryptol = cenv
                , rwPPOpts = defaultPPOpts
                , rwJVMTrans = jvmTrans
                , rwPrimsAvail = mempty
                , rwSMTArrayMemoryModel = False
                , rwProfilingFile = Nothing
                , rwCrucibleAssertThenAssume = False
                , rwLaxArith = False
                , rwWhat4HashConsing = False
                , rwWhat4HashConsingX86 = False
                , rwStackBaseAlign = defaultStackBaseAlign
                , rwProofs = []
                , rwPreservedRegs = []
                }
     return (SAWState emptyEnv bic [] ro rw M.empty)

-- NOTE: KWF: 2020-04-22: This function could introduce a race condition: if a
-- file changes on disk after its hash is computed by validateSAWState, but
-- before the function returns and its result is used to inform whether to
-- recompute a cached result, the cached result may be used even if it is
-- associated with stale filesystem state. See the discussion of this issue at:
-- https://github.com/GaloisInc/argo/pull/70#discussion_r412462908
validateSAWState :: SAWState -> IO Bool
validateSAWState sawState =
  checkAll
    [ CryptolServer.validateServerState cryptolState
    , checkAll $ map (uncurry checkHash) (M.assocs (view trackedFiles sawState))
    ]
  where
    checkAll [] = pure True
    checkAll (c : cs) =
      do result <- c
         if result
           then checkAll cs
           else pure False

    checkHash path hash =
      do currentHash <- Hash.hashFile path
         pure (currentHash == hash)

    cryptolState =
      CryptolServer.ServerState Nothing
        (CryptolEnv.eModuleEnv . rwCryptol . view sawTopLevelRW $ sawState)


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
  | VSimpset Simpset
  | VType Cryptol.Schema
  | VCryptolModule CryptolModule -- from SAW, includes Term mappings
  | VJVMClass JSS.Class
  | VJVMCrucibleSetup (Pair CrucibleSetupTypeRepr JVMSetupM)
  | VLLVMCrucibleSetup (Pair CrucibleSetupTypeRepr LLVMCrucibleSetupM)
  | VLLVMModule (Some CMS.LLVMModule)
  | VJVMMethodSpecIR (CMS.CrucibleMethodSpecIR CJ.JVM)
  | VLLVMMethodSpecIR (CMS.SomeLLVM CMS.CrucibleMethodSpecIR)
  | VGhostVar CMS.GhostGlobal

instance Show ServerVal where
  show (VTerm t) = "(VTerm " ++ show t ++ ")"
  show (VSimpset ss) = "(VSimpset " ++ show ss ++ ")"
  show (VType t) = "(VType " ++ show t ++ ")"
  show (VCryptolModule _) = "VCryptolModule"
  show (VJVMClass _) = "VJVMClass"
  show (VJVMCrucibleSetup _) = "VJVMCrucibleSetup"
  show (VLLVMCrucibleSetup _) = "VLLVMCrucibleSetup"
  show (VLLVMModule (Some _)) = "VLLVMModule"
  show (VLLVMMethodSpecIR _) = "VLLVMMethodSpecIR"
  show (VJVMMethodSpecIR _) = "VJVMMethodSpecIR"
  show (VGhostVar x) = "(VGhostVar " ++ show x ++ ")"

class IsServerVal a where
  toServerVal :: a -> ServerVal

instance IsServerVal TypedTerm where
  toServerVal = VTerm

instance IsServerVal Simpset where
  toServerVal = VSimpset

instance IsServerVal Cryptol.Schema where
  toServerVal = VType

instance IsServerVal CryptolModule where
  toServerVal = VCryptolModule

instance IsServerVal (CMS.CrucibleMethodSpecIR CJ.JVM) where
  toServerVal = VJVMMethodSpecIR

instance IsServerVal (CMS.SomeLLVM CMS.CrucibleMethodSpecIR) where
  toServerVal = VLLVMMethodSpecIR

instance IsServerVal JSS.Class where
  toServerVal = VJVMClass

instance IsServerVal CMS.GhostGlobal where
  toServerVal = VGhostVar

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
  do SAWEnv serverEnv <- view sawEnv <$> Argo.getState
     st <- Argo.getState @SAWState
     Argo.debugLog $ "Looking up " <> T.pack (show n) <> " in " <> T.pack (show st)
     case M.lookup n serverEnv of
       Nothing -> Argo.raise (serverValNotFound n)
       Just val -> return val

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

getJVMMethodSpecIR :: ServerName -> Argo.Command SAWState (CMS.CrucibleMethodSpecIR CJ.JVM)
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

getLLVMSetup :: ServerName -> Argo.Command SAWState (Pair CrucibleSetupTypeRepr LLVMCrucibleSetupM)
getLLVMSetup n =
  do v <- getServerVal n
     case v of
       VLLVMCrucibleSetup setup -> return setup
       _other -> Argo.raise (notAnLLVMSetup n)

getLLVMMethodSpecIR :: ServerName -> Argo.Command SAWState (CMS.SomeLLVM CMS.CrucibleMethodSpecIR)
getLLVMMethodSpecIR n =
  do v <- getServerVal n
     case v of
       VLLVMMethodSpecIR ir -> return ir
       _other -> Argo.raise (notAnLLVMMethodSpecIR n)

getSimpset :: ServerName -> Argo.Command SAWState Simpset
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
