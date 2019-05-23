{- |
Module      : SAWScript.Value
Description : Value datatype for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}

module SAWScript.Value where

import Data.Semigroup ((<>))
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif
import Control.Monad.ST
import Control.Monad.Fail (MonadFail)
import qualified Control.Exception as X
import qualified System.IO.Error as IOError
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT(..), ask, asks, local)
import Control.Monad.State (StateT(..), get, gets, put)
import Control.Monad.Trans.Class (lift)
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Set ( Set )
import qualified Text.LLVM    as L
import qualified Text.LLVM.PP as L
import qualified Text.PrettyPrint.HughesPJ as PP
import qualified Text.PrettyPrint.ANSI.Leijen as PPL
import Data.Parameterized.Some
import Data.Typeable

import qualified Data.AIG as AIG

import qualified SAWScript.AST as SS
import qualified SAWScript.Utils as SS
import qualified SAWScript.JavaMethodSpecIR as JIR
import qualified SAWScript.CrucibleLLVM as Crucible
import qualified SAWScript.CrucibleMethodSpecIR as CIR
import qualified SAWScript.JVM.CrucibleMethodSpecIR as JCIR
import qualified Verifier.Java.Codebase as JSS
import qualified Text.LLVM.AST as LLVM (Type)
import qualified Text.LLVM.PP as LLVM (ppType)
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.JavaPretty (prettyClass)
import SAWScript.Options (Options(printOutFn),printOutLn,Verbosity)
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.SAWCorePrimitives( concretePrimitives )

import Verifier.SAW.CryptolEnv as CEnv
import Verifier.SAW.FiniteValue (FirstOrderValue, ppFirstOrderValue)
import Verifier.SAW.Rewriter (Simpset, lhsRewriteRule, rhsRewriteRule, listRules)
import Verifier.SAW.SharedTerm hiding (PPOpts(..), defaultPPOpts,
                                       ppTerm, scPrettyTerm)
import qualified Verifier.SAW.SharedTerm as SAWCorePP (PPOpts(..), defaultPPOpts,
                                                       ppTerm, scPrettyTerm)
import Verifier.SAW.TypedTerm

import qualified Verifier.SAW.Simulator.Concrete as Concrete
import qualified Cryptol.Eval as C
import qualified Cryptol.Eval.Value as C
import Verifier.SAW.Cryptol (exportValueWithSchema)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema)
import qualified Cryptol.Utils.Logger as C (quietLogger)
import Cryptol.Utils.PP (pretty)

import qualified Lang.Crucible.CFG.Core as Crucible (AnyCFG)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.LLVM.MemModel as Crucible (HasPtrWidth)

import           Lang.Crucible.JVM (JVM)
import qualified Lang.Crucible.JVM as CJ

-- Values ----------------------------------------------------------------------

data Value
  = VBool Bool
  | VString String
  | VInteger Integer
  | VArray [Value]
  | VTuple [Value]
  | VRecord (Map SS.Name Value)
  | VLambda (Value -> TopLevel Value)
  | VTerm TypedTerm
  | VType Cryptol.Schema
  | VReturn Value -- Returned value in unspecified monad
  | VBind Value Value -- Monadic bind in unspecified monad
  | VTopLevel (TopLevel Value)
  | VProofScript (ProofScript Value)
  | VSimpset Simpset
  | VTheorem Theorem
  | VJavaSetup (JavaSetup Value)
  | VJavaMethodSpec JIR.JavaMethodSpecIR
  -----
  | VCrucibleSetup !(CrucibleSetupM Value)
  | VCrucibleMethodSpec CIR.CrucibleMethodSpecIR
  | VCrucibleSetupValue CIR.SetupValue
  -----
  | VJVMSetup !(JVMSetupM Value)
  | VJVMMethodSpec JCIR.CrucibleMethodSpecIR
  | VJVMSetupValue JCIR.SetupValue
  -----
  | VJavaType JavaType
  | VLLVMType LLVM.Type
  | VCryptolModule CryptolModule
  | VJavaClass JSS.Class
  | VLLVMModule LLVMModule
  | VSatResult SatResult
  | VProofResult ProofResult
  | VUninterp Uninterp
  | VAIG AIGNetwork
  | VCFG SAW_CFG
  | VGhostVar CIR.GhostGlobal

data AIGNetwork where
  AIGNetwork :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Network l g -> AIGNetwork

data AIGProxy where
  AIGProxy :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Proxy l g -> AIGProxy

data SAW_CFG where
  LLVM_CFG :: Crucible.AnyCFG (Crucible.LLVM arch) -> SAW_CFG
  JVM_CFG :: Crucible.AnyCFG JVM -> SAW_CFG

data LLVMModule =
  LLVMModule
  { modName :: String
  , modMod :: L.Module
  , modTrans :: Some Crucible.ModuleTranslation
  }

showLLVMModule :: LLVMModule -> String
showLLVMModule (LLVMModule name m _) =
  unlines [ "Module: " ++ name
          , "Types:"
          , showParts L.ppTypeDecl (L.modTypes m)
          , "Globals:"
          , showParts ppGlobal' (L.modGlobals m)
          , "External references:"
          , showParts L.ppDeclare (L.modDeclares m)
          , "Definitions:"
          , showParts ppDefine' (L.modDefines m)
          ]
  where
    showParts pp xs = unlines $ map (show . PP.nest 2 . pp) xs
    ppGlobal' g =
      L.ppSymbol (L.globalSym g) PP.<+> PP.char '=' PP.<+>
      L.ppGlobalAttrs (L.globalAttrs g) PP.<+>
      L.ppType (L.globalType g)
    ppDefine' d =
      L.ppMaybe L.ppLinkage (L.defLinkage d) PP.<+>
      L.ppType (L.defRetType d) PP.<+>
      L.ppSymbol (L.defName d) PP.<>
      L.ppArgList (L.defVarArgs d) (map (L.ppTyped L.ppIdent) (L.defArgs d)) PP.<+>
      L.ppMaybe (\gc -> PP.text "gc" PP.<+> L.ppGC gc) (L.defGC d)

data ProofResult
  = Valid SolverStats
  | InvalidMulti SolverStats [(String, FirstOrderValue)]
    deriving (Show)

data SatResult
  = Unsat SolverStats
  | SatMulti SolverStats [(String, FirstOrderValue)]
    deriving (Show)

flipSatResult :: SatResult -> ProofResult
flipSatResult (Unsat stats) = Valid stats
flipSatResult (SatMulti stats t) = InvalidMulti stats t

isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

data PPOpts = PPOpts
  { ppOptsAnnotate :: Bool
  , ppOptsAscii :: Bool
  , ppOptsBase :: Int
  , ppOptsColor :: Bool
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts False False 10 False

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
    Valid _ -> showString "Valid"
    InvalidMulti _ ts -> showString "Invalid: [" . showMulti "" ts
  where
    opts' = sawPPOpts opts
    showVal t = shows (ppFirstOrderValue opts' t)
    showEqn (x, t) = showString x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showsSatResult :: PPOpts -> SatResult -> ShowS
showsSatResult opts r =
  case r of
    Unsat _ -> showString "Unsat"
    SatMulti _ ts -> showString "Sat: [" . showMulti "" ts
  where
    opts' = sawPPOpts opts
    showVal t = shows (ppFirstOrderValue opts' t)
    showEqn (x, t) = showString x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showSimpset :: PPOpts -> Simpset -> String
showSimpset opts ss =
  unlines ("Rewrite Rules" : "=============" : map (show . ppRule) (listRules ss))
  where
    ppRule r =
      PPL.char '*' PPL.<+>
      (PPL.nest 2 $
       SAWCorePP.ppTerm opts' (lhsRewriteRule r)
       PPL.</> PPL.char '=' PPL.<+>
       ppTerm (rhsRewriteRule r))
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
    VTheorem (Theorem t) ->
      showString "Theorem " .
      showParen True (showString (SAWCorePP.scPrettyTerm opts' t))
    VJavaSetup {} -> showString "<<Java Setup>>"
    VCrucibleSetup{} -> showString "<<Crucible Setup>>"
    VCrucibleSetupValue x -> shows x
    VJavaMethodSpec ms -> shows (JIR.ppMethodSpec ms)
    VCrucibleMethodSpec{} -> showString "<<Crucible MethodSpec>>"
    VJavaType {} -> showString "<<Java type>>"
    VLLVMType t -> showString (show (LLVM.ppType t))
    VCryptolModule m -> showString (showCryptolModule m)
    VLLVMModule m -> showString (showLLVMModule m)
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
  (\modmap -> Concrete.evalSharedTerm modmap concretePrimitives t) <$>
  scGetModuleMap sc

evaluateTypedTerm :: SharedContext -> TypedTerm -> IO C.Value
evaluateTypedTerm sc (TypedTerm schema trm) =
  exportValueWithSchema schema <$> evaluate sc trm

applyValue :: Value -> Value -> TopLevel Value
applyValue (VLambda f) x = f x
applyValue _ _ = fail "applyValue"

thenValue :: Value -> Value -> Value
thenValue v1 v2 = VBind v1 (VLambda (const (return v2)))

bindValue :: Value -> Value -> TopLevel Value
bindValue v1 v2 = return (VBind v1 v2)

forValue :: [Value] -> Value -> TopLevel Value
forValue [] _ = return $ VReturn (VArray [])
forValue (x : xs) f =
  do m1 <- applyValue f x
     m2 <- forValue xs f
     bindValue m1 (VLambda $ \v1 ->
       bindValue m2 (VLambda $ \v2 ->
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
  , roHandleAlloc   :: Crucible.HandleAllocator RealWorld
  , roPosition      :: SS.Pos
  , roProxy         :: AIGProxy
  }

data TopLevelRW =
  TopLevelRW
  { rwValues  :: Map SS.LName Value
  , rwTypes   :: Map SS.LName SS.Schema
  , rwTypedef :: Map SS.Name SS.Type
  , rwDocs    :: Map SS.Name String
  , rwCryptol :: CEnv.CryptolEnv
  , rwPPOpts  :: PPOpts
  -- , rwCrucibleLLVMCtx :: Crucible.LLVMContext
  , rwJVMTrans :: CJ.JVMContext
  -- ^ crucible-jvm: Handles and info for classes that have already been translated
  , rwPrimsAvail :: Set PrimitiveLifecycle
  }

newtype TopLevel a = TopLevel (ReaderT TopLevelRO (StateT TopLevelRW IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runTopLevel :: TopLevel a -> TopLevelRO -> TopLevelRW -> IO (a, TopLevelRW)
runTopLevel (TopLevel m) = runStateT . runReaderT m

io :: IO a -> TopLevel a
io = liftIO

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

getHandleAlloc :: TopLevel (Crucible.HandleAllocator RealWorld)
getHandleAlloc = TopLevel (asks roHandleAlloc)

getTopLevelRO :: TopLevel TopLevelRO
getTopLevelRO = TopLevel ask

getTopLevelRW :: TopLevel TopLevelRW
getTopLevelRW = TopLevel get

putTopLevelRW :: TopLevelRW -> TopLevel ()
putTopLevelRW rw = TopLevel (put rw)

-- | Access the current state of Java Class translation
getJVMTrans :: TopLevel  CJ.JVMContext
getJVMTrans = TopLevel (gets rwJVMTrans)

-- | Add a newly translated class to the translation
addJVMTrans :: CJ.JVMContext -> TopLevel ()
addJVMTrans trans = do
  rw <- getTopLevelRW
  let jvmt = rwJVMTrans rw
  putTopLevelRW ( rw { rwJVMTrans = trans <> jvmt })


-- Other SAWScript Monads ------------------------------------------------------

-- The ProofScript in RunVerify is in the SAWScript context, and
-- should stay there.
data ValidationPlan
  = Skip
  | RunVerify (ProofScript SatResult)

data JavaSetupState
  = JavaSetupState {
      jsSpec :: JIR.JavaMethodSpecIR
    , jsContext :: SharedContext
    , jsTactic :: ValidationPlan
    , jsSimulate :: Bool
    , jsSatBranches :: Bool
    }

type JavaSetup a = StateT JavaSetupState TopLevel a

type CrucibleSetup arch a =
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) => StateT (CIR.CrucibleSetupState arch) TopLevel a

data CrucibleSetupM a =
  CrucibleSetupM { runCrucibleSetupM :: forall arch. CrucibleSetup arch a }

instance Functor CrucibleSetupM where
  fmap f (CrucibleSetupM m) = CrucibleSetupM (fmap f m)

instance Applicative CrucibleSetupM where
  pure x = CrucibleSetupM (pure x)
  CrucibleSetupM f <*> CrucibleSetupM m = CrucibleSetupM (f <*> m)

instance Monad CrucibleSetupM where
  return = pure
  CrucibleSetupM m >>= f = CrucibleSetupM (m >>= runCrucibleSetupM . f)

--
type JVMSetup a =
  StateT JCIR.CrucibleSetupState TopLevel a

data JVMSetupM a =
  JVMSetupM { runJVMSetupM :: JVMSetup a }

instance Functor JVMSetupM where
  fmap f (JVMSetupM m) = JVMSetupM (fmap f m)

instance Applicative JVMSetupM where
  pure x = JVMSetupM (pure x)
  JVMSetupM f <*> JVMSetupM m = JVMSetupM (f <*> m)

instance Monad JVMSetupM where
  return = pure
  JVMSetupM m >>= f = JVMSetupM (m >>= runJVMSetupM . f)
--
type ProofScript a = StateT ProofState TopLevel a

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

instance IsValue a => IsValue (TopLevel a) where
    toValue action = VTopLevel (fmap toValue action)

instance FromValue a => FromValue (TopLevel a) where
    fromValue (VTopLevel action) = fmap fromValue action
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue TopLevel"

instance IsValue a => IsValue (StateT ProofState TopLevel a) where
    toValue m = VProofScript (fmap toValue m)

instance FromValue a => FromValue (StateT ProofState TopLevel a) where
    fromValue (VProofScript m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- lift $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue ProofScript"

instance IsValue a => IsValue (StateT JavaSetupState TopLevel a) where
    toValue m = VJavaSetup (fmap toValue m)

instance FromValue a => FromValue (StateT JavaSetupState TopLevel a) where
    fromValue (VJavaSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- lift $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue JavaSetup"

---------------------------------------------------------------------------------
instance IsValue a => IsValue (CrucibleSetupM a) where
    toValue m = VCrucibleSetup (fmap toValue m)

instance FromValue a => FromValue (CrucibleSetupM a) where
    fromValue (VCrucibleSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = CrucibleSetupM $ do
      v1 <- runCrucibleSetupM (fromValue m1)
      m2 <- lift $ applyValue v2 v1
      runCrucibleSetupM (fromValue m2)
    fromValue _ = error "fromValue CrucibleSetup"

instance IsValue a => IsValue (JVMSetupM a) where
    toValue m = VJVMSetup (fmap toValue m)

instance FromValue a => FromValue (JVMSetupM a) where
    fromValue (VJVMSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = JVMSetupM $ do
      v1 <- runJVMSetupM (fromValue m1)
      m2 <- lift $ applyValue v2 v1
      runJVMSetupM (fromValue m2)
    fromValue _ = error "fromValue JVMSetup"

instance IsValue CIR.SetupValue where
  toValue v = VCrucibleSetupValue v

instance FromValue CIR.SetupValue where
  fromValue (VCrucibleSetupValue v) = v
  fromValue _ = error "fromValue Crucible.SetupValue"

instance IsValue JCIR.SetupValue where
  toValue v = VJVMSetupValue v

instance FromValue JCIR.SetupValue where
  fromValue (VJVMSetupValue v) = v
  fromValue _ = error "fromValue Crucible.SetupValue"

instance IsValue SAW_CFG where
    toValue t = VCFG t

instance FromValue SAW_CFG where
    fromValue (VCFG t) = t
    fromValue _ = error "fromValue CFG"

instance IsValue CIR.CrucibleMethodSpecIR where
    toValue t = VCrucibleMethodSpec t

instance FromValue CIR.CrucibleMethodSpecIR where
    fromValue (VCrucibleMethodSpec t) = t
    fromValue _ = error "fromValue CrucibleMethodSpecIR"

instance IsValue JCIR.CrucibleMethodSpecIR where
    toValue t = VJVMMethodSpec t

instance FromValue JCIR.CrucibleMethodSpecIR where
    fromValue (VJVMMethodSpec t) = t
    fromValue _ = error "fromValue CrucibleMethodSpecIR"

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
    toValue n = VString n

instance FromValue String where
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

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

instance IsValue Simpset where
    toValue ss = VSimpset ss

instance FromValue Simpset where
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue Theorem where
    toValue t = VTheorem t

instance FromValue Theorem where
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

instance IsValue JIR.JavaMethodSpecIR where
    toValue ms = VJavaMethodSpec ms

instance FromValue JIR.JavaMethodSpecIR where
    fromValue (VJavaMethodSpec ms) = ms
    fromValue _ = error "fromValue JavaMethodSpec"

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

instance IsValue LLVMModule where
    toValue m = VLLVMModule m

instance FromValue LLVMModule where
    fromValue (VLLVMModule m) = m
    fromValue _ = error "fromValue LLVMModule"

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

instance IsValue CIR.GhostGlobal where
  toValue = VGhostVar

instance FromValue CIR.GhostGlobal where
  fromValue (VGhostVar r) = r
  fromValue v = error ("fromValue GlobalVar: " ++ show v)

-- Error handling --------------------------------------------------------------

-- | Implement stack tracing by adding error handlers that rethrow
-- user errors, prepended with the given string.
addTrace :: String -> Value -> Value
addTrace str val =
  case val of
    VLambda        f -> VLambda        (\x -> addTrace str `fmap` addTraceTopLevel str (f x))
    VTopLevel      m -> VTopLevel      (addTrace str `fmap` addTraceTopLevel str m)
    VProofScript   m -> VProofScript   (addTrace str `fmap` addTraceStateT str m)
    VJavaSetup     m -> VJavaSetup     (addTrace str `fmap` addTraceStateT str m)
    VCrucibleSetup (CrucibleSetupM m) -> VCrucibleSetup (CrucibleSetupM (addTrace str `fmap` addTraceStateT str m))
    VBind v1 v2      -> VBind          (addTrace str v1) (addTrace str v2)
    _                -> val

-- | Wrap an action with a handler that catches and rethrows user
-- errors with an extended message.
addTraceIO :: String -> IO a -> IO a
addTraceIO str action = X.catchJust p action h
  where
    -- TODO: Use a custom exception type instead of fail/userError
    -- init/drop 12 is a hack to remove "user error (" and ")"
    p e = if IOError.isUserError e then Just (init (drop 12 (show e))) else Nothing
    h msg = X.throwIO (IOError.userError (str ++ ":\n" ++ msg))

-- | Similar to addTraceIO, but for the TopLevel monad.
addTraceTopLevel :: String -> TopLevel a -> TopLevel a
addTraceTopLevel str action =
  TopLevel $ ReaderT $ \ro -> StateT $ \rw ->
    addTraceIO str (runTopLevel action ro rw)

-- | Similar to addTraceIO, but for state monads built from TopLevel.
addTraceStateT :: String -> StateT s TopLevel a -> StateT s TopLevel a
addTraceStateT str action =
  StateT $ \s -> addTraceTopLevel str (runStateT action s)

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext
                                     , biJavaCodebase  :: JSS.Codebase
                                     , biBasicSS       :: Simpset
                                     }
