{- |
Module      : SAWScript.Crucible.Common.MethodSpec
Description : Language-neutral method specifications
License     : BSD3
Maintainer  : langston
Stability   : provisional

This module uses GADTs & type families to distinguish syntax-extension- (source
language-) specific code. This technique is described in the paper \"Trees That
Grow\", and is prevalent across the Crucible codebase.
-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.MethodSpec where

import           Data.Constraint (Constraint)
import           Data.List (isPrefixOf)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Void (Void)
import           Control.Monad.ST (RealWorld)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import           Data.Monoid ((<>))
import           Data.Type.Equality (TestEquality(..), (:~:)(..))
import           Data.Kind (Type)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- what4
import           What4.ProgramLoc (ProgramLoc)

import           Data.Parameterized.NatRepr (NatRepr(..))
import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible (SymGlobalState)
import qualified Lang.Crucible.Backend.SAWCore as Crucible
  (SAWCoreBackend, toSC, SAWCruciblePersonality)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible (SimContext)

import qualified Cryptol.Utils.PP as Cryptol

-- LLVM
import qualified SAWScript.Crucible.LLVM.CrucibleLLVM as CL
import qualified Text.LLVM.AST as L

-- JVM
import qualified Lang.Crucible.JVM as CJ
import qualified Language.JVM.Parser as J
import qualified Verifier.Java.Codebase as CB

-- Language extension tags
import           Lang.Crucible.LLVM.Extension (LLVM, X86)
import           Lang.Crucible.JVM.Types (JVM)

import           Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm as SAWVerifier

import           SAWScript.Options
import           SAWScript.Prover.SolverStats

import           SAWScript.Crucible.Common

--------------------------------------------------------------------------------
-- ** ExtRepr

-- | A singleton type representing a language extension
--
-- While Crucible supports extensibly adding and simulating new languages, we can
-- exhaustively enumerate all the languages SAW supports verifying.
data ExtRepr ext where
  ExtJVM :: ExtRepr JVM
  ExtLLVM :: NatRepr n -> ExtRepr (LLVM (X86 n))

instance TestEquality ExtRepr where
  testEquality (ExtLLVM n) (ExtLLVM m) =
    case testEquality n m of
      Just Refl -> Just Refl
      Nothing -> Nothing
  testEquality ExtJVM ExtJVM = Just Refl
  testEquality _ _ = Nothing

--------------------------------------------------------------------------------
-- ** SetupValue

 -- The following type families describe what SetupValues are legal for which
 -- languages.

type family HasSetupStruct ext where
  HasSetupStruct (LLVM arch) = ()
  HasSetupStruct JVM = Void

type family HasSetupArray ext where
  HasSetupArray (LLVM arch) = ()
  HasSetupArray JVM = Void

type family HasSetupElem ext where
  HasSetupElem (LLVM arch) = ()
  HasSetupElem JVM = Void

type family HasSetupField ext where
  HasSetupField (LLVM arch) = ()
  HasSetupField JVM = Void

type family HasSetupGlobalInitializer ext where
  HasSetupGlobalInitializer (LLVM arch) = ()
  HasSetupGlobalInitializer JVM = Void

-- | From the manual: \"The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both 'Term' values, pointers, and
-- composite types consisting of either of these (both structures and arrays).\"
data SetupValue ext where
  SetupVar    :: AllocIndex -> SetupValue ext
  SetupTerm   :: TypedTerm -> SetupValue ext
  SetupNull   :: SetupValue ext
  -- | If the 'Bool' is 'True', it's a (LLVM) packed struct
  SetupStruct :: HasSetupStruct ext -> Bool -> [SetupValue ext] -> SetupValue ext
  SetupArray  :: HasSetupArray ext -> [SetupValue ext] -> SetupValue ext
  SetupElem   :: HasSetupElem ext -> SetupValue ext -> Int -> SetupValue ext
  SetupField  :: HasSetupField ext -> SetupValue ext -> String -> SetupValue ext
  -- | A pointer to a global variable
  SetupGlobal :: String -> SetupValue ext
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer :: HasSetupGlobalInitializer ext -> String -> SetupValue ext

type SetupValueHas (c :: Type -> Constraint) ext =
  ( c (HasSetupStruct ext)
  , c (HasSetupArray ext)
  , c (HasSetupElem ext)
  , c (HasSetupField ext)
  , c (HasSetupGlobalInitializer ext)
  )

deriving instance (SetupValueHas Show ext) => Show (SetupValue ext)
-- TypedTerm is neither Data, Eq nor Ord
-- deriving instance ( SetupValueHas Data ext
--                   , SetupValueHas Typeable ext
--                   , Typeable ext
--                   ) => Data (SetupValue ext)
-- deriving instance (SetupValueHas Eq ext) => Eq (SetupValue ext)
-- deriving instance (SetupValueHas Ord ext) => Ord (SetupValue ext)

-- | Note that most 'SetupValue' concepts (like allocation indices)
--   are implementation details and won't be familiar to users.
--   Consider using 'resolveSetupValue' and printing an 'LLVMVal'
--   with @PP.pretty@ instead.
ppSetupValue :: SetupValue ext -> PP.Doc
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> PP.text ("@" ++ show i)
  SetupNull      -> PP.text "NULL"
  SetupStruct _ packed vs
    | packed     -> PP.angles (PP.braces (commaList (map ppSetupValue vs)))
    | otherwise  -> PP.braces (commaList (map ppSetupValue vs))
  SetupArray _ vs  -> PP.brackets (commaList (map ppSetupValue vs))
  SetupElem _ v i  -> PP.parens (ppSetupValue v) PP.<> PP.text ("." ++ show i)
  SetupField _ v f -> PP.parens (ppSetupValue v) PP.<> PP.text ("." ++ f)
  SetupGlobal nm -> PP.text ("global(" ++ nm ++ ")")
  SetupGlobalInitializer _ nm -> PP.text ("global_initializer(" ++ nm ++ ")")
  where
    commaList :: [PP.Doc] -> PP.Doc
    commaList []     = PP.empty
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

    ppTypedTerm :: TypedTerm -> PP.Doc
    ppTypedTerm (TypedTerm tp tm) =
      ppTerm defaultPPOpts tm
      PP.<+> PP.text ":" PP.<+>
      PP.text (show (Cryptol.ppPrec 0 tp))

setupToTypedTerm ::
  ExtRepr ext {-^ Which language/syntax extension are we using? -} ->
  Options {-^ Printing options -} ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO TypedTerm
setupToTypedTerm ext opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm ext opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm ::
  ExtRepr ext {-^ Which language/syntax extension are we using? -} ->
  Options ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO Term
setupToTerm ext opts sc sv =
  case (ext, sv) of
    (_, SetupTerm term) -> return (ttTerm term)

    -- LLVM-specific cases
    (ExtLLVM _ptrWidth, SetupStruct () _ fields) ->
      do ts <- mapM (setupToTerm ext opts sc) fields
         lift $ scTuple sc ts

    (ExtLLVM _ptrWidth, SetupArray () elems@(_:_)) ->
      do ts@(t:_) <- mapM (setupToTerm ext opts sc) elems
         typt <- lift $ scTypeOf sc t
         vec <- lift $ scVector sc typt ts
         typ <- lift $ scTypeOf sc vec
         lift $ printOutLn opts Info $ show vec
         lift $ printOutLn opts Info $ show typ
         return vec

    (ExtLLVM _ptrWidth, SetupElem () base ind) ->
      case base of
        SetupArray () elems@(e:_) ->
          do let intToNat = fromInteger . toInteger
             art <- setupToTerm ext opts sc base
             ixt <- lift $ scNat sc $ intToNat ind
             lent <- lift $ scNat sc $ intToNat $ length elems
             et <- setupToTerm ext opts sc e
             typ <- lift $ scTypeOf sc et
             lift $ scAt sc lent typ art ixt

        SetupStruct () _ fs ->
          do st <- setupToTerm ext opts sc base
             lift $ scTupleSelector sc st ind (length fs)

        _ -> MaybeT $ return Nothing

    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

--------------------------------------------------------------------------------
-- ** Ghost state

-- TODO: These are really language-independent, and should be made so!
-- TODO: documentation

type family HasGhostState ext where
  HasGhostState (LLVM arch) = ()
  HasGhostState JVM = Void

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

--------------------------------------------------------------------------------
-- ** Pre- and post-conditions

--------------------------------------------------------------------------------
-- *** ResolvedState

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
data ResolvedState =
  ResolvedState
  { _rsAllocs :: Map AllocIndex [[Int]]
  , _rsGlobals :: Map String [[Int]]
  }

-- | A datatype to keep track of which parts of the simulator state
-- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
-- data ResolvedState =
--   ResolvedState
--   { _rsAllocs :: Map AllocIndex [Either String Int]
--   , _rsGlobals :: Map String [Either String Int]
--   }

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ext ->
  ResolvedState ->
  ResolvedState
markResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n      -> rs {_rsAllocs = Map.alter (ins path) n (_rsAllocs rs) }
        SetupGlobal c   -> rs {_rsGlobals = Map.alter (ins path) c (_rsGlobals rs)}
        SetupElem _ v i -> go (i : path) v
        _               -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ext ->
  ResolvedState ->
  Bool
testResolved val0 rs = go [] val0
  where
    go path val =
      case val of
        SetupVar n      -> test path (Map.lookup n (_rsAllocs rs))
        SetupGlobal c   -> test path (Map.lookup c (_rsGlobals rs))
        SetupElem _ v i -> go (i : path) v
        _               -> False

    test _ Nothing = False
    test path (Just paths) = any (`isPrefixOf` path) paths


-- intrinsics :: MapF.MapF Crucible.SymbolRepr (Crucible.IntrinsicMuxFn Sym)
-- intrinsics =
--   MapF.insert
--     (Crucible.knownSymbol :: Crucible.SymbolRepr GhostValue)
--     Crucible.IntrinsicMuxFn
--     CL.llvmIntrinsicTypes

--------------------------------------------------------------------------------
-- *** CrucibleContext

-- | TODO: What do we say this is??
type family CrucibleContext ext a where
  CrucibleContext (LLVM arch) wptr = LLVMCrucibleContext wptr
  CrucibleContext JVM _ = JVMCrucibleContext

data JVMCrucibleContext =
  JVMCrucibleContext
  { _jccJVMClass       :: J.Class
  , _jccCodebase       :: CB.Codebase
  , _jccJVMContext     :: CJ.JVMContext
  , _jccBackend        :: Sym -- This is stored inside field _ctxSymInterface of Crucible.SimContext; why do we need another one?
  , _jccHandleAllocator :: Crucible.HandleAllocator RealWorld
  }

data LLVMCrucibleContext wptr =
  LLVMCrucibleContext
  { _llccLLVMModule      :: L.Module
  , _llccLLVMModuleTrans :: CL.ModuleTranslation wptr
  , _llccBackend         :: Sym
  , _llccLLVMEmptyMem    :: CL.MemImpl Sym -- ^ A heap where LLVM globals are allocated, but not initialized.
  , _llccLLVMSimContext  :: Crucible.SimContext (Crucible.SAWCruciblePersonality Sym) Sym (CL.LLVM wptr)
  , _llccLLVMGlobals     :: Crucible.SymGlobalState Sym
  }

makeLenses ''JVMCrucibleContext
makeLenses ''LLVMCrucibleContext

--------------------------------------------------------------------------------
-- *** Extension-specific information

data AllocSpecLLVM =
  AllocSpecLLVM
    { allocSpecMut   :: CL.Mutability
    , allocSpecType  :: CL.MemType
    , allocSpecBytes :: CL.Bytes
    } -- TODO: deriving

type JIdent = String -- FIXME(huffman): what to put here?

-- | How to specify allocations in this syntax extension
type family AllocSpec ext where
  AllocSpec (LLVM arch) = AllocSpecLLVM
  AllocSpec JVM = ()

-- | The type of identifiers for types in this syntax extension
type family TypeName ext where
  TypeName (LLVM arch) = CL.Ident
  TypeName JVM = JIdent

-- | The type of types of the syntax extension we're dealing with
type family ExtType ext where
  ExtType (LLVM arch) = CL.MemType
  ExtType JVM = J.Type

--------------------------------------------------------------------------------
-- *** StateSpec

data SetupCondition ext where
  SetupCond_Equal    :: ProgramLoc -> SetupValue ext -> SetupValue ext -> SetupCondition ext
  SetupCond_Pred     :: ProgramLoc -> TypedTerm -> SetupCondition ext
  SetupCond_Ghost    :: HasGhostState ext ->
                        ProgramLoc ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition ext

deriving instance ( SetupValueHas Show ext
                  , Show (HasGhostState ext)
                  ) => Show (SetupCondition ext)

-- | TODO: documentation
data PointsTo ext
  = PointsToField ProgramLoc (SetupValue ext) String (SetupValue ext)
  | PointsToElem ProgramLoc (SetupValue ext) Int (SetupValue ext)

deriving instance (SetupValueHas Show ext) => Show (PointsTo ext)

-- | Verification state (either pre- or post-) specification
data StateSpec ext = StateSpec
  { _csAllocs        :: Map AllocIndex (AllocSpec ext)
    -- ^ allocated pointers
  , _csFreshPointers :: Map AllocIndex (AllocSpec ext)
    -- ^ symbolic pointers
  , _csPointsTos     :: [PointsTo ext]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition ext]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedTerm]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: Map AllocIndex (TypeName ext)
    -- ^ names for types of variables, for diagnostics
  }

makeLenses ''StateSpec

initialStateSpec :: StateSpec ext
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csFreshPointers = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  , _csVarTypeNames  = Map.empty
  }

--------------------------------------------------------------------------------
-- *** Method specs

data LLVMMethod =
  LLVMMethod
    { llvmMethodName   :: String
    , llvmMethodParent :: Maybe String -- ^ Something to do with breakpoints...
    } deriving (Eq, Ord, Show) -- TODO: deriving

data JVMMethod =
  JVMMethod
    { jvmMethodName  :: String
    , jvmMethodClass :: J.ClassName
    } deriving (Eq, Ord, Show) -- TODO: deriving

-- | The type of types of the syntax extension we're dealing with
type family Method ext where
  Method (LLVM arch) = LLVMMethod
  Method JVM = J.ClassName

data CrucibleMethodSpecIR ext =
  CrucibleMethodSpec
  { _csMethod          :: Method ext
  , _csArgs            :: [ExtType ext]
  , _csRet             :: Maybe (ExtType ext)
  , _csPreState        :: StateSpec ext -- ^ state before the function runs
  , _csPostState       :: StateSpec ext -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (ExtType ext, SetupValue ext) -- ^ function arguments
  , _csRetValue        :: Maybe (SetupValue ext)            -- ^ function return value
  , _csSolverStats     :: SolverStats                 -- ^ statistics about the proof that produced this
  , _csLoc             :: ProgramLoc
  }

makeLenses ''CrucibleMethodSpecIR

csAllocations :: CrucibleMethodSpecIR ext -> Map AllocIndex (AllocSpec ext)
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csAllocs)

csTypeNames :: CrucibleMethodSpecIR ext -> Map AllocIndex (TypeName ext)
csTypeNames
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csVarTypeNames)

--------------------------------------------------------------------------------
-- *** CrucibleSetupState

-- | The type of state kept in the 'CrucibleSetup' monad
data CrucibleSetupState ext a =
  CrucibleSetupState
  { _csVarCounter      :: !AllocIndex
  , _csPrePost         :: PrePost
  , _csResolvedState   :: ResolvedState
  , _csMethodSpec      :: CrucibleMethodSpecIR ext
  , _csCrucibleContext :: CrucibleContext ext a
  }

makeLenses ''CrucibleSetupState
