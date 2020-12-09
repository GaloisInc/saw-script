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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module SAWScript.Crucible.Common.MethodSpec where

import           Data.Constraint (Constraint)
import           Data.List (isPrefixOf)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Void (Void)
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans (lift)
import           Control.Lens
import           Data.Kind (Type)
import qualified Prettyprinter as PP

-- what4
import           What4.ProgramLoc (ProgramLoc(plSourceLoc), Position)

import qualified Lang.Crucible.Types as Crucible
  (IntrinsicType, EmptyCtx)
import qualified Lang.Crucible.CFG.Common as Crucible (GlobalVar)

import qualified Cryptol.Utils.PP as Cryptol

import           Verifier.SAW.TypedTerm as SAWVerifier
import           Verifier.SAW.SharedTerm as SAWVerifier

import           SAWScript.Options
import           SAWScript.Prover.SolverStats
import           SAWScript.Utils (bullets)

-- | How many allocations have we made in this method spec?
newtype AllocIndex = AllocIndex Int
  deriving (Eq, Ord, Show)

nextAllocIndex :: AllocIndex -> AllocIndex
nextAllocIndex (AllocIndex n) = AllocIndex (n + 1)

-- | Are we writing preconditions or postconditions?
data PrePost
  = PreState | PostState
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- ** SetupValue

-- | An injective type family mapping type-level booleans to types
type family BoolToType (b :: Bool) = (t :: Type) | t -> b where
  BoolToType 'True  = ()
  BoolToType 'False = Void

type B b = BoolToType b

 -- The following type families describe what SetupValues are legal for which
 -- languages.
type family HasSetupNull ext :: Bool
type family HasSetupStruct ext :: Bool
type family HasSetupArray ext :: Bool
type family HasSetupElem ext :: Bool
type family HasSetupField ext :: Bool
type family HasSetupGlobal ext :: Bool
type family HasSetupGlobalInitializer ext :: Bool

-- | From the manual: \"The SetupValue type corresponds to values that can occur
-- during symbolic execution, which includes both 'Term' values, pointers, and
-- composite types consisting of either of these (both structures and arrays).\"
data SetupValue ext where
  SetupVar    :: AllocIndex -> SetupValue ext
  SetupTerm   :: TypedTerm -> SetupValue ext
  SetupNull   :: B (HasSetupNull ext) -> SetupValue ext
  -- | If the 'Bool' is 'True', it's a (LLVM) packed struct
  SetupStruct :: B (HasSetupStruct ext) -> Bool -> [SetupValue ext] -> SetupValue ext
  SetupArray  :: B (HasSetupArray ext) -> [SetupValue ext] -> SetupValue ext
  SetupElem   :: B (HasSetupElem ext) -> SetupValue ext -> Int -> SetupValue ext
  SetupField  :: B (HasSetupField ext) -> SetupValue ext -> String -> SetupValue ext
  -- | A pointer to a global variable
  SetupGlobal :: B (HasSetupGlobal ext) -> String -> SetupValue ext
  -- | This represents the value of a global's initializer.
  SetupGlobalInitializer ::
    B (HasSetupGlobalInitializer ext) -> String -> SetupValue ext

-- | This constraint can be solved for any ext so long as '()' and 'Void' have
--   the constraint. Unfortunately, GHC can't (yet?) reason over the equations
--   in our closed type family, and realize that
type SetupValueHas (c :: Type -> Constraint) ext =
  ( c (B (HasSetupNull ext))
  , c (B (HasSetupStruct ext))
  , c (B (HasSetupArray ext))
  , c (B (HasSetupElem ext))
  , c (B (HasSetupField ext))
  , c (B (HasSetupGlobal ext))
  , c (B (HasSetupGlobalInitializer ext))
  )

deriving instance (SetupValueHas Show ext) => Show (SetupValue ext)

-- TypedTerm is neither Eq nor Ord
-- deriving instance (SetupValueHas Eq ext) => Eq (SetupValue ext)
-- deriving instance (SetupValueHas Ord ext) => Ord (SetupValue ext)

-- | Note that most 'SetupValue' concepts (like allocation indices)
--   are implementation details and won't be familiar to users.
--   Consider using 'resolveSetupValue' and printing an 'LLVMVal'
--   with @PP.pretty@ instead.
ppSetupValue :: SetupValue ext -> PP.Doc ann
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> ppAllocIndex i
  SetupNull _    -> PP.pretty "NULL"
  SetupStruct _ packed vs
    | packed     -> PP.angles (PP.braces (commaList (map ppSetupValue vs)))
    | otherwise  -> PP.braces (commaList (map ppSetupValue vs))
  SetupArray _ vs  -> PP.brackets (commaList (map ppSetupValue vs))
  SetupElem _ v i  -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ show i)
  SetupField _ v f -> PP.parens (ppSetupValue v) PP.<> PP.pretty ("." ++ f)
  SetupGlobal _ nm -> PP.pretty ("global(" ++ nm ++ ")")
  SetupGlobalInitializer _ nm -> PP.pretty ("global_initializer(" ++ nm ++ ")")
  where
    commaList :: [PP.Doc ann] -> PP.Doc ann
    commaList []     = PP.emptyDoc
    commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

ppAllocIndex :: AllocIndex -> PP.Doc ann
ppAllocIndex i = PP.pretty '@' <> PP.viaShow i

ppTypedTerm :: TypedTerm -> PP.Doc ann
ppTypedTerm (TypedTerm tp tm) =
  PP.unAnnotate (ppTerm defaultPPOpts tm)
  PP.<+> PP.pretty ":" PP.<+>
  PP.viaShow (Cryptol.ppPrec 0 tp)

ppTypedExtCns :: TypedExtCns -> PP.Doc ann
ppTypedExtCns (TypedExtCns tp ec) =
  PP.unAnnotate (ppName (ecName ec))
  PP.<+> PP.pretty ":" PP.<+>
  PP.viaShow (Cryptol.ppPrec 0 tp)

setupToTypedTerm ::
  Options {-^ Printing options -} ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO TypedTerm
setupToTypedTerm opts sc sv =
  case sv of
    SetupTerm term -> return term
    _ -> do t <- setupToTerm opts sc sv
            lift $ mkTypedTerm sc t

-- | Convert a setup value to a SAW-Core term. This is a partial
-- function, as certain setup values ---SetupVar, SetupNull and
-- SetupGlobal--- don't have semantics outside of the symbolic
-- simulator.
setupToTerm ::
  Options ->
  SharedContext ->
  SetupValue ext ->
  MaybeT IO Term
setupToTerm opts sc =
  \case
    SetupTerm term -> return (ttTerm term)

    SetupStruct _ _ fields ->
      do ts <- mapM (setupToTerm opts sc) fields
         lift $ scTuple sc ts

    SetupArray _ elems@(_:_) ->
      do ts@(t:_) <- mapM (setupToTerm opts sc) elems
         typt <- lift $ scTypeOf sc t
         vec <- lift $ scVector sc typt ts
         typ <- lift $ scTypeOf sc vec
         lift $ printOutLn opts Info $ show vec
         lift $ printOutLn opts Info $ show typ
         return vec

    SetupElem _ base ind ->
      case base of
        SetupArray _ elems@(e:_) ->
          do let intToNat = fromInteger . toInteger
             art <- setupToTerm opts sc base
             ixt <- lift $ scNat sc $ intToNat ind
             lent <- lift $ scNat sc $ intToNat $ length elems
             et <- setupToTerm opts sc e
             typ <- lift $ scTypeOf sc et
             lift $ scAt sc lent typ art ixt

        SetupStruct _ _ fs ->
          do st <- setupToTerm opts sc base
             lift $ scTupleSelector sc st ind (length fs)

        _ -> MaybeT $ return Nothing

    -- SetupVar, SetupNull, SetupGlobal
    _ -> MaybeT $ return Nothing

--------------------------------------------------------------------------------
-- ** Ghost state

-- TODO: This is language-independent, it should be always-true rather than a
-- toggle.

-- TODO: documentation

type family HasGhostState ext :: Bool

type GhostValue  = "GhostValue"
type GhostType   = Crucible.IntrinsicType GhostValue Crucible.EmptyCtx
type GhostGlobal = Crucible.GlobalVar GhostType

--------------------------------------------------------------------------------
-- ** Pre- and post-conditions

--------------------------------------------------------------------------------
-- *** ResolvedState

-- | A datatype to keep track of which parts of the simulator state -- have been initialized already. For each allocation unit or global,
-- we keep a list of element-paths that identify the initialized
-- sub-components.
data ResolvedState =
  ResolvedState
    { _rsAllocs :: Map AllocIndex [[Either String Int]]
    , _rsGlobals :: Map String [[Either String Int]]
    }
  deriving (Eq, Ord, Show)

makeLenses ''ResolvedState

emptyResolvedState :: ResolvedState
emptyResolvedState = ResolvedState Map.empty Map.empty

-- | Record the initialization of the pointer represented by the given
-- SetupValue.
markResolved ::
  SetupValue ext ->
  [Either String Int] {-^ path within this object (if any) -} ->
  ResolvedState ->
  ResolvedState
markResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        SetupVar n         -> rs & rsAllocs %~ Map.alter (ins path) n
        SetupGlobal _ name -> rs & rsGlobals %~ Map.alter (ins path) name
        SetupElem _ v idx  -> go (Right idx : path) v
        SetupField _ v fld -> go (Left fld : path) v
        _                  -> rs

    ins path Nothing = Just [path]
    ins path (Just paths) = Just (path : paths)

-- | Test whether the pointer represented by the given SetupValue has
-- been initialized already.
testResolved ::
  SetupValue ext ->
  [Either String Int] {-^ path within this object (if any) -} ->
  ResolvedState ->
  Bool
testResolved val0 path0 rs = go path0 val0
  where
    go path val =
      case val of
        SetupVar n         -> test path (Map.lookup n (_rsAllocs rs))
        SetupGlobal _ c    -> test path (Map.lookup c (_rsGlobals rs))
        SetupElem _ v idx  -> go (Right idx : path) v
        SetupField _ v fld -> go (Left fld : path) v
        _                  -> False

    test _ Nothing = False
    test path (Just paths) = any (`isPrefixOf` path) paths


--------------------------------------------------------------------------------
-- *** Extension-specific information

type family CrucibleContext ext :: Type

-- | How to specify allocations in this syntax extension
type family AllocSpec ext :: Type

-- | The type of identifiers for types in this syntax extension
type family TypeName ext :: Type

-- | The type of types of the syntax extension we're dealing with
type family ExtType ext :: Type

-- | The type of points-to assertions
type family PointsTo ext :: Type

-- | The type of global allocations
type family AllocGlobal ext :: Type

--------------------------------------------------------------------------------
-- *** StateSpec

data SetupCondition ext where
  SetupCond_Equal    :: ProgramLoc -> SetupValue ext -> SetupValue ext -> SetupCondition ext
  SetupCond_Pred     :: ProgramLoc -> TypedTerm -> SetupCondition ext
  SetupCond_Ghost    :: B (HasGhostState ext) ->
                        ProgramLoc ->
                        GhostGlobal ->
                        TypedTerm ->
                        SetupCondition ext

deriving instance ( SetupValueHas Show ext
                  , Show (B (HasGhostState ext))
                  ) => Show (SetupCondition ext)

-- | Verification state (either pre- or post-) specification
data StateSpec ext = StateSpec
  { _csAllocs        :: Map AllocIndex (AllocSpec ext)
    -- ^ allocated or declared pointers
  , _csPointsTos     :: [PointsTo ext]
    -- ^ points-to statements
  , _csConditions    :: [SetupCondition ext]
    -- ^ equality, propositions, and ghost-variable conditions
  , _csFreshVars     :: [TypedExtCns]
    -- ^ fresh variables created in this state
  , _csVarTypeNames  :: !(Map AllocIndex (TypeName ext))
    -- ^ names for types of variables, for diagnostics
  }

makeLenses ''StateSpec

initialStateSpec :: StateSpec ext
initialStateSpec =  StateSpec
  { _csAllocs        = Map.empty
  , _csPointsTos     = []
  , _csConditions    = []
  , _csFreshVars     = []
  , _csVarTypeNames  = Map.empty
  }

--------------------------------------------------------------------------------
-- *** Method specs

-- | How to identify methods in a codebase
type family MethodId ext :: Type

-- | A body of code in which a method resides
--
-- Examples: An 'LLVMModule', a Java 'Codebase'
type family Codebase ext :: Type

data CrucibleMethodSpecIR ext =
  CrucibleMethodSpec
  { _csMethod          :: MethodId ext
  , _csArgs            :: [ExtType ext]
  , _csRet             :: Maybe (ExtType ext)
  , _csPreState        :: StateSpec ext -- ^ state before the function runs
  , _csPostState       :: StateSpec ext -- ^ state after the function runs
  , _csArgBindings     :: Map Integer (ExtType ext, SetupValue ext) -- ^ function arguments
  , _csRetValue        :: Maybe (SetupValue ext) -- ^ function return value
  , _csGlobalAllocs    :: [AllocGlobal ext] -- ^ globals allocated
  , _csSolverStats     :: SolverStats -- ^ statistics about the proof that produced this
  , _csCodebase        :: Codebase ext -- ^ the codebase this spec was verified against
  , _csLoc             :: ProgramLoc -- ^ where in the SAWscript was this spec?
  }

makeLenses ''CrucibleMethodSpecIR

-- TODO: remove when what4 switches to prettyprinter
prettyPosition :: Position -> PP.Doc ann
prettyPosition = PP.viaShow

ppMethodSpec ::
  ( PP.Pretty (MethodId ext)
  , PP.Pretty (ExtType ext)
  ) =>
  CrucibleMethodSpecIR ext ->
  PP.Doc ann
ppMethodSpec methodSpec =
  PP.vcat
  [ PP.pretty "Name: " <> PP.pretty (methodSpec ^. csMethod)
  , PP.pretty "Location: " <> prettyPosition (plSourceLoc (methodSpec ^. csLoc))
  , PP.pretty "Argument types: "
  , bullets '-' (map PP.pretty (methodSpec ^. csArgs))
  , PP.pretty "Return type: " <> case methodSpec ^. csRet of
                                       Nothing  -> PP.pretty "<void>"
                                       Just ret -> PP.pretty ret
  ]

csAllocations :: CrucibleMethodSpecIR ext -> Map AllocIndex (AllocSpec ext)
csAllocations
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csAllocs)

csTypeNames :: CrucibleMethodSpecIR ext -> Map AllocIndex (TypeName ext)
csTypeNames
  = Map.unions
  . toListOf ((csPreState <> csPostState) . csVarTypeNames)

makeCrucibleMethodSpecIR ::
  MethodId ext ->
  [ExtType ext] ->
  Maybe (ExtType ext) ->
  ProgramLoc ->
  Codebase ext ->
  CrucibleMethodSpecIR ext
makeCrucibleMethodSpecIR meth args ret loc code = do
  CrucibleMethodSpec
    {_csMethod          = meth
    ,_csArgs            = args
    ,_csRet             = ret
    ,_csPreState        = initialStateSpec
    ,_csPostState       = initialStateSpec
    ,_csArgBindings     = Map.empty
    ,_csRetValue        = Nothing
    ,_csGlobalAllocs    = []
    ,_csSolverStats     = mempty
    ,_csLoc             = loc
    ,_csCodebase        = code
    }
