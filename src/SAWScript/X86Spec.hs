{-# Language GADTs, KindSignatures, DataKinds, ImplicitParams #-}
{-# Language PatternSynonyms, TypeFamilies, TypeSynonymInstances #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language OverloadedStrings #-}
{-# Language ExistentialQuantification #-}
{-# Language Rank2Types #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language ConstraintKinds #-}
{-# Language PartialTypeSignatures #-}
{-# Language CPP #-}
#if __GLASGOW_HASKELL__ >= 806
{-# Language NoStarIsType #-}
#endif
module SAWScript.X86Spec
  ( Specification(..)
  , SpecType, Pre, Post
  , FunSpec(..)
  , verifyMode
  , overrideMode
  , State(..)
  , Loc(..)
  , V(..)
  , Prop(..)
  , Alloc(..)
  , Area(..)
  , Mode(..)
  , Unit(..)
  , (*.)
  , inMem
  , (===)
  , Opts(..)
  , KnownType
  , intLit
  , litByte
  , litWord
  , litDWord
  , litQWord
  , litV128
  , litV256
  , area
  , LLVMPointerType
  , Overrides
  , debugPPReg

  , Sym
  , freshRegister

  -- * Cryptol
  , CryArg(..)
  , cryPre
  , cryCur
  , cryTerm
  , cryConst
  , mkGlobalMap
  ) where

import GHC.TypeLits(KnownNat)
import GHC.Natural(Natural)
import Data.Kind(Type)
import Control.Applicative ( (<|>) )
import Control.Lens (view, (^.), over)
import qualified Data.BitVector.Sized as BV
import Data.List(sortBy)
import Data.Maybe(catMaybes)
import Data.Map (Map)
import Data.Proxy(Proxy(..))
import qualified Data.Map as Map
import Data.IORef(newIORef,atomicModifyIORef')
import Data.String
import Control.Monad.Reader

import Data.Parameterized.NatRepr
import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Pair

import Data.Foldable(foldlM, toList)

import What4.Interface
          (bvLit,isEq, Pred, notPred, orPred, natEq, freshNat
          , bvUle, truePred, natLit, asNat, andPred, userSymbol, freshConstant )
import What4.ProgramLoc

import Lang.Crucible.FunctionHandle
import SAWScript.Crucible.LLVM.CrucibleLLVM
  ( EndianForm(LittleEndian)
  , MemImpl, doLoad, doPtrAddOffset, emptyMem
  , AllocType(HeapAlloc, GlobalAlloc), Mutability(..), Mem
  , pattern LLVMPointerRepr, doMalloc, storeConstRaw, packMemValue
  , LLVMPointerType, LLVMVal(LLVMValInt)
  , ptrEq, LLVMPtr, ppPtr, llvmPointerView, projectLLVM_bv, llvmPointer_bv
  , muxLLVMPtr
  , bitvectorType
  , Bytes, bytesToInteger, toBytes
  , StorageType
  , noAlignment
  , pattern LLVMPointer
  )
import qualified Lang.Crucible.LLVM.MemModel as Crucible

import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.Backend
          (addAssumption, getProofObligations, proofGoalsToList
          ,assert, AssumptionReason(..)
          ,LabeledPred(..), ProofGoal(..), labeledPredMsg)

import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.CFG.Common
import Lang.Crucible.Simulator.RegMap

--import Lang.Crucible.Backend.SAWCore
--  (bindSAWTerm,sawBackendSharedContext,toSC,SAWCoreBackend)
import Lang.Crucible.Types
  (TypeRepr(..),BaseTypeRepr(..),BaseToType,CrucibleType)

import Verifier.SAW.SharedTerm
  (Term,scApplyAll,scVector,scBitvector,scAt,scNat)
import Data.Macaw.Memory(RegionIndex)
import Data.Macaw.Symbolic(GlobalMap, ToCrucibleType, LookupFunctionHandle(..), MacawCrucibleRegTypes)
import Data.Macaw.Symbolic.Backend ( crucArchRegTypes )
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.Symbolic
     (x86_64MacawSymbolicFns,lookupX86Reg,updateX86Reg)
import Data.Macaw.X86.ArchTypes(X86_64)
import qualified Data.Macaw.Types as M

import Verifier.SAW.CryptolEnv(CryptolEnv(..), lookupIn, getAllIfaceDecls)
import Verifier.SAW.Simulator.What4.ReturnTrip

import Cryptol.ModuleSystem.Name(Name)
import Cryptol.ModuleSystem.Interface(ifTySyns)
import Cryptol.TypeCheck.AST(TySyn(tsDef))
import Cryptol.TypeCheck.TypePat(aNat)
import Cryptol.Utils.PP(render,pp)
import Cryptol.Utils.Patterns(matchMaybe)

import SAWScript.Crucible.Common (Sym, sawCoreState)


data Specification = Specification
  { specAllocs  :: ![Alloc]
  , specPres    :: ![(String, Prop Pre)]
  , specPosts   :: ![(String, Prop Post)]

  , specGlobsRO :: ![ (String, Integer, Unit, [ Integer ]) ]
    -- ^ Read only globals.

  , specCalls   :: ![ (String, Integer, Int -> Specification) ]
    -- ^ Specifications for the functions we call.
    -- The integer is the absolute address of the function.
    -- The "Int" counts how many times we called this function so far.
  }

data Unit = Bytes | Words | DWords | QWords | V128s | V256s deriving Show

{- | A specifiction for a function.
The outer, "Pre", computiation sets up the initial state of the
computation (i.e., the pre-condition for the function).
As a result, we return the inital register assignemtn,
and the post-condition for the function). -}
data FunSpec =
    NewStyle (CryptolEnv -> IO Specification)
             (State -> IO ())
              -- Debug: Run this to print some stuff at interesting times.

-- | Is this a pre- or post-condition specificiation.
data {- kind -} SpecType = Pre | Post

-- | We are specifying a pre-condition.
type Pre  = 'Pre

-- | We are specifying a post-condition.
type Post = 'Post



data Opts = Opts
  { optsSym :: Sym
  , optsMvar :: GlobalVar Mem
  , optsCry :: CryptolEnv
  }

(*.) :: Integer -> Unit -> Bytes
n *. u = toBytes (fromInteger n * bs)
  where bs = unitByteSize u natValue :: Natural

unitBitSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitBitSize u k = unitByteSize u $ \bits ->
  case leqMulPos (knownNat @8) bits of
    LeqProof -> k (natMultiply (knownNat @8) bits)

unitByteSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitByteSize u k =
  case u of
    Bytes  -> k (knownNat @1)
    Words  -> k (knownNat @2)
    DWords -> k (knownNat @4)
    QWords -> k (knownNat @8)
    V128s  -> k (knownNat @16)
    V256s  -> k (knownNat @32)



data Mode = RO    -- ^ Starts initialized; cannot write to it
          | RW    -- ^ Starts initialized; can write to it
          | WO    -- ^ Starts uninitialized; can write to it
          deriving (Eq,Show)

data Area = Area
  { areaName :: String
  , areaMode :: Mode
  , areaSize :: (Integer,Unit)

  , areaHasPointers :: Bool
    -- ^ Could this area contain pointers

  , areaPtr  :: Bytes
    {- ^ The canonical pointer to this area is this many bytes from
    -- the start of the actual object.
    -- When we initialize such an area, we allocate it, then advnace
    -- the pointer by this much, and return *that* as the value of
    -- initialization.

    -- When we match such an area, we get the value as it,
    -- but then we have to check that there are this many bytes *before*
    -- the value we got.
    -}
  }

area :: String -> Mode -> Integer -> Unit -> Area
area n m u s = Area { areaName = n
                  , areaMode = m
                  , areaSize = (u,s)
                  , areaHasPointers = False
                  , areaPtr = 0 *. Bytes
                  }

data Loc :: CrucibleType -> Type where

  InMem :: (1 <= w) =>
           NatRepr w                {- Read this much (in bytes) -} ->
           Loc (LLVMPointerType 64) {- Read from this pointer -} ->
           Integer                  {- Starting at this offset in bytes -} ->
           Loc (LLVMPointerType (8*w))

  InReg :: X86Reg tp -> Loc (ToCrucibleType tp)

instance Show (Loc t) where
  show x =
    case x of
      InReg r -> show r
      InMem w l o ->
        "[" ++ show l ++ off ++ " |" ++ show (8 * natValue w) ++ "]"
        where off | o < 0     = " - " ++ show (negate o)
                  | o == 0    = ""
                  | otherwise = " + " ++ show o

inMem ::
  (1 <= w, KnownNat w) =>
  Loc (LLVMPointerType 64) ->
  Integer ->
  Unit ->
  Loc (LLVMPointerType (8 * w))
inMem l n u = InMem knownNat l (bytesToInteger (n *. u))

instance TestEquality Loc where
  testEquality x y = case compareF x y of
                       EQF -> Just Refl
                       _   -> Nothing

-- | Allocation order.  Also used when resolving equalities,
-- the smallest number is the representative.
instance OrdF Loc where
  compareF x y =
    case (x,y) of
      (InReg a, InReg b) -> case compareF a b of
                              EQF -> EQF
                              LTF -> LTF
                              GTF -> GTF

      (InReg {}, InMem {}) -> LTF
      (InMem {}, InReg {}) -> GTF
      (InMem s a i, InMem t b j) ->
        case compareF a b of
          EQF -> case compare i j of
                   LT -> LTF
                   GT -> GTF
                   EQ -> case compareF s t of
                           LTF -> LTF -- XXX: shouldn't allow?
                           GTF -> GTF -- XXX: shouldn't allow?
                           EQF -> EQF
          LTF -> LTF
          GTF -> GTF



data Alloc = Loc (LLVMPointerType 64) := Area

allocArea :: Alloc -> Area
allocArea (_ := a) = a

cmpAlloc :: Alloc -> Alloc -> Ordering
cmpAlloc (l1 := _) (l2 := _) = case compareF l1 l2 of
                                 LTF -> LT
                                 EQF -> EQ
                                 GTF -> GT

data V :: SpecType -> CrucibleType -> Type where

  CryFun ::
    (1 <= w) => NatRepr w -> String -> [CryArg p] -> V p (LLVMPointerType w)
  -- An opaque Cryptol term term; WARNING: type is unchecked

  IntLit :: (1 <= w) => NatRepr w -> Integer -> V p (LLVMPointerType w)
  -- A literal value

  -- The whole location thing needs to be fixed...

  Loc    :: Loc t -> V p t
  -- Read the value at the location in the *current* state:
  -- pre or post depending on `p`

  PreLoc :: Loc t -> V Post t
  -- Read the location from the pre-condition state.

  PreAddPtr ::
    Loc (LLVMPointerType 64) -> Integer -> Unit -> V Post (LLVMPointerType 64)
  -- Add a constant to a pointer from a location in the pre-condition.


instance Show (V p t) where
  show val =
    case val of
      CryFun w f xs -> pars (f ++ " " ++ unwords (map show xs) ++ sh w)
      IntLit w x -> pars (show x ++ sh w)
      Loc l     -> show l
      PreLoc l  -> pars ("pre " ++ show l)
      PreAddPtr l i u ->
          pars ("pre &" ++ show l ++ " + " ++ show i ++ " " ++ show u)

    where
    pars x = "(" ++ x ++ ")"
    sh w = " : [" ++ show (natValue w) ++ "]"


litByte :: Integer -> V p (LLVMPointerType 8)
litByte = intLit

litWord :: Integer -> V p (LLVMPointerType 16)
litWord = intLit

litDWord :: Integer -> V p (LLVMPointerType 32)
litDWord = intLit

litQWord :: Integer -> V p (LLVMPointerType 64)
litQWord = intLit

litV128 :: Integer -> V p (LLVMPointerType 128)
litV128 = intLit

litV256 :: Integer -> V p (LLVMPointerType 256)
litV256 = intLit

intLit :: (1 <= w, KnownNat w) => Integer -> V p (LLVMPointerType w)
intLit = IntLit knownNat



data CryArg :: SpecType -> Type where
  CryNat    :: Integer -> CryArg p
  Cry       :: V p (LLVMPointerType w) -> CryArg p
  CryArrCur :: V p (LLVMPointerType 64) -> Integer -> Unit -> CryArg p
  CryArrPre :: V Post (LLVMPointerType 64) -> Integer -> Unit -> CryArg Post


instance Show (CryArg p) where
  show x =
    case x of
      Cry v -> show v
      CryNat n -> show n
      CryArrCur p n u -> "[" ++ show p ++ "|" ++ show n ++ " " ++ show u ++ "]"
      CryArrPre p n u ->
        "[pre " ++ show p ++ "|" ++ show n ++ " " ++ show u ++ "]"

cryPre :: Loc (LLVMPointerType w) -> CryArg Post
cryPre l = Cry (PreLoc l)

cryCur :: Loc (LLVMPointerType w) -> CryArg p
cryCur l = Cry (Loc l)


data Prop :: SpecType -> Type where
  Same    :: TypeRepr t -> V p t -> V p t -> Prop p
  CryProp :: String -> [ CryArg p ] -> Prop p
  CryPostMem ::
    V Post (LLVMPointerType 64) {- starting here -} ->
    Integer                     {- this many elemnts -} ->
    Unit                        {- of this size -} ->
    String                      {- are defined by this Cry. func. -} ->
    [CryArg Post]               {- applied to these argumnets -} ->
    Prop Post

type KnownType = KnownRepr TypeRepr

(===) :: KnownType t => V p t -> V p t -> Prop p
x === y = Same knownRepr x y

locRepr :: Loc t -> TypeRepr t
locRepr l =
  case l of
    InMem w _ _ -> ptrTy w
    InReg r ->
      case M.typeRepr r of
        M.BVTypeRepr w -> LLVMPointerRepr w
        M.BoolTypeRepr -> BoolRepr
        M.TupleTypeRepr {} -> error $ "[locRepr] Unexpected tuple register"
        M.FloatTypeRepr {} -> error $ "[locRepr] Unexpected float register"
        M.VecTypeRepr {} -> error $ "[locRepr] Unexpected vector register"

--------------------------------------------------------------------------------

data State = State
  { stateMem  :: MemImpl Sym
  , stateRegs :: Ctx.Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)
  }

freshState :: Sym -> IO State
freshState sym =
  do regs <- Ctx.traverseWithIndex (freshRegister sym) knownRepr
     mem  <- emptyMem LittleEndian
     return State { stateMem = mem, stateRegs = regs }

freshRegister :: Sym -> Ctx.Index ctx tp -> TypeRepr tp -> IO (RegValue' Sym tp)
freshRegister sym idx repr = RV <$> freshVal sym repr True ("reg" ++ show idx)

freshVal ::
  Sym -> TypeRepr t -> Bool {- ptrOK ?-}-> String -> IO (RegValue Sym t)
freshVal sym t ptrOk nm =
  case t of
    BoolRepr -> do
      sn <- symName nm
      freshConstant sym sn BaseBoolRepr
    LLVMPointerRepr w
      | ptrOk, Just Refl <- testEquality w (knownNat @64) -> do
          sn_base <- symName (nm ++ "_base")
          sn_off <- symName (nm ++ "_off")
          base <- freshNat sym sn_base
          off <- freshConstant sym sn_off (BaseBVRepr w)
          return (LLVMPointer base off)
      | otherwise -> do
          sn <- symName nm
          base <- natLit sym 0
          off <- freshConstant sym sn (BaseBVRepr w)
          return (LLVMPointer base off)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)

  where
  symName s =
    case userSymbol ("macaw_" ++ s) of
      Left err -> error ("Invalid symbol name " ++ show s ++ ": " ++ show err)
      Right a -> return a

getLoc :: Crucible.HasLLVMAnn Sym => Loc t -> Sym -> State -> IO (RegValue Sym t)
getLoc l =
  case l of

    InReg r ->
      \_ s -> case lookupX86Reg r (stateRegs s) of
                Just (RV v) -> return v
                _           -> fail ("[getLoc] Invalid register: " ++ show r)

    InMem w lm n ->
      \sym s ->
      do obj <- getLoc lm sym s
         let mem = stateMem s
         let ?ptrWidth = knownNat
         loc <- adjustPtr sym mem obj n
         doLoad sym mem loc (llvmBytes w) (locRepr l) noAlignment


ptrTy :: (1 <= w) => NatRepr w -> TypeRepr (LLVMPointerType (8 * w))
ptrTy wb
  | LeqProof <- leqMulPos (knownNat @8) wb =
        LLVMPointerRepr (natMultiply (knownNat @8) wb)

llvmBytes :: NatRepr w -> StorageType
llvmBytes w = bitvectorType (toBytes (natValue w))

setLoc :: Crucible.HasLLVMAnn Sym => Loc t -> Sym -> RegValue Sym t -> State -> IO State
setLoc l =

  case l of
    InReg r ->
      \_ v s ->
        case updateX86Reg r (const (RV v)) (stateRegs s) of
          Just rs -> return s { stateRegs = rs }
          Nothing -> fail ("[setLoc] Invalid register: " ++ show r)

    InMem w lm n ->
      \sym v s ->
          do obj <- getLoc lm sym s
             let mem = stateMem s
             let ?ptrWidth = knownNat
             loc <- adjustPtr sym mem obj n

             let lty = llvmBytes w
                 ty  = locRepr l
             val <- packMemValue sym lty ty v
             let alignment = noAlignment -- default to byte-aligned (FIXME)
             mem1 <- storeConstRaw sym mem loc lty alignment val

             return s { stateMem = mem1 }


class Eval p where
  type S p
  eval :: Crucible.HasLLVMAnn Sym => V p t -> Opts -> S p -> IO (RegValue Sym t)
  curState :: f p -> S p -> State
  setCurState :: f p -> State -> S p -> S p

evIntLit :: (1 <= w) => Sym -> NatRepr w -> Integer -> IO (LLVMPtr Sym w)
evIntLit sym w n = llvmPointer_bv sym =<< bvLit sym w (BV.mkBV w n)

instance Eval Pre where
  type S Pre = State
  eval val =
    case val of
      CryFun w f xs  -> \opts s -> evalCryFun opts s w f xs
      IntLit w n     -> \opts _ -> evIntLit (optsSym opts) w n
      Loc l          -> \opts s -> getLoc l (optsSym opts) s
  curState _ s = s
  setCurState _ s _ = s

instance Eval Post where
  type S Post = (State,State)
  eval val =
    case val of
      CryFun w f xs   -> \opts s         -> evalCryFun opts s w f xs
      IntLit w n      -> \opts _         -> evIntLit (optsSym opts) w n
      Loc l           -> \opts (_,post)  -> getLoc l (optsSym opts) post
      PreLoc l        -> \opts (pre,_)   -> getLoc l (optsSym opts) pre
      PreAddPtr l i u -> \opts (pre,_) ->
        do let sym = optsSym opts
           ptr <- getLoc l sym pre
           adjustPtr sym (stateMem pre) ptr (bytesToInteger (i *. u))

  curState _ (_,s) = s
  setCurState _ s (s1,_) = (s1,s)

evalCry :: forall p. (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> CryArg p -> S p -> IO Term
evalCry opts cry s =
  do let sym = optsSym opts
     st <- sawCoreState sym
     let sc = saw_ctx st
     case cry of
       CryNat n -> scNat sc (fromInteger n)

       Cry v -> toSC sym st =<< projectLLVM_bv sym =<< eval v opts s

       CryArrCur ptr n u ->
         unitByteSize u $ \byteW ->
         do vs <- readArr opts ptr n byteW s (curState (Proxy @p) s)
            terms <- mapM (\x -> toSC sym st =<< projectLLVM_bv sym x) vs
            ty <- scBitvector sc (fromIntegral (8 * natValue byteW))
            scVector sc ty terms

       CryArrPre ptr n u ->
         unitByteSize u $ \byteW ->
         do vs <- readArr opts ptr n byteW s (fst s)
            terms <- mapM (\x -> toSC sym st =<< projectLLVM_bv sym x) vs
            ty <- scBitvector sc (fromIntegral (8 * natValue byteW))
            scVector sc ty terms

evalCryFunGen ::
  (Eval p, Crucible.HasLLVMAnn Sym) =>
  Opts ->
  S p ->
  BaseTypeRepr t ->
  String ->
  [CryArg p] ->
  IO (RegValue Sym (BaseToType t))
evalCryFunGen opts s ty f xs =
  do let sym = optsSym opts
     st <- sawCoreState sym
     ts <- mapM (\x -> evalCry opts x s) xs
     bindSAWTerm sym st ty =<< cryTerm opts f ts


-- | Cryptol function that returns a list of bit-vectors.
evalCryFunArr ::
  (1 <= w, Eval p, Crucible.HasLLVMAnn Sym) =>
  Opts ->
  S p ->
  Integer ->
  NatRepr w ->
  String ->
  [CryArg p] ->
  IO [ LLVMPtr Sym w ]
evalCryFunArr opts s n w f xs =
  do term <- cryTerm opts f =<< mapM (\x -> evalCry opts x s) xs
     let sym = optsSym opts
     st  <- sawCoreState sym
     let sc = saw_ctx st
     len <- scNat sc (fromInteger n)
     ty  <- scBitvector sc (natValue w)
     let atIx i = do ind    <- scNat sc (fromInteger i)
                     term_i <- scAt sc len ty term ind
                     bv <- bindSAWTerm sym st (BaseBVRepr w) term_i
                     llvmPointer_bv sym bv
     mapM atIx [ 0 .. n - 1 ]


-- | Cryptol function that returns a bitvector of the given len
evalCryFun ::
  (1 <= w, Eval p, Crucible.HasLLVMAnn Sym) =>
  Opts ->
  S p ->
  NatRepr w ->
  String ->
  [CryArg p] ->
  IO (LLVMPtr Sym w)
evalCryFun opts s w f xs =
  llvmPointer_bv (optsSym opts) =<< evalCryFunGen opts s (BaseBVRepr w) f xs

evalProp :: (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> Prop p -> S p -> IO (Pred Sym)
evalProp opts p s =
  case p of
    Same t x y ->
      do v1 <- eval x opts s
         v2 <- eval y opts s
         evalSame sym t v1 v2

    CryProp f xs -> evalCryFunGen opts s BaseBoolRepr f xs

    CryPostMem ptr n u f xs ->
      -- unitBitSize  u $ \wBits ->
      unitByteSize u $ \wBytes ->
      do LeqProof <- return (leqMulPos (Proxy @8) wBytes)
         let wBits = natMultiply (knownNat @8) wBytes
         need   <- evalCryFunArr opts s n wBits f xs -- expected values
         have   <- readArr opts ptr n wBytes s (snd s)
         checks <- zipWithM (ptrEq sym wBits) need have
         foldM (andPred sym) (truePred sym) checks
  where
  sym = optsSym opts


readArr :: forall w p.
  (1 <= w, Eval p, Crucible.HasLLVMAnn Sym) =>
  Opts ->
  V p (LLVMPointerType 64) ->
  Integer ->
  NatRepr w ->
  S p ->
  State ->
  IO [ LLVMPtr Sym (8 * w) ]
readArr opts ptr n wBytes s sMem =
  do ptrV <- eval ptr opts s
     LeqProof <- return (leqMulPos (Proxy @8) (Proxy @w))
     let sym    = optsSym opts
         mem    = stateMem sMem
         wBits  = natMultiply (knownNat @8) wBytes
         cruT   = LLVMPointerRepr wBits
         llT    = llvmBytes wBytes
         getAt i =
           do let ?ptrWidth = knownNat
              loc <- adjustPtr sym mem ptrV (i * toInteger (natValue wBytes))
              doLoad sym mem loc llT cruT noAlignment

     mapM getAt [ 0 .. n - 1 ]


evalSame ::
  Sym -> TypeRepr t -> RegValue Sym t -> RegValue Sym t -> IO (Pred Sym)
evalSame sym t v1 v2 =
  case t of
    BoolRepr          -> isEq sym v1 v2
    LLVMPointerRepr w -> ptrEq sym w v1 v2
    it -> fail ("[evalProp] Unexpected value repr: " ++ show it)



-- | Add an assertion to the post-condition.
doAssert :: (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> S p -> (String, Prop p) -> IO ()
doAssert opts s (msg,p) =
  do pr <- evalProp opts p s
     assert (optsSym opts) pr (AssertFailureSimError msg "")


--------------------------------------------------------------------------------

data Rep t = Rep (TypeRepr t) Int

instance Eq (Rep t) where
  Rep _ x == Rep _ y = x == y

instance TestEquality Rep where
  testEquality x y = case compareF x y of
                       EQF -> Just Refl
                       _   -> Nothing

instance OrdF Rep where
  compareF (Rep s x) (Rep t y) =
    case compareF s t of
      LTF -> LTF
      GTF -> GTF
      EQF -> case compare x y of
                LT -> LTF
                GT -> GTF
                EQ -> EQF

data RepMap p = RepMap
  { repFor :: MapF.MapF Loc Rep
     -- ^ Keeps track of the representative for a value

  , repBy  :: MapF.MapF Rep (Equiv p)
    -- ^ Inverse of the above: keeps track of which locs have this rep.

  , nextRep :: !Int
  }


emptyRepMap :: RepMap p
emptyRepMap = RepMap { repFor = MapF.empty
                     , repBy = MapF.empty
                     , nextRep = 0
                     }

data Equiv p t = Equiv [ Loc t ] [ V p t ] deriving Show

jnEquiv :: Equiv p t -> Equiv p t -> Equiv p t
jnEquiv (Equiv xs ys) (Equiv as bs) = Equiv (xs ++ as) (ys ++ bs)

-- | Add a fresh representative for something that had no rep before.
newRep :: TypeRepr t -> Equiv p t -> RepMap p -> (Rep t, RepMap p)
newRep t xs mp =
  let n = nextRep mp
      r = Rep t n
  in (r, mp { nextRep = n + 1
            , repBy   = MapF.insert r xs (repBy mp)
            })

getRep :: TypeRepr t -> RepMap p -> Loc t -> (Rep t, RepMap p)
getRep t mp x =
  case MapF.lookup x (repFor mp) of
    Nothing -> let (r,mp1) = newRep t (Equiv [x] []) mp
               in (r, mp1 { repFor = MapF.insert x r (repFor mp1) })
    Just y  -> (y, mp)


addEqLocVal :: TypeRepr t -> Loc t -> V p t -> RepMap p -> RepMap p
addEqLocVal t loc lit mp =
  let (x1,mp1) = getRep t mp loc
      (x2,mp2) = newRep t (Equiv [] [lit]) mp1
  in joinReps x1 x2 mp2

addEqLocLoc :: TypeRepr t -> Loc t -> Loc t -> RepMap p -> RepMap p
addEqLocLoc t x y mp =
  let (x1,mp1) = getRep t mp  x
      (y1,mp2) = getRep t mp1 y
  in joinReps x1 y1 mp2

joinReps :: Rep t -> Rep t -> RepMap p -> RepMap p
joinReps x y mp
  | x == y = mp
  | otherwise =
    -- x is the new rep
    case MapF.lookup y (repBy mp) of
      Nothing -> error "[joinReps] Empty equivalance class"
      Just new@(Equiv ls _) ->
        let setRep z = MapF.insert z x
        in mp { repBy = MapF.insertWith jnEquiv x new
                      $ MapF.delete y (repBy mp)
              , repFor = foldr setRep (repFor mp) ls
              }

getEq :: (String,Prop p) -> RepMap p -> RepMap p
getEq (_,p) mp =
  case p of
    Same t (Loc x) (Loc y) -> addEqLocLoc t x y mp
    Same t (Loc x) v       -> addEqLocVal t x v mp
    Same t v       (Loc x) -> addEqLocVal t x v mp
    _                      -> mp

makeEquiv :: forall p. (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> S p -> Pair Rep (Equiv p) -> IO (S p)
makeEquiv opts s (Pair (Rep t _) (Equiv xs ys)) =
  do -- Note that (at least currently) the `ys` do not
     -- depend on the current state: they are all either `Lit`
     -- or SAW terms, or `PreLoc`.  This is why we can evaluate
     -- them now, without worrying about dependencies.  I think. (Yav)

     -- XXX: With the introduction of `CryFun` one could depend on the
     -- current state.  For now, we are simply careful not to,
     -- in particular, `CryFun` is used only in pre-conditions and all
     -- its argumnets are `LocPre` (i.e., the values before execution).

     -- Note 2: Sometimes it is useful for CryFun to depend on the current
     -- state.  For example, consider a function which computes two things
     -- f : x -> (a,b)
     -- Now we may have specs like this:
     --    a = spec1 x
     --    b = spec2 x a
     -- Of course, we could replcae `b` by:
     --    b = spec2 x (spec1 x)
     -- but that's ugly and duplicates stuff.

     vs <- mapM (\v -> eval v opts s) ys

     let sym = optsSym opts
     let pName = Proxy :: Proxy p
     let cur = curState pName s

     (v,rest) <- case vs of
                   v : us -> return (v,us)
                   [] -> case xs of
                           [] -> error "[makeEquiv] Empty equivalence class"
                           l : _ -> do v <- getLoc l sym cur
                                       return (v,[])

     s1 <- foldM (\s' y -> setLoc y sym v s') cur xs

     let same a =
           do p <- evalSame sym t v a
              let loc = mkProgramLoc "<makeEquiv>" InternalPos
              addAssumption sym (LabeledPred p (AssumptionReason loc "equivalance class assumption"))

     mapM_ same rest

     return (setCurState pName s1 s)


makeEquivs :: (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> RepMap p -> S p -> IO (S p)
makeEquivs opts mp s = foldM (makeEquiv opts) s (MapF.toList (repBy mp))



addAsmp :: (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> S p -> (String,Prop p) -> IO ()
addAsmp opts s (msg,p) =
  case p of
    Same _ (Loc _) _ -> return ()
    Same _ _ (Loc _) -> return ()
    CryPostMem {}    -> return ()

    _ -> do p' <- evalProp opts p s
            let loc = mkProgramLoc "<addAssmp>" InternalPos -- FIXME
            addAssumption (optsSym opts) (LabeledPred p' (AssumptionReason loc msg))

setCryPost :: forall p. (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> S p -> (String,Prop p) -> IO (S p)
setCryPost opts s (_nm,p) =
  case p of
    CryPostMem ptr n u f xs ->
      unitBitSize  u $ \bitW ->
      unitByteSize u $ \byteW ->
      do vs   <- evalCryFunArr opts s n bitW f xs
         ptrV <- eval ptr opts s
         let llT  = llvmBytes byteW
             cruT = LLVMPointerRepr bitW
             sym  = optsSym opts

         let doSet mem (i,v) =
               do let ?ptrWidth = knownNat
                  loc <- adjustPtr sym mem ptrV (bytesToInteger (i *. u))
                  val <- packMemValue sym llT cruT v
                  let alignment = noAlignment -- default to byte-aligned (FIXME)
                  storeConstRaw sym mem loc llT alignment val

         let cur   = Proxy @p
             curSt = curState cur s :: State
         mem1 <- foldM doSet (stateMem curSt) (zip [ 0 .. ] vs)
         return (setCurState cur curSt { stateMem = mem1 } s)

    _ -> return s


addAssumptions ::
  forall p. (Eval p, Crucible.HasLLVMAnn Sym) => Opts -> S p -> [(String, Prop p)] -> IO State
addAssumptions opts s0 ps =
  do let mp = foldr getEq emptyRepMap ps
     s1 <- makeEquivs opts mp s0
     s2 <- foldM (setCryPost opts) s1 ps
     mapM_ (addAsmp opts s2) ps
     return (curState (Proxy :: Proxy p) s2)


--------------------------------------------------------------------------------

-- | Allocate a memory region.
allocate :: Crucible.HasLLVMAnn Sym => Sym -> Area -> State -> IO (LLVMPtr Sym 64, State)
allocate sym ar s =
  case areaMode ar of
    RO -> do (base,p,m1) <- alloc Immutable
             m2     <- fillFresh sym withPtrs base uni names m1
             return (p, s { stateMem = m2 })

    RW -> do (base,p,m1) <- alloc Mutable
             m2 <- fillFresh sym withPtrs base uni names m1
             return (p, s { stateMem = m2 })

    WO -> do (_,p,m1) <- alloc Mutable
             return (p, s { stateMem = m1 })
  where
  withPtrs = areaHasPointers ar

  alloc mut =
    do let ?ptrWidth = knownNat @64
       let szInt = bytesToInteger (uncurry (*.) (areaSize ar))
       sz <- bvLit sym knownNat (BV.mkBV knownNat szInt)
       let alignment = noAlignment -- default to byte-aligned (FIXME)
       (base,mem) <- doMalloc sym HeapAlloc mut (areaName ar) (stateMem s) sz alignment
       ptr <- adjustPtr sym mem base (bytesToInteger (areaPtr ar))
       return (base,ptr,mem)

  (num,uni) = areaSize ar

  names :: [String]
  names = [ areaName ar ++ "_" ++ show uni ++ "_" ++ show i
          | i <- take (fromInteger num) [ 0 :: Int .. ] ]

fillFresh ::
  Crucible.HasLLVMAnn Sym =>
  Sym -> Bool -> LLVMPtr Sym 64 -> Unit ->
  [String] -> MemImpl Sym -> IO (MemImpl Sym)
fillFresh sym ptrOk p u todo mem =
  unitByteSize u $ \w ->
  case todo of
    [] -> return mem
    nm : more ->
      do let ?ptrWidth = knownNat
         let ty        = ptrTy w
         let elS       = toInteger (natValue w)
         let lty       = bitvectorType (toBytes elS)
         val <- packMemValue sym lty ty =<< freshVal sym ty ptrOk nm
         -- Here we use the write that ignore mutability.
         -- This is because we are writinging initialization code.
         let alignment = noAlignment -- default to byte-aligned (FIXME)
         mem1 <- storeConstRaw sym mem p lty alignment val
         p1   <- adjustPtr sym mem1 p elS
         fillFresh sym ptrOk p1 u more mem1


-- | Make an allocation.  Used when verifying.
doAlloc :: Crucible.HasLLVMAnn Sym => Sym -> State -> Alloc -> IO State
doAlloc sym s (l := a) =
  do (p,s1) <- allocate sym a s
     setLoc l sym p s1

-- | Fill-in a memory area with fresh values.
-- This has no effect if the area is RO.
clobberArea ::
  Crucible.HasLLVMAnn Sym =>
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Area -> IO (MemImpl Sym)
clobberArea sym mem p ar =
  case areaMode ar of
    RO -> return mem
    _  ->
      do base <- adjustPtr sym mem p (negate (bytesToInteger (areaPtr ar)))
         let (num,uni) = areaSize ar
             xs = take (fromInteger num)
                  [ areaName ar ++ "_" ++ show uni ++ "_at_" ++ show i
                                                      | i <- [ 0 :: Int .. ]]
         fillFresh sym (areaHasPointers ar) base uni xs mem


-- | Lookup the value for an allocation in the existing state.
-- Used when overriding.
-- Returns the start and end of the allocation.
checkAlloc :: Crucible.HasLLVMAnn Sym => Sym -> State -> Alloc -> IO (LLVMPtr Sym 64, LLVMPtr Sym 64)
checkAlloc sym s (l := a) =
  do p1 <- getLoc l sym s
     let mem = stateMem s
     p2 <- adjustPtr sym mem p1 (negate (bytesToInteger (areaPtr a)))

     -- Make sure that we have a pointer and it is big enough.
     let siI = bytesToInteger $ uncurry (*.) (areaSize a)
     p3 <- adjustPtr sym mem p2 siI
     return (p2,p3)

-- | Implements a layer to map 'LLVMPtr's to their underlying allocations, as
-- tracked by the 'RegionIndex' map
--
-- NOTE: If the initial obvious mapping (where the concrete nat is in the map)
-- fails, there are two possibilities:
--
-- 1. The region ID is concrete but not in the map.  We should just pass it
--    through without modifying it, since it is a valid LLVM pointer
-- 2. The region ID is symbolic.  In this case, we need to generate a mux that
--    dispatches to the entries in the map when they match, or otherwise passes
--    the pointer through untouched.
--
-- If the region ID is concretely zero, it should be the case that the
-- 'RegionIndex' map would translate it into a real 'LLVMPtr' since the only map
-- entry (established in 'setupGlobals') is for 0.
mkGlobalMap ::
  Crucible.HasLLVMAnn Sym =>
  Map.Map RegionIndex (LLVMPtr Sym 64) ->
  GlobalMap Sym Crucible.Mem 64
mkGlobalMap rmap sym mem region off =
  mapConcreteRegion <|> passThroughConcreteRegion <|> mapSymbolicRegion
  where
    mapConcreteRegion = maybe mzero id (addOffset <$> thisRegion)
    thisRegion = join (findRegion <$> asNat region)
    findRegion r = Map.lookup (fromIntegral r) rmap
    addOffset p = doPtrAddOffset sym mem p off
      where ?ptrWidth = knownNat
    passThroughConcreteRegion =
      case asNat region of
        Nothing -> mzero
        Just _ -> return (LLVMPointer region off)
    -- If the symbolic nat is (symbolically) equal to any of the entries in the
    -- rmap, we need to do the translation; otherwise, we pass it through
    mapSymbolicRegion = foldlM muxSymbolicRegion (LLVMPointer region off) (Map.toList rmap)
    muxSymbolicRegion others (regionNum, basePtr) = do
      thisRegionNat <- natLit sym (fromIntegral regionNum)
      isEqRegion <- natEq sym thisRegionNat region
      adjustedPtr <- addOffset basePtr
      muxLLVMPtr sym isEqRegion adjustedPtr others

-- | Setup globals in a single read-only region (index 0).
setupGlobals ::
  Crucible.HasLLVMAnn Sym =>
  Opts ->
  [(String,Integer,Unit,[Integer])] ->
  [(String,Integer,Int -> Specification)] ->
  State ->
  IO ((GlobalMap Sym Crucible.Mem 64, Overrides), State)
setupGlobals opts gs fs s
  | null regions && null fs = return ((mkGlobalMap Map.empty, Map.empty), s)

  | not (null overlaps) =
      fail $ unlines $ "Overlapping regions in global spec:"
                     : [ "*** " ++ x ++ " and " ++ y
                          | (x,y) <- overlaps ]

  | otherwise =
    do let endGlob = case last regions of
                       (_,start,n) -> start + bytesToInteger n
           size    = maximum (endGlob : fundAddrs)

       let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat (BV.mkBV knownNat size)
       let alignment = noAlignment -- default to byte-aligned (FIXME)
       (p,mem) <- doMalloc sym GlobalAlloc Immutable "Globals" (stateMem s) sz alignment

       let Just base = asNat (fst (llvmPointerView p))

       mem1 <- foldM (writeGlob p) mem gs
       let gMap = mkGlobalMap (Map.singleton 0 p)

           {- NOTE:  Some functions are called multiple times with different
                     sizes. This means that we need different specs for them,
                     at least until we support polymorphic specs.  As a quick
                     work-around we count the number of times a function is
                     entered and provide this as an input to the spec.
                     In simple cases this allows the spec to change itslef. -}
           mkHandler (name,a, sp) =
              do entryCounter <- newIORef 0
                 let fname = fromString name
                 return $
                    ( (base,a)
                    , \_ -> LookupFunctionHandle $ \st _ _ ->
                         do
                            let sty = crucArchRegTypes x86_64MacawSymbolicFns
                            let rty = StructRepr sty
                            let o = mkOverride' fname rty $ do
                                      ent <- liftIO $ atomicModifyIORef' entryCounter $
                                                             \e -> (e + 1, e)
                                      -- liftIO $ putStrLn ("ENTER " ++ _f)
                                      sym' <- getSymInterface
                                      RegMap args <- getOverrideArgs
                                      mem' <- readGlobal (optsMvar opts)
                                      let st0 = State { stateRegs = regValue (Ctx.last args), stateMem = mem' }
                                      -- liftIO $ debugPPReg RCX st0
                                      st1 <- liftIO $ overrideMode (sp ent) opts { optsSym = sym' } st0
                                      -- liftIO $ debugPPReg RCX st1
                                      writeGlobal (optsMvar opts) (stateMem st1)
                                      -- liftIO $ putStrLn ("EXIT " ++ _f)
                                      return (stateRegs st1)
                            let halloc = simHandleAllocator (st ^. stateContext)
                            h <- mkHandle halloc fname
                            let addBinding = over (stateContext . functionBindings)
                                               (FnBindings . insertHandleMap h (UseOverride o) . fnBindings)
                            return (h, addBinding st)
                      )

       fMap <- Map.fromList <$> mapM mkHandler fs

       return ((gMap,fMap), s { stateMem = mem1 })
  where
  sym = optsSym opts

  fundAddrs = [ a | (_,a,_) <- fs ]

  regions = sortBy cmpStart
          $ [ (nm,start, fromIntegral (length els) *. u)
              | (nm,start,u,els) <- gs ]
  cmpStart (_,s1,_) (_,s2,_) = compare s1 s2

  overlaps = catMaybes (zipWith check regions (tail regions))

  -- check for overlap, assuming first one starts at smaller address.
  check (r1,s1,n1) (r2,s2,_)
    | s1 + bytesToInteger n1 <= s2 = Nothing
    | otherwise                    = Just (r1,r2)

  writeGlob base mem (_,start,u,els) =
    do p <- adjustPtr sym mem base start
       snd <$> foldM (writeU u) (p,mem) els

  writeU u (p,mem) v =
    unitBitSize u $ \w ->
      do let sz = 1 *. u
             szI = bytesToInteger sz
             lty = bitvectorType sz
         z    <- natLit sym 0
         val  <- LLVMValInt z <$> bvLit sym w (BV.mkBV w v)
         let ?ptrWidth = knownNat
         let alignment = noAlignment -- default to byte-aligned (FIXME)
         mem1 <- storeConstRaw sym mem p lty alignment val
         p1   <- adjustPtr sym mem1 p szI
         return (p1,mem1)

debugPPReg ::
  (ToCrucibleType mt ~ LLVMPointerType w) =>
  X86Reg mt -> State -> IO ()
debugPPReg r s =
  do let Just (RV v) = lookupX86Reg r (stateRegs s)
     putStrLn (show r ++ " = " ++ show (ppPtr v))

_debugDumpGoals :: Sym -> IO ()
_debugDumpGoals sym =
  do obls <- proofGoalsToList <$> getProofObligations sym
     mapM_ sh (toList obls)
  where
  sh (ProofGoal _hyps g) = print (view labeledPredMsg g)


type Overrides = Map (Natural,Integer) (Sym -> LookupFunctionHandle Sym X86_64)

-- | Use a specification to verify a function.
-- Returns the initial state for the function, and a post-condition.
verifyMode ::
  Crucible.HasLLVMAnn Sym =>
  Specification ->
  Opts ->
  IO ( (GlobalMap Sym Crucible.Mem 64, Overrides)
     , State
     , State -> IO ()
     )
verifyMode spec opts =
  do let sym = optsSym opts
     s0 <- freshState sym
     (globs,s1) <- setupGlobals opts (specGlobsRO spec) (specCalls spec) s0
     s2 <- foldM (doAlloc sym) s1 $ sortBy cmpAlloc $ specAllocs spec
     s3 <- addAssumptions opts s2 (specPres spec)
     let post sF = mapM_ (doAssert opts (s3,sF)) (specPosts spec)
     return (globs, s3, post)

-- | Ensure that writable areas do not overlap with any other areas.
checkOverlaps :: Crucible.HasLLVMAnn Sym => Sym -> [((LLVMPtr Sym 64, LLVMPtr Sym 64), Area)] -> IO ()
checkOverlaps sym = check
  where
  check (p : ps) = mapM_ (nonOverLap p) ps >> check ps
  check []       = return ()

  nonOverLap ((p1,p2),ar1) ((q1,q2),ar2)
    -- Read-only area may overlap
    | areaMode ar1 == RO && areaMode ar2 == RO = return ()

    | otherwise =
    do let (a1,x1) = llvmPointerView p1
           (_, x2) = llvmPointerView p2
           (b1,y1) = llvmPointerView q1
           (_,y2)  = llvmPointerView q2
       opt1 <- notPred sym =<< natEq sym a1 b1
       opt2 <- bvUle sym x2 y1
       opt3 <- bvUle sym y2 x1
       ok <- orPred sym opt1 =<< orPred sym opt2 opt3
       let msg = unlines
             [ "Potentially aliased pointers:"
             , "*** " ++ show (ppPtr p1)
             , "*** " ++ show (ppPtr q1)
             ]
       assert sym ok $ AssertFailureSimError msg ""

-- | Use a specification to replace the execution of a function.
overrideMode :: Crucible.HasLLVMAnn Sym => Specification -> Opts -> State -> IO State
overrideMode spec opts s =
  do let sym = optsSym opts
     let orderedAllocs = sortBy cmpAlloc (specAllocs spec)
     as <- mapM (checkAlloc sym s) orderedAllocs    -- check sizes
     checkOverlaps sym (zip as (map allocArea orderedAllocs)) -- check distinct
     mapM_ (doAssert opts s) (specPres spec)         -- assert pre-condition

     newRegs <- stateRegs <$> freshState sym

     mem1 <- foldM (\s' (p,a) -> clobberArea sym s' p a) (stateMem s)
           $ reverse $ zip (map fst as) [ a | _ := a <- orderedAllocs ]

     let sNew1 = State { stateMem = mem1, stateRegs = newRegs  }
     sf <- addAssumptions opts (s,sNew1) (specPosts spec)

     -- XXX: When Macaw calls us, the IP is already at the adress of the
     -- called function.  Unfortunately, the return address is not on top
     -- of the stack, as it shold be, so we don't know the correct value.
     -- It looks like things work, if keep the orignal value instead.

     let Just ip0 = lookupX86Reg X86_IP (stateRegs s)
     let Just finalRegs = updateX86Reg X86_IP (const ip0) (stateRegs sf)
     return sf { stateRegs = finalRegs }



--------------------------------------------------------------------------------
-- Cryptol


-- | Lookup a cryptol term, and apply it to the given arguments,
-- returning the result.
cryTerm :: Opts -> String -> [Term] -> IO Term
cryTerm opts x xs =
  case lookupCry x (eTermEnv (optsCry opts)) of
    Left err -> fail err
    Right t ->
     do let sym = optsSym opts
        sc <- saw_ctx <$> sawCoreState sym
        scApplyAll sc t xs

-- | Lookup a Crytpol type synonym, which should resolve to a constant.
cryConst :: CryptolEnv -> String -> Either String Integer
cryConst env x =
  do let mp = ifTySyns (getAllIfaceDecls (eModuleEnv env))
     t <- lookupCry x mp
     case matchMaybe (aNat (tsDef t)) of
       Just n  -> return n
       Nothing -> Left (x ++ " is not a fixed constant type synonym.")

-- | Lookup a name in a map indexed by Cryptol names.
lookupCry :: String -> Map Name a -> Either String a
lookupCry x mp =
  case x `lookupIn` mp of
    Left [] -> Left $ unlines $ ("Missing Cryptol name: " ++ show x)
                              : [ "*** " ++ ppName y | y <- Map.keys mp ]
    Left ys -> Left $ unlines ( "Ambiguous Cryptol name:"
                              : [ "*** " ++ ppName y | y <- ys ]
                              )
    Right a -> Right a

  where ppName = render . pp




--------------------------------------------------------------------------------


adjustPtr ::
  Crucible.HasLLVMAnn Sym =>
  Sym ->
  MemImpl Sym ->
  LLVMPtr Sym 64 ->
  Integer ->
  IO (LLVMPtr Sym 64)
adjustPtr sym mem ptr amt
  | amt == 0  = return ptr
  | otherwise =
    do let ?ptrWidth = knownNat
       doPtrAddOffset sym mem ptr =<< bvLit sym knownNat (BV.mkBV knownNat amt)
