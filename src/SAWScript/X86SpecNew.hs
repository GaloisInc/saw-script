{-# Language GADTs, KindSignatures, DataKinds, ImplicitParams #-}
{-# Language PatternSynonyms, TypeFamilies, TypeSynonymInstances #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
module SAWScript.X86SpecNew
  ( Specification(..)
  , verifyMode
  , overrideMode
  , State(..)
  , Loc(..)
  , Prop(..)
  , Alloc(..)
  , Area(..)
  , Mode(..)
  ) where

import Data.Kind(Type)
import Control.Monad(foldM)
import Data.List(sortBy)

import Data.Parameterized.NatRepr
import Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Pair

import Lang.Crucible.LLVM.DataLayout(EndianForm(LittleEndian))
import Lang.Crucible.LLVM.MemModel
  ( MemImpl,coerceAny,doLoad,doPtrAddOffset,doStore, emptyMem
  , pattern LLVMPointerRepr, doMalloc, storeConstRaw, packMemValue
  , LLVMPointerType )
import Lang.Crucible.LLVM.MemModel.Pointer
    (ptrEq, LLVMPtr, ppPtr, llvmPointerView)
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import qualified Lang.Crucible.LLVM.MemModel.Type as LLVM
import Lang.Crucible.LLVM.Bytes(Bytes,bytesToInteger,toBytes)
import Lang.Crucible.LLVM.MemModel.Generic(AllocType(HeapAlloc), Mutability(..))
import Lang.Crucible.Simulator.RegValue(RegValue'(..),RegValue)
import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.Solver.Interface
          (bvLit,isEq, Pred, addAssumption, addAssertion, notPred, orPred
          , bvUle )
import Lang.Crucible.Solver.SAWCoreBackend(bindSAWTerm)
import Lang.Crucible.Types(TypeRepr(..),BaseTypeRepr(..),BaseToType,CrucibleType)

import Verifier.SAW.SharedTerm(Term)
import Data.Macaw.Symbolic(freshValue)
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType)
import Data.Macaw.Symbolic(Regs, macawAssignToCrucM )
import Data.Macaw.Symbolic.CrucGen(MacawSymbolicArchFunctions(..))
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.Symbolic
            (x86_64MacawSymbolicFns,lookupX86Reg,updateX86Reg,freshX86Reg)
import Data.Macaw.X86.ArchTypes(X86_64)
import qualified Data.Macaw.Types as M

import SAWScript.X86Spec.Types(Sym)
import SAWScript.X86Spec.Monad(SpecType,Pre,Post)

data Mode = RO    -- ^ Starts initialized; cannot write to it
          | RW    -- ^ Starts initialized; can write to it
          | WO    -- ^ Starts uninitialized; can write to it

data Area where
  Array :: (1 <= w) =>
           String    {- ^ Name -} ->
           Mode      {- ^ Read/write etc. -} ->
           Integer   {- ^ Number of elements -} ->
           NatRepr w {- ^ Size in bytes of each element -} ->
           Area

areaSize :: Area -> Bytes
areaSize a =
  case a of
    Array _ _ n t -> toBytes (n * natValue t)

areaName :: Area -> String
areaName a =
  case a of
    Array s _ _ _ -> s

data Loc :: CrucibleType -> Type where
  InMem :: (1 <= w) =>
           NatRepr w                {- ^ Read this much (in bytes) -} ->
           Loc (LLVMPointerType 64) {- ^ Read from this pointer -} ->
           Integer                  {- ^ Offset in bytes -} ->
           Loc (LLVMPointerType (8*w))
  InReg :: X86Reg tp -> Loc (ToCrucibleType tp)

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

cmpAlloc :: Alloc -> Alloc -> Ordering
cmpAlloc (l1 := _) (l2 := _) = case compareF l1 l2 of
                                 LTF -> LT
                                 EQF -> EQ
                                 GTF -> GT

data V :: SpecType -> CrucibleType -> Type where
  SAW    :: BaseTypeRepr s -> Term  -> V p (BaseToType s)
            -- ^ WARNING: unchecked
  Loc    :: Loc t -> V p t     -- ^ Read the value at the location
                               -- in the *current* state.
  PreLoc :: Loc t -> V Post t  -- ^ Read the value in the pre-condition.

data Prop :: SpecType -> Type where
  Same    :: TypeRepr t -> V p t -> V p t -> Prop p
  SAWProp :: Term -> Prop p

data Specification = Specification
  { specAllocs :: [Alloc]
  , specPres   :: [(String, Prop Pre)]
  , specPosts  :: [(String, Prop Post)]
  }

locRepr :: Loc t -> TypeRepr t
locRepr l =
  case l of
    InMem w _ _ -> ptrTy w
    InReg r ->
      case M.typeRepr r of
        M.BVTypeRepr w -> LLVMPointerRepr w
        M.BoolTypeRepr -> BoolRepr
        M.TupleTypeRepr {} -> error $ "[locRepr] Unexpected tuple register"

--------------------------------------------------------------------------------

data State = State
  { stateMem  :: MemImpl Sym
  , stateRegs :: Regs Sym X86_64
  }

freshState :: Sym -> IO State
freshState sym =
  do regs <- macawAssignToCrucM (freshX86Reg sym) $
             crucGenRegAssignment x86_64MacawSymbolicFns
     mem  <- emptyMem LittleEndian
     return State { stateMem = mem, stateRegs = regs }


freshVal :: Sym -> TypeRepr t -> String -> IO (RegValue Sym t)
freshVal sym t nm =
  case t of
    BoolRepr ->  freshValue sym nm (knownNat @64) M.BoolTypeRepr
    LLVMPointerRepr w -> freshValue sym nm (knownNat @64) (M.BVTypeRepr w)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)


getLoc :: Loc t -> Sym -> State -> IO (RegValue Sym t)
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
         loc <- doPtrAddOffset sym mem obj =<< bvLit sym knownNat n
         anyV <- doLoad sym mem loc (llvmBytes w) 0
         coerceAny sym (locRepr l) anyV


ptrTy :: (1 <= w) => NatRepr w -> TypeRepr (LLVMPointerType (8 * w))
ptrTy wb
  | LeqProof <- leqMulPos (knownNat @8) wb =
        LLVMPointerRepr (natMultiply (knownNat @8) wb)

llvmBytes :: NatRepr w -> LLVM.Type
llvmBytes w = bitvectorType (toBytes (natValue w))

setLoc :: Loc t -> Sym -> RegValue Sym t -> State -> IO State
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
             loc <- doPtrAddOffset sym mem obj =<< bvLit sym knownNat n
             mem1 <- doStore sym mem loc (locRepr l) (llvmBytes w) v
             return s { stateMem = mem1 }


class Eval p where
  type S p
  eval :: V p t -> Sym -> S p -> IO (RegValue Sym t)

instance Eval Pre where
  type S Pre = State
  eval val =
    case val of
      SAW ty t -> \sym _ -> bindSAWTerm sym ty t
      Loc l -> getLoc l

instance Eval Post where
  type S Post = (State,State)
  eval val =
    case val of
      SAW ty t -> \sym _        -> bindSAWTerm sym ty t
      Loc l    -> \sym (_,post) -> getLoc l sym post
      PreLoc l -> \sym (pre,_)  -> getLoc l sym pre

evalProp :: Eval p => Prop p -> Sym -> S p -> IO (Pred Sym)
evalProp p =
  case p of
    Same t x y ->
      \sym s ->
        do v1 <- eval x sym s
           v2 <- eval y sym s
           case t of
             BoolRepr          -> isEq sym v1 v2
             LLVMPointerRepr w -> ptrEq sym w v1 v2
             it -> fail ("[evalProp] Unexpected value repr: " ++ show it)
    SAWProp t -> \sym _ -> bindSAWTerm sym BaseBoolRepr t


-- | Add an assertion to the post-condition.
doAssert :: Eval p => Sym -> S p -> (String, Prop p) -> IO ()
doAssert sym s (msg,p) =
  do pr <- evalProp p sym s
     addAssertion sym pr (AssertFailureSimError msg)


--------------------------------------------------------------------------------

data RepMap = RepMap
  { repFor :: MapF.MapF Loc Loc
     -- ^ Keeps track of the representative for a value
  , repBy  :: MapF.MapF Loc Locs
    -- ^ Inverse of the above: keeps track of which locs have this rep.
  }

emptyRepMap :: RepMap
emptyRepMap = RepMap { repFor = MapF.empty, repBy = MapF.empty }

newtype Locs t = Locs [ Loc t ]

jnLocs :: Locs t -> Locs t -> Locs t
jnLocs (Locs xs) (Locs ys) = Locs (xs ++ ys)

getRep :: RepMap -> Loc t -> Loc t
getRep mp x = case MapF.lookup x (repFor mp) of
                Nothing -> x
                Just y  -> y

addEq :: Loc t -> Loc t -> RepMap -> RepMap
addEq x y mp =
  let x1 = getRep mp x
      y1 = getRep mp y
  in case compareF x1 y1 of
       EQF -> mp
       LTF -> (x1 `isRepFor` y1) mp
       GTF -> (y1 `isRepFor` x1) mp

isRepFor :: Loc t -> Loc t -> RepMap -> RepMap
(x `isRepFor` y) mp =
  let newReps = case MapF.lookup y (repBy mp) of
                  Nothing -> [y]
                  Just (Locs xs) -> y : xs
      setRep z = MapF.insert z x
  in RepMap { repBy   = MapF.insertWith jnLocs x (Locs newReps)
                      $ MapF.delete y (repBy mp)
            , repFor  = foldr setRep (repFor mp) newReps
            }

makeEquiv :: Sym -> State -> Pair Loc Locs -> IO State
makeEquiv sym s (Pair x (Locs xs)) =
  do v  <- getLoc x sym s
     foldM (\s' y -> setLoc y sym v s') s xs

makeEquivs :: Sym -> RepMap -> State -> IO State
makeEquivs sym mp s = foldM (makeEquiv sym) s (MapF.toList (repBy mp))

setPrePost :: Sym -> State -> State -> (String,Prop Post) -> IO State
setPrePost sym s1 s2 (_,p) =
  case p of
    Same _ (PreLoc x) (Loc y) ->
      do v <- getLoc x sym s1
         setLoc y sym v s2
    Same _ (Loc y) (PreLoc x) ->
      do v <- getLoc x sym s1
         setLoc y sym v s2
    _ -> return s2

getEq :: (String,Prop p) -> RepMap -> RepMap
getEq (_,p) mp =
  case p of
    Same _ (Loc x) (Loc y) -> addEq x y mp
    _                      -> mp

addAsmp :: Eval p => Sym -> S p -> (String,Prop p) -> IO ()
addAsmp sym s (_,p) =
  case p of
    Same _ (Loc _) (Loc _) -> return ()
    Same _ (PreLoc _) (Loc _) -> return ()
    Same _ (Loc _) (PreLoc _) -> return ()
    _ -> addAssumption sym =<< evalProp p sym s


addAssumptions :: Sym -> State -> [(String, Prop Pre)] -> IO State
addAssumptions sym s0 ps =
  do s1 <- makeEquivs sym (foldr getEq emptyRepMap ps) s0
     mapM_ (addAsmp sym s1) ps
     return s1

addAssumptionsPost ::
  Sym -> (State,State) -> [(String, Prop Post)] -> IO State
addAssumptionsPost sym (s1,s2) ps =
  do s3 <- foldM (setPrePost sym s1) s2 ps
     s4 <- makeEquivs sym (foldr getEq emptyRepMap ps) s3
     mapM_ (addAsmp sym (s1,s4)) ps
     return s4


--------------------------------------------------------------------------------

-- | Allocate a memory region.
allocate :: Sym -> Area -> State -> IO (LLVMPtr Sym 64, State)
allocate sym area s =
  case area of
    Array nm mode size w ->
      case mode of
        RO -> do (p,m1) <- alloc nm Immutable
                 m2     <- fillFresh sym w p (names nm size) m1
                 return (p, s { stateMem = m2 })

        RW -> do (p,m1) <- alloc nm Mutable
                 m2 <- fillFresh sym w p (names nm size) m1
                 return (p, s { stateMem = m2 })

        WO -> do (p,m1) <- alloc nm Mutable
                 return (p, s { stateMem = m1 })
  where
  alloc str mut =
    do let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat (bytesToInteger (areaSize area))
       doMalloc sym HeapAlloc mut str (stateMem s) sz

  names :: String -> Integer -> [String]
  names nm todo = [ nm ++ "_at_" ++ show i
                        | i <- take (fromInteger todo) [ 0 :: Int .. ] ]


fillFresh ::
  (1 <= w) => Sym -> NatRepr w -> LLVMPtr Sym 64 ->
           [String] -> MemImpl Sym -> IO (MemImpl Sym)
fillFresh sym w p todo mem =
  case todo of
    [] -> return mem
    nm : more ->
      do let ?ptrWidth = knownNat
         let ty        = ptrTy w
         let elS       = natValue w
         let lty       = bitvectorType (toBytes elS)
         x   <- freshVal sym ty nm
         val <- packMemValue sym lty ty x
         -- Here we use the write that ignore mutability.
         -- This is because we are writinging initialization code.
         mem1 <- storeConstRaw sym mem p lty val
         off <- bvLit sym knownNat elS
         p1 <- doPtrAddOffset sym mem1 p off
         fillFresh sym w p1 more mem1


-- | Make an allocation.  Used when verifying.
doAlloc :: Sym -> State -> Alloc -> IO State
doAlloc sym s (l := a) =
  do (p,s1) <- allocate sym a s
     setLoc l sym p s1

-- | Fill-in a memory area with fresh values.
clobberArea ::
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Area -> IO (MemImpl Sym)
clobberArea sym mem p area =
  do let xs = take (fromInteger (bytesToInteger (areaSize area)))
                   [ areaName area ++ "_at_" ++ show i | i <- [ 0 :: Int .. ]]
     fillFresh sym (knownNat @1) p xs mem


-- | Lookup the value for an allocation in the existing state.
-- Used when overriding.
-- Returns the start and end of the allocation.
checkAlloc :: Sym -> State -> Alloc -> IO (LLVMPtr Sym 64, LLVMPtr Sym 64)
checkAlloc sym s (l := a) =
  do p1 <- getLoc l sym s
     let is = bytesToInteger (areaSize a)
     -- Make sure that we have a pointer and it is big enough.
     let ?ptrWidth = knownNat
     p2 <- doPtrAddOffset sym (stateMem s) p1 =<< bvLit sym knownNat is
     return (p1,p2)

-- | Use a specification to verify a function.
-- Returns the initial state for the function, and a post-condition.
verifyMode :: Specification -> Sym -> IO (State, State -> IO ())
verifyMode spec sym =
  do s0 <- freshState sym
     s1 <- foldM (doAlloc sym) s0 $ sortBy cmpAlloc $ specAllocs spec
     s2 <- addAssumptions sym s1 (specPres spec)
     let post sF = mapM_ (doAssert sym (s2,sF)) (specPosts spec)
     return (s2, post)

checkOverlaps :: Sym -> [(LLVMPtr Sym 64, LLVMPtr Sym 64)] -> IO ()
checkOverlaps sym = check
  where
  check (p : ps) = mapM_ (nonOverLap p) ps >> check ps
  check []       = return ()

  nonOverLap (p1,p2) (q1,q2) =
    do let (a1,x1) = llvmPointerView p1
           (_, x2) = llvmPointerView p2
           (b1,y1) = llvmPointerView q1
           (_,y2)  = llvmPointerView q2
       opt1 <- notPred sym =<< isEq sym a1 b1
       opt2 <- bvUle sym x2 y1
       opt3 <- bvUle sym y2 x1
       ok <- orPred sym opt1 =<< orPred sym opt2 opt3
       addAssertion sym ok $ AssertFailureSimError $
         unlines [ "Potentially aliased pointers:"
                 , "*** " ++ show (ppPtr p1)
                 , "*** " ++ show (ppPtr q1)
                 ]

-- | Use a specification to replace the execution of a function.
overrideMode :: Specification -> Sym -> State -> IO State
overrideMode spec sym s =
  do let orderedAllocs = sortBy cmpAlloc (specAllocs spec)
     as <- mapM (checkAlloc sym s) orderedAllocs    -- check sizes
     checkOverlaps sym as                           -- check distinct
     mapM_ (doAssert sym s) (specPres spec)         -- assert pre-condition

     sNew0 <- freshState sym

     mem1 <- foldM (\s' (p,a) -> clobberArea sym s' p a) (stateMem s)
           $ reverse $ zip (map fst as) [ a | _ := a <- orderedAllocs ]

     let sNew1 = sNew0 { stateMem = mem1 }
     addAssumptionsPost sym (s,sNew1) (specPosts spec)

