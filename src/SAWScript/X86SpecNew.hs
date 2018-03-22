{-# Language GADTs, KindSignatures, DataKinds, ImplicitParams #-}
{-# Language PatternSynonyms, TypeFamilies, TypeSynonymInstances #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language ExistentialQuantification #-}
{-# Language Rank2Types #-}
{-# Language FlexibleContexts #-}
module SAWScript.X86SpecNew
  ( Specification(..)
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
  , (===)
  , Opts(..)

  -- * Cryptol
  , CryArg(..)
  , cryTerm
  , cryConst
  ) where

import Data.Kind(Type)
import Control.Monad(foldM)
import Data.List(sortBy)
import Data.Maybe(catMaybes)
import Data.Map (Map)
import qualified Data.Map as Map

import Data.Parameterized.NatRepr
import Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Pair

import Lang.Crucible.LLVM.DataLayout(EndianForm(LittleEndian))
import Lang.Crucible.LLVM.MemModel
  ( MemImpl,coerceAny,doLoad,doPtrAddOffset, emptyMem
  , pattern LLVMPointerRepr, doMalloc, storeConstRaw, packMemValue
  , LLVMPointerType, LLVMVal(LLVMValInt) )
import Lang.Crucible.LLVM.MemModel.Pointer
    (ptrEq, LLVMPtr, ppPtr, llvmPointerView, projectLLVM_bv)
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import qualified Lang.Crucible.LLVM.MemModel.Type as LLVM
import Lang.Crucible.LLVM.Bytes(Bytes,bytesToInteger,toBytes)
import Lang.Crucible.LLVM.MemModel.Generic
    (AllocType(HeapAlloc,GlobalAlloc), Mutability(..))
import Lang.Crucible.Simulator.RegValue(RegValue'(..),RegValue)
import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.Solver.Interface
          (bvLit,isEq, Pred, addAssumption, addAssertion, notPred, orPred
          , bvUle, truePred, falsePred, natLit )
import Lang.Crucible.Solver.SAWCoreBackend
  (bindSAWTerm,sawBackendSharedContext,toSC)
import Lang.Crucible.Types
  (TypeRepr(..),BaseTypeRepr(..),BaseToType,CrucibleType
  , BoolType, BVType )

import Verifier.SAW.SharedTerm(Term,scApplyAll)
import Data.Macaw.Symbolic(freshValue,GlobalMap)
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType)
import Data.Macaw.Symbolic(Regs, macawAssignToCrucM )
import Data.Macaw.Symbolic.CrucGen(MacawSymbolicArchFunctions(..))
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.Symbolic
            (x86_64MacawSymbolicFns,lookupX86Reg,updateX86Reg,freshX86Reg)
import Data.Macaw.X86.ArchTypes(X86_64)
import qualified Data.Macaw.Types as M

import Verifier.SAW.CryptolEnv(CryptolEnv(..), lookupIn, getAllIfaceDecls)

import Cryptol.ModuleSystem.Name(Name)
import Cryptol.ModuleSystem.Interface(ifTySyns)
import Cryptol.TypeCheck.AST(TySyn(tsDef))
import Cryptol.TypeCheck.TypePat(aNat)
import Cryptol.Utils.PP(alwaysQualify,runDoc,pp)
import Cryptol.Utils.Patterns(matchMaybe)


import SAWScript.X86Spec.Types(Sym)
import SAWScript.X86Spec.Monad(SpecType,Pre,Post)

data Specification = Specification
  { specAllocs  :: [Alloc]
  , specPres    :: [(String, Prop Pre)]
  , specPosts   :: [(String, Prop Post)]

  , specGlobsRO :: [ (String, Integer, Unit, [ Integer ]) ]
    -- ^ Read only globals. 
  }

data Unit = Bytes | Words | DWords | QWords | V128s | V256s


data Opts = Opts
  { optsSym :: Sym
  , optsCry :: CryptolEnv
  }

(*.) :: Integer -> Unit -> Bytes
n *. u = toBytes (fromIntegral n * bs)
  where
  bs :: Integer
  bs = case u of
         Bytes  -> 1
         Words  -> 2
         DWords -> 4
         QWords -> 8
         V128s  -> 16
         V256s  -> 32

unitBitSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitBitSize u k =
  case u of
    Bytes  -> k (knownNat @8)
    Words  -> k (knownNat @16)
    DWords -> k (knownNat @32)
    QWords -> k (knownNat @64)
    V128s  -> k (knownNat @128)
    V256s  -> k (knownNat @256)

data Mode = RO    -- ^ Starts initialized; cannot write to it
          | RW    -- ^ Starts initialized; can write to it
          | WO    -- ^ Starts uninitialized; can write to it
          deriving (Eq,Show)

data Area = Area
  { areaName :: String
  , areaMode :: Mode
  , areaSize :: Bytes

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

allocArea :: Alloc -> Area
allocArea (_ := a) = a

cmpAlloc :: Alloc -> Alloc -> Ordering
cmpAlloc (l1 := _) (l2 := _) = case compareF l1 l2 of
                                 LTF -> LT
                                 EQF -> EQ
                                 GTF -> GT

data V :: SpecType -> CrucibleType -> Type where
  SAW    :: BaseTypeRepr s -> Term  -> V p (BaseToType s)
  -- ^ An opaque SAW term; WARNING: type is unchecked

  Lit    :: Lit t -> V p t
  -- ^ A literal value

  Loc    :: Loc t -> V p t
  -- ^ Read the value at the location
  -- in the *current* state.

  PreLoc :: Loc t -> V Post t
  -- ^ Read the value in the pre-condition.

data Lit :: CrucibleType -> Type where
  BVLit   :: (1 <= w) => NatRepr w -> Integer -> Lit (BVType w)
  BoolLit :: Bool -> Lit BoolType

instance Show (Lit t) where
  show x =
    case x of
      BVLit w i -> "(" ++ show i ++ " : [" ++ show (natValue w) ++ "]"
      BoolLit b -> show b

instance TestEquality Lit where
  testEquality x y = case compareF x y of
                       EQF -> Just Refl
                       _   -> Nothing

instance OrdF Lit where
  compareF x y =
    case (x,y) of

      (BoolLit a, BoolLit b) ->
        case compare a b of
          EQ -> EQF
          LT -> LTF
          GT -> GTF
      (BoolLit _, _) -> LTF
      (_, BoolLit _) -> GTF

      (BVLit w1 a, BVLit w2 b) ->
        case compareF w1 w2 of
          LTF -> LTF
          GTF -> GTF
          EQF -> case compare a b of
                   LT -> LTF
                   EQ -> EQF
                   GT -> GTF

data CryArg p = forall w. Cry (V p (LLVMPointerType w))

data Prop :: SpecType -> Type where
  Same    :: TypeRepr t -> V p t -> V p t -> Prop p
  CryProp :: String -> [ CryArg p ] -> Prop p
  SAWProp :: Term -> Prop p

(===) :: KnownRepr TypeRepr t => V p t -> V p t -> Prop p
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
         loc <- adjustPtr sym mem obj n
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
             loc <- adjustPtr sym mem obj n

             let lty = llvmBytes w
                 ty  = locRepr l
             val <- packMemValue sym lty ty v
             mem1 <- storeConstRaw sym mem loc lty val

             return s { stateMem = mem1 }


class Eval p where
  type S p
  eval :: V p t -> Sym -> S p -> IO (RegValue Sym t)

evalLit :: Sym -> Lit t -> IO (RegValue Sym t)
evalLit sym l =
  case l of
    BVLit w n -> bvLit sym w n
    BoolLit b -> return (if b then truePred sym else falsePred sym)

instance Eval Pre where
  type S Pre = State
  eval val =
    case val of
      SAW ty t -> \sym _ -> bindSAWTerm sym ty t
      Lit l    -> \sym _ -> evalLit sym l
      Loc l    -> getLoc l

instance Eval Post where
  type S Post = (State,State)
  eval val =
    case val of
      SAW ty t -> \sym _        -> bindSAWTerm sym ty t
      Lit l    -> \sym _        -> evalLit sym l
      Loc l    -> \sym (_,post) -> getLoc l sym post
      PreLoc l -> \sym (pre,_)  -> getLoc l sym pre

evalCry :: Eval p => Sym -> CryArg p -> S p -> IO Term
evalCry sym (Cry v) s = toSC sym =<< projectLLVM_bv sym =<< eval v sym s

evalProp :: Eval p => Opts -> Prop p -> S p -> IO (Pred Sym)
evalProp opts p s =
  case p of
    Same t x y ->
      do v1 <- eval x sym s
         v2 <- eval y sym s
         case t of
           BoolRepr          -> isEq sym v1 v2
           LLVMPointerRepr w -> ptrEq sym w v1 v2
           it -> fail ("[evalProp] Unexpected value repr: " ++ show it)

    CryProp f xs ->
      do ts <- mapM (\x -> evalCry sym x s) xs
         bindSAWTerm (optsSym opts) BaseBoolRepr =<< cryTerm opts f ts

    SAWProp t -> bindSAWTerm sym BaseBoolRepr t
  where
  sym = optsSym opts


-- | Add an assertion to the post-condition.
doAssert :: Eval p => Opts -> S p -> (String, Prop p) -> IO ()
doAssert opts s (msg,p) =
  do pr <- evalProp opts p s
     addAssertion (optsSym opts) pr (AssertFailureSimError msg)


--------------------------------------------------------------------------------

data Rep t = RLoc (Loc t)
           | RLit (Lit t)


instance TestEquality Rep where
  testEquality x y = case compareF x y of
                       EQF -> Just Refl
                       _   -> Nothing

-- | We prefer literals as the representatives
instance OrdF Rep where
  compareF x y =
    case (x,y) of
      (RLit a, RLit b) -> compareF a b
      (RLit _, _)      -> LTF
      (_, RLit _)      -> GTF
      (RLoc a, RLoc b) -> compareF a b


data RepMap = RepMap
  { repFor :: MapF.MapF Loc Rep
     -- ^ Keeps track of the representative for a value
  , repBy  :: MapF.MapF Rep Locs
    -- ^ Inverse of the above: keeps track of which locs have this rep.

  , contradiction :: Maybe Contradiction
  }

data Contradiction = forall t. NotEqual (Lit t) (Lit t)

emptyRepMap :: RepMap
emptyRepMap = RepMap { repFor = MapF.empty
                     , repBy = MapF.empty
                     , contradiction = Nothing
                     }

newtype Locs t = Locs [ Loc t ]

jnLocs :: Locs t -> Locs t -> Locs t
jnLocs (Locs xs) (Locs ys) = Locs (xs ++ ys)

getRep :: RepMap -> Loc t -> Rep t
getRep mp x = case MapF.lookup x (repFor mp) of
                Nothing -> RLoc x
                Just y  -> y


addEqLitLit :: Lit t -> Lit t -> RepMap -> RepMap
addEqLitLit x y = RLit x `isRepFor` RLit y

addEqLocLit :: Loc t -> Lit t -> RepMap -> RepMap
addEqLocLit loc lit mp = (RLit lit `isRepFor` getRep mp loc) mp

addEqLocLoc :: Loc t -> Loc t -> RepMap -> RepMap
addEqLocLoc x y mp =
  let x1 = getRep mp x
      y1 = getRep mp y
  in case compareF x1 y1 of
       EQF -> mp
       LTF -> (x1 `isRepFor` y1) mp
       GTF -> (y1 `isRepFor` x1) mp

isRepFor :: Rep t -> Rep t -> RepMap -> RepMap
(x `isRepFor` y) mp =
  case y of
    RLit yl ->
      case x of
        RLit xl
          | Just Refl <- testEquality xl yl -> mp
          | otherwise -> mp { contradiction = Just (NotEqual xl yl) }
        RLoc _  -> error ("[bug] Literal " ++ show yl ++
                          " represented by a location.")
    RLoc yl ->
      let newReps = case MapF.lookup y (repBy mp) of
                      Nothing -> [yl]
                      Just (Locs xs) -> yl : xs
          setRep z = MapF.insert z x
      in RepMap { repBy   = MapF.insertWith jnLocs x (Locs newReps)
                          $ MapF.delete y (repBy mp)
                , repFor  = foldr setRep (repFor mp) newReps
                , contradiction = contradiction mp
                }

makeEquiv :: Sym -> State -> Pair Rep Locs -> IO State
makeEquiv sym s (Pair x (Locs xs)) =
  do v  <- case x of
             RLoc l -> getLoc l sym s
             RLit l -> evalLit sym l
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
    Same _ (Loc x) (Loc y) -> addEqLocLoc x y mp
    Same _ (Loc x) (Lit y) -> addEqLocLit x y mp
    Same _ (Lit x) (Loc y) -> addEqLocLit y x mp
    Same _ (Lit x) (Lit y) -> addEqLitLit x y mp
    _                      -> mp

addAsmp :: Eval p => Opts -> S p -> (String,Prop p) -> IO ()
addAsmp opts s (_,p) =
  case p of
    Same _ (Loc _) (Loc _) -> return ()
    Same _ (Loc _) (Lit _) -> return ()
    Same _ (Lit _) (Loc _) -> return ()
    Same _ (Lit _) (Lit _) -> return ()
    Same _ (PreLoc _) (Loc _) -> return ()
    Same _ (Loc _) (PreLoc _) -> return ()
    _ -> addAssumption (optsSym opts) =<< evalProp opts p s


addAssumptions :: Opts -> State -> [(String, Prop Pre)] -> IO State
addAssumptions opts s0 ps =
  do let sym = optsSym opts
     let mp = foldr getEq emptyRepMap ps
     case contradiction mp of
       Nothing -> return ()
       Just (NotEqual x y) ->
         fail $ unlines [ "Attempt to assume false equality:"
                        , "*** " ++ show x ++ " /= " ++ show y
                        ]
     s1 <- makeEquivs sym mp s0
     mapM_ (addAsmp opts s1) ps
     return s1

addAssumptionsPost ::
  Opts -> (State,State) -> [(String, Prop Post)] -> IO State
addAssumptionsPost opts (s1,s2) ps =
  do let sym = optsSym opts
     s3 <- foldM (setPrePost sym s1) s2 ps
     s4 <- makeEquivs sym (foldr getEq emptyRepMap ps) s3
     mapM_ (addAsmp opts (s1,s4)) ps
     return s4


--------------------------------------------------------------------------------

-- | Allocate a memory region.
allocate :: Sym -> Area -> State -> IO (LLVMPtr Sym 64, State)
allocate sym area s =
  case areaMode area of
    RO -> do (base,p,m1) <- alloc Immutable
             m2     <- fillFresh sym base names m1
             return (p, s { stateMem = m2 })

    RW -> do (base,p,m1) <- alloc Mutable
             m2 <- fillFresh sym base names m1
             return (p, s { stateMem = m2 })

    WO -> do (_,p,m1) <- alloc Mutable
             return (p, s { stateMem = m1 })
  where

  alloc mut =
    do let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat (bytesToInteger (areaSize area))
       (base,mem) <- doMalloc sym HeapAlloc mut (areaName area) (stateMem s) sz
       ptr <- adjustPtr sym mem base (bytesToInteger (areaPtr area))
       return (base,ptr,mem)

  names :: [String]
  names = [ areaName area ++ "_byte_" ++ show i
          | i <- take (bytesToInt (areaSize area)) [ 0 :: Int .. ] ]

bytesToInt :: Bytes -> Int
bytesToInt = fromIntegral . bytesToInteger

fillFresh :: Sym -> LLVMPtr Sym 64 ->
                [String] -> MemImpl Sym -> IO (MemImpl Sym)
fillFresh sym p todo mem =
  case todo of
    [] -> return mem
    nm : more ->
      do let w = knownNat @1
         let ?ptrWidth = knownNat
         let ty        = ptrTy w
         let elS       = natValue w
         let lty       = bitvectorType (toBytes elS)
         val <- packMemValue sym lty ty =<< freshVal sym ty nm
         -- Here we use the write that ignore mutability.
         -- This is because we are writinging initialization code.
         mem1 <- storeConstRaw sym mem p lty val
         p1   <- adjustPtr sym mem1 p elS
         fillFresh sym p1 more mem1


-- | Make an allocation.  Used when verifying.
doAlloc :: Sym -> State -> Alloc -> IO State
doAlloc sym s (l := a) =
  do (p,s1) <- allocate sym a s
     setLoc l sym p s1

-- | Fill-in a memory area with fresh values.
-- This has no effect if the area is RO.
clobberArea ::
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Area -> IO (MemImpl Sym)
clobberArea sym mem p area =
  case areaMode area of
    RO -> return mem
    _  ->
      do base <- adjustPtr sym mem p (negate (bytesToInteger (areaPtr area)))
         let xs = take (bytesToInt (areaSize area))
                     [ areaName area ++ "_at_" ++ show i | i <- [ 0 :: Int .. ]]
         fillFresh sym base xs mem


-- | Lookup the value for an allocation in the existing state.
-- Used when overriding.
-- Returns the start and end of the allocation.
checkAlloc :: Sym -> State -> Alloc -> IO (LLVMPtr Sym 64, LLVMPtr Sym 64)
checkAlloc sym s (l := a) =
  do p1 <- getLoc l sym s
     let mem = stateMem s
     p2 <- adjustPtr sym mem p1 (negate (bytesToInteger (areaPtr a)))

     -- Make sure that we have a pointer and it is big enough.
     p3 <- adjustPtr sym mem p2 (bytesToInteger (areaSize a))
     return (p2,p3)


-- | Setup globals in a single read-only region (index 0).
setupGlobals ::
  Sym ->
  [(String,Integer,Unit,[Integer])] ->
  State ->
  IO (GlobalMap Sym X86_64, State)
setupGlobals sym gs s
  | null regions = return (Map.empty, s)

  | not (null overlaps) =
      fail $ unlines $ "Overlapping regions in global spec:"
                     : [ "*** " ++ x ++ " and " ++ y
                          | (x,y) <- overlaps ]

  | otherwise =
    do let size = case last regions of
                    (_,start,n) -> start + bytesToInteger n

       let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat size
       (p,mem) <- doMalloc sym GlobalAlloc Immutable "Globals" (stateMem s) sz
       mem1 <- foldM (writeGlob p) mem gs
       return (Map.singleton 0 p, s { stateMem = mem1 })
  where
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
         val  <- LLVMValInt z <$> bvLit sym w v
         let ?ptrWidth = knownNat
         mem1 <- storeConstRaw sym mem p lty val
         p1   <- adjustPtr sym mem1 p szI
         return (p1,mem1)

-- | Use a specification to verify a function.
-- Returns the initial state for the function, and a post-condition.
verifyMode ::
  Specification -> Opts -> IO (GlobalMap Sym X86_64, State, State -> IO ())
verifyMode spec opts =
  do let sym = optsSym opts
     s0 <- freshState sym
     s1 <- foldM (doAlloc sym) s0 $ sortBy cmpAlloc $ specAllocs spec
     (globs,s2) <- setupGlobals sym (specGlobsRO spec) s1
     s3 <- addAssumptions opts s2 (specPres spec)
     let post sF = mapM_ (doAssert opts (s3,sF)) (specPosts spec)
     return (globs, s3, post)

-- | Ensure that writable areas do not overlap with any other areas.
checkOverlaps :: Sym -> [((LLVMPtr Sym 64, LLVMPtr Sym 64), Area)] -> IO ()
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
overrideMode :: Specification -> Opts -> State -> IO State
overrideMode spec opts s =
  do let sym = optsSym opts
     let orderedAllocs = sortBy cmpAlloc (specAllocs spec)
     as <- mapM (checkAlloc sym s) orderedAllocs    -- check sizes
     checkOverlaps sym (zip as (map allocArea orderedAllocs)) -- check distinct
     mapM_ (doAssert opts s) (specPres spec)         -- assert pre-condition

     sNew0 <- freshState sym

     mem1 <- foldM (\s' (p,a) -> clobberArea sym s' p a) (stateMem s)
           $ reverse $ zip (map fst as) [ a | _ := a <- orderedAllocs ]

     let sNew1 = sNew0 { stateMem = mem1 }
     addAssumptionsPost opts (s,sNew1) (specPosts spec)


--------------------------------------------------------------------------------
-- Cryptol


-- | Lookup a cryptol term, and apply it to the given arguments,
-- returning the result.
cryTerm :: Opts -> String -> [Term] -> IO Term
cryTerm opts x xs =
  do t  <- lookupCry x (eTermEnv (optsCry opts))
     sc <- sawBackendSharedContext (optsSym opts)
     t1 <- scApplyAll sc t xs
     return t1

-- | Lookup a Crytpol type synonym, which should resolve to a constant.
cryConst :: CryptolEnv -> String -> IO Integer
cryConst env x =
  do let mp = ifTySyns (getAllIfaceDecls (eModuleEnv env))
     t <- lookupCry x mp
     case matchMaybe (aNat (tsDef t)) of
       Just n  -> return n
       Nothing -> fail (x ++ " is not a fixed constant type synonym.")

-- | Lookup a name in a map indexed by Cryptol names.
lookupCry :: String -> Map Name a -> IO a
lookupCry x mp =
  case x `lookupIn` mp of
    Left [] -> fail $ unlines $ ("Missing Cryptol name: " ++ show x)
                              : [ "*** " ++ ppName y | y <- Map.keys mp ]
    Left ys -> fail $ unlines ( "Ambiguous Cryptol name:"
                              : [ "*** " ++ ppName y | y <- ys ]
                              )
    Right a -> return a

  where ppName = show . runDoc alwaysQualify . pp




--------------------------------------------------------------------------------


adjustPtr ::
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Integer -> IO (LLVMPtr Sym 64)
adjustPtr sym mem ptr amt
  | amt == 0  = return ptr
  | otherwise =
    do let ?ptrWidth = knownNat
       doPtrAddOffset sym mem ptr =<< bvLit sym knownNat amt


