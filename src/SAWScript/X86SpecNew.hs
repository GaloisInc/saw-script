{-# Language GADTs, KindSignatures, DataKinds, ImplicitParams #-}
{-# Language PatternSynonyms, TypeFamilies, TypeSynonymInstances #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language ExistentialQuantification #-}
{-# Language Rank2Types #-}
{-# Language FlexibleContexts #-}
{-# Language ScopedTypeVariables #-}
{-# Language ConstraintKinds #-}
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

  -- * Cryptol
  , CryArg(..)
  , cryPre
  , cryCur
  , cryArrPre
  , cryArrCur
  , cryTerm
  , cryConst
  ) where

import GHC.TypeLits(KnownNat)
import GHC.Natural(Natural)
import Data.Kind(Type)
import Control.Monad(foldM)
import Data.List(sortBy,intercalate)
import Data.Maybe(catMaybes)
import Data.Map (Map)
import Data.Proxy(Proxy(..))
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
    (ptrEq, LLVMPtr, ppPtr, llvmPointerView, projectLLVM_bv, llvmPointer_bv)
import Lang.Crucible.LLVM.MemModel.Type(bitvectorType)
import qualified Lang.Crucible.LLVM.MemModel.Type as LLVM
import Lang.Crucible.LLVM.Bytes(Bytes,bytesToInteger,toBytes)
import Lang.Crucible.LLVM.MemModel.Generic
    (AllocType(HeapAlloc,GlobalAlloc), Mutability(..))
import Lang.Crucible.Simulator.RegValue(RegValue'(..),RegValue)
import Lang.Crucible.Simulator.SimError(SimErrorReason(AssertFailureSimError))
import Lang.Crucible.Solver.Interface
          (bvLit,isEq, Pred, addAssumption, addAssertion, notPred, orPred
          , bvUle, truePred, falsePred, natLit, asNat )
import Lang.Crucible.Solver.SAWCoreBackend
  (bindSAWTerm,sawBackendSharedContext,toSC)
import Lang.Crucible.Types
  (TypeRepr(..),BaseTypeRepr(..),BaseToType,CrucibleType, BoolType )

import Verifier.SAW.SharedTerm(Term,scApplyAll,scVector,scBitvector)
import Data.Macaw.Symbolic(freshValue,GlobalMap)
import Data.Macaw.Symbolic.PersistentState(ToCrucibleType)
import Data.Macaw.Symbolic(Regs, macawAssignToCrucM, CallHandler )
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
  { specAllocs  :: ![Alloc]
  , specPres    :: ![(String, Prop Pre)]
  , specPosts   :: ![(String, Prop Post)]

  , specGlobsRO :: ![ (String, Integer, Unit, [ Integer ]) ]
    -- ^ Read only globals.

  , specCalls   :: ![ (String, Integer, Specification) ]
    -- ^ Specifications for the functions we call.
    -- The integer is the absolute address of the function.
  }

data Unit = Bytes | Words | DWords | QWords | V128s | V256s deriving Show


data Opts = Opts
  { optsSym :: Sym
  , optsCry :: CryptolEnv
  }

(*.) :: Integer -> Unit -> Bytes
n *. u = toBytes (fromIntegral n * bs)
  where bs = unitByteSize u natValue :: Integer

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
  , areaSize :: Bytes

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
                  , areaSize = u *. s
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

arrLoc ::
  (1 <= w) =>
  Loc (LLVMPointerType 64) {- ^ Start of array -} ->
  NatRepr w                {- ^ Size of value in bytes -} ->
  Integer                  {- ^ Element number -} ->
  Loc (LLVMPointerType (8*w))
arrLoc ptr byteW i = InMem byteW ptr (i * natValue byteW)



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
  -- An opaque SAW term; WARNING: type is unchecked

  CryFun ::
    (1 <= w) => NatRepr w -> String -> [CryArg p] -> V p (LLVMPointerType w)
  -- An opaque Cryptol term term; WARNING: type is unchecked

  IntLit :: (1 <= w) => NatRepr w -> Integer -> V p (LLVMPointerType w)
  -- A literal value

  BoolLit :: Bool -> V p BoolType
  -- A literal value


  Loc    :: Loc t -> V p t
  -- Read the value at the location
  -- in the *current* state.

  PreLoc :: Loc t -> V Post t
  -- Read the value in the pre-condition.

  PreAddPtr ::
    Loc (LLVMPointerType 64) -> Integer -> Unit -> V Post (LLVMPointerType 64)
  -- Add a constant to a pointer from a location in the pre-condition.


instance Show (V p t) where
  show val =
    case val of
      SAW ty _  -> pars ("SAW ... : " ++ show ty)
      CryFun w f xs -> pars (f ++ " " ++ unwords (map show xs) ++ sh w)
      IntLit w x -> pars (show x ++ sh w)
      BoolLit x -> show x
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



data CryArg p = forall w. Cry (V p (LLVMPointerType w))
              | forall w. CryArr (NatRepr w) [V p (LLVMPointerType w)]

instance Show (CryArg p) where
  show x =
    case x of
      Cry v -> show v
      CryArr _ vs -> "[" ++ intercalate "," (map show vs) ++ "]"

cryPre :: Loc (LLVMPointerType w) -> CryArg Post
cryPre l = Cry (PreLoc l)

cryCur :: Loc (LLVMPointerType w) -> CryArg p
cryCur l = Cry (Loc l)

cryArr ::
  (forall t. Loc t -> V p t) {- ^ "Loc" or "PreLoc" -} ->
  Loc (LLVMPointerType 64)   {- ^ Start address of array -} ->
  Integer                    {- ^ Number of elements to read -} ->
  Unit                       {- ^ Size of array elements -} ->
  CryArg p
cryArr toV ptr n u =
  unitByteSize u $ \w ->
    CryArr (natMultiply (knownNat @8) w)
      [ toV (arrLoc ptr w i) | i <- [ 0 .. n - 1 ] ]


cryArrPre :: Loc (LLVMPointerType 64) -> Integer -> Unit -> CryArg Post
cryArrPre = cryArr PreLoc

cryArrCur :: Loc (LLVMPointerType 64) -> Integer -> Unit -> CryArg p
cryArrCur = cryArr Loc


data Prop :: SpecType -> Type where
  Same    :: TypeRepr t -> V p t -> V p t -> Prop p
  CryProp :: String -> [ CryArg p ] -> Prop p
  SAWProp :: Term -> Prop p

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


freshVal ::
  Sym -> TypeRepr t -> Bool {- ptrOK ?-}-> String -> IO (RegValue Sym t)
freshVal sym t ptrOk nm =
  case t of
    BoolRepr -> freshValue sym nm ptr M.BoolTypeRepr
    LLVMPointerRepr w ->
      freshValue sym nm ptr (M.BVTypeRepr w)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)

  where
  ptr = if ptrOk then Just (knownNat @64) else Nothing


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
  eval :: V p t -> Opts -> S p -> IO (RegValue Sym t)
  curState :: f p -> S p -> State
  setCurState :: f p -> State -> S p -> S p

evIntLit :: (1 <= w) => Sym -> NatRepr w -> Integer -> IO (LLVMPtr Sym w)
evIntLit sym w n = llvmPointer_bv sym =<< bvLit sym w n

evBoolLit :: Sym -> Bool -> IO (RegValue Sym BoolType)
evBoolLit sym b = return (if b then truePred sym else falsePred sym)

instance Eval Pre where
  type S Pre = State
  eval val =
    case val of
      SAW ty t       -> \opts _ -> bindSAWTerm (optsSym opts) ty t
      CryFun w f xs  -> \opts s -> evalCryFun opts s w f xs
      IntLit w n     -> \opts _ -> evIntLit (optsSym opts) w n
      BoolLit b      -> \opts _ -> evBoolLit (optsSym opts) b
      Loc l          -> \opts s -> getLoc l (optsSym opts) s
  curState _ s = s
  setCurState _ s _ = s

instance Eval Post where
  type S Post = (State,State)
  eval val =
    case val of
      SAW ty t        -> \opts _         -> bindSAWTerm (optsSym opts) ty t
      CryFun w f xs   -> \opts s         -> evalCryFun opts s w f xs
      IntLit w n      -> \opts _         -> evIntLit (optsSym opts) w n
      BoolLit b       -> \opts _         -> evBoolLit (optsSym opts) b
      Loc l           -> \opts (_,post)  -> getLoc l (optsSym opts) post
      PreLoc l        -> \opts (pre,_)   -> getLoc l (optsSym opts) pre
      PreAddPtr l i u -> \opts (pre,_) ->
        do let sym = optsSym opts
           ptr <- getLoc l sym pre
           adjustPtr sym (stateMem pre) ptr (bytesToInteger (i *. u))

  curState _ (_,s) = s
  setCurState _ s (s1,_) = (s1,s)

evalCry :: Eval p => Opts -> CryArg p -> S p -> IO Term
evalCry opts cry s =
  case cry of
    Cry v -> toSC sym =<< projectLLVM_bv sym =<< eval v opts s
    CryArr w cs ->
      do ts <- mapM (\x -> evalCry opts (Cry x) s) cs
         sc <- sawBackendSharedContext sym
         ty <- scBitvector sc (fromIntegral (natValue w))
         scVector sc ty ts
  where
  sym = optsSym opts

evalCryFunGen ::
  Eval p =>
  Opts ->
  S p ->
  BaseTypeRepr t ->
  String ->
  [CryArg p] ->
  IO (RegValue Sym (BaseToType t))
evalCryFunGen opts s ty f xs =
  do ts <- mapM (\x -> evalCry opts x s) xs
     bindSAWTerm (optsSym opts) ty =<< cryTerm opts f ts

evalCryFun ::
  (1 <= w, Eval p) =>
  Opts ->
  S p ->
  NatRepr w ->
  String ->
  [CryArg p] ->
  IO (LLVMPtr Sym w)
evalCryFun opts s w f xs =
  llvmPointer_bv (optsSym opts) =<< evalCryFunGen opts s (BaseBVRepr w) f xs

evalProp :: Eval p => Opts -> Prop p -> S p -> IO (Pred Sym)
evalProp opts p s =
  case p of
    Same t x y ->
      do v1 <- eval x opts s
         v2 <- eval y opts s
         evalSame sym t v1 v2

    CryProp f xs -> evalCryFunGen opts s BaseBoolRepr f xs

    SAWProp t -> bindSAWTerm sym BaseBoolRepr t
  where
  sym = optsSym opts

evalSame ::
  Sym -> TypeRepr t -> RegValue Sym t -> RegValue Sym t -> IO (Pred Sym)
evalSame sym t v1 v2 =
  case t of
    BoolRepr          -> isEq sym v1 v2
    LLVMPointerRepr w -> ptrEq sym w v1 v2
    it -> fail ("[evalProp] Unexpected value repr: " ++ show it)



-- | Add an assertion to the post-condition.
doAssert :: Eval p => Opts -> S p -> (String, Prop p) -> IO ()
doAssert opts s (msg,p) =
  do pr <- evalProp opts p s
     addAssertion (optsSym opts) pr (AssertFailureSimError msg)


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

makeEquiv :: forall p. Eval p => Opts -> S p -> Pair Rep (Equiv p) -> IO (S p)
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

     let same a = addAssumption sym =<< evalSame sym t v a

     mapM_ same rest

     return (setCurState pName s1 s)


makeEquivs :: Eval p => Opts -> RepMap p -> S p -> IO (S p)
makeEquivs opts mp s = foldM (makeEquiv opts) s (MapF.toList (repBy mp))



addAsmp :: Eval p => Opts -> S p -> (String,Prop p) -> IO ()
addAsmp opts s (_,p) =
  case p of
    Same _ (Loc _) _ -> return ()
    Same _ _ (Loc _) -> return ()
    _ -> addAssumption (optsSym opts) =<< evalProp opts p s


addAssumptions ::
  forall p. Eval p => Opts -> S p -> [(String, Prop p)] -> IO State
addAssumptions opts s0 ps =
  do let mp = foldr getEq emptyRepMap ps
     s1 <- makeEquivs opts mp s0
     mapM_ (addAsmp opts s1) ps
     return (curState (Proxy :: Proxy p) s1)


--------------------------------------------------------------------------------

-- | Allocate a memory region.
allocate :: Sym -> Area -> State -> IO (LLVMPtr Sym 64, State)
allocate sym ar s =
  case areaMode ar of
    RO -> do (base,p,m1) <- alloc Immutable
             m2     <- fillFresh sym withPtrs base names m1
             return (p, s { stateMem = m2 })

    RW -> do (base,p,m1) <- alloc Mutable
             m2 <- fillFresh sym withPtrs base names m1
             return (p, s { stateMem = m2 })

    WO -> do (_,p,m1) <- alloc Mutable
             return (p, s { stateMem = m1 })
  where
  withPtrs = areaHasPointers ar

  alloc mut =
    do let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat (bytesToInteger (areaSize ar))
       (base,mem) <- doMalloc sym HeapAlloc mut (areaName ar) (stateMem s) sz
       ptr <- adjustPtr sym mem base (bytesToInteger (areaPtr ar))
       return (base,ptr,mem)

  names :: [String]
  names = [ areaName ar ++ "_byte_" ++ show i
          | i <- take (bytesToInt (areaSize ar)) [ 0 :: Int .. ] ]

bytesToInt :: Bytes -> Int
bytesToInt = fromIntegral . bytesToInteger

fillFresh :: Sym -> Bool -> LLVMPtr Sym 64 ->
                [String] -> MemImpl Sym -> IO (MemImpl Sym)
fillFresh sym ptrOk p todo mem =
  case todo of
    [] -> return mem
    nm : more ->
      do let w = knownNat @1
         let ?ptrWidth = knownNat
         let ty        = ptrTy w
         let elS       = natValue w
         let lty       = bitvectorType (toBytes elS)
         val <- packMemValue sym lty ty =<< freshVal sym ty ptrOk nm
         -- Here we use the write that ignore mutability.
         -- This is because we are writinging initialization code.
         mem1 <- storeConstRaw sym mem p lty val
         p1   <- adjustPtr sym mem1 p elS
         fillFresh sym ptrOk p1 more mem1


-- | Make an allocation.  Used when verifying.
doAlloc :: Sym -> State -> Alloc -> IO State
doAlloc sym s (l := a) =
  do (p,s1) <- allocate sym a s
     setLoc l sym p s1

-- | Fill-in a memory area with fresh values.
-- This has no effect if the area is RO.
clobberArea ::
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Area -> IO (MemImpl Sym)
clobberArea sym mem p ar =
  case areaMode ar of
    RO -> return mem
    _  ->
      do base <- adjustPtr sym mem p (negate (bytesToInteger (areaPtr ar)))
         let xs = take (bytesToInt (areaSize ar))
                     [ areaName ar ++ "_at_" ++ show i | i <- [ 0 :: Int .. ]]
         fillFresh sym (areaHasPointers ar) base xs mem


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
  Opts ->
  [(String,Integer,Unit,[Integer])] ->
  [(String,Integer,Specification)] ->
  State ->
  IO ((GlobalMap Sym X86_64,Overrides), State)
setupGlobals opts gs fs s
  | null regions && null fs = return ((Map.empty,Map.empty), s)

  | not (null overlaps) =
      fail $ unlines $ "Overlapping regions in global spec:"
                     : [ "*** " ++ x ++ " and " ++ y
                          | (x,y) <- overlaps ]

  | otherwise =
    do let endGlob = case last regions of
                       (_,start,n) -> start + bytesToInteger n
           size    = maximum (endGlob : fundAddrs)

       let ?ptrWidth = knownNat @64
       sz <- bvLit sym knownNat size
       (p,mem) <- doMalloc sym GlobalAlloc Immutable "Globals" (stateMem s) sz

       let Just base = asNat (fst (llvmPointerView p))

       mem1 <- foldM (writeGlob p) mem gs
       let gMap = Map.singleton 0 p

           handler _f sp sy (m,r) =
              do let st0 = State { stateRegs = r, stateMem = m }
                 st1 <- overrideMode sp opts { optsSym = sy } st0
                 return (stateMem st1, stateRegs st1)

           fMap = Map.fromList [ ((base,a), handler f sp) | (f,a,sp) <- fs ]

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
         val  <- LLVMValInt z <$> bvLit sym w v
         let ?ptrWidth = knownNat
         mem1 <- storeConstRaw sym mem p lty val
         p1   <- adjustPtr sym mem1 p szI
         return (p1,mem1)

debugPPReg ::
  (ToCrucibleType mt ~ LLVMPointerType w) =>
  X86Reg mt -> State -> IO ()
debugPPReg r s =
  do let Just (RV v) = lookupX86Reg r (stateRegs s)
     putStrLn (show r ++ " = " ++ show (ppPtr v))



type Overrides = Map (Natural,Integer) (Sym -> CallHandler Sym X86_64)

-- | Use a specification to verify a function.
-- Returns the initial state for the function, and a post-condition.
verifyMode ::
  Specification -> Opts -> IO ( ( GlobalMap Sym X86_64, Overrides )
                              , State, State -> IO ()
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
     do sc <- sawBackendSharedContext (optsSym opts)
        t1 <- scApplyAll sc t xs
        return t1

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

  where ppName = show . runDoc alwaysQualify . pp




--------------------------------------------------------------------------------


adjustPtr ::
  Sym -> MemImpl Sym -> LLVMPtr Sym 64 -> Integer -> IO (LLVMPtr Sym 64)
adjustPtr sym mem ptr amt
  | amt == 0  = return ptr
  | otherwise =
    do let ?ptrWidth = knownNat
       doPtrAddOffset sym mem ptr =<< bvLit sym knownNat amt


