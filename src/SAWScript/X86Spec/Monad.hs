{-# Language DataKinds #-}
{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}
{-# Language TypeSynonymInstances #-}
{-# Language PatternSynonyms #-}
module SAWScript.X86Spec.Monad
  ( SpecType, Pre, Post
  , Spec
  , runPreSpec, runPostSpec
  , io
  , getSym
  , withSym
  , updMem
  , updMem_
  , withMem
  , registerRegion
  , lookupReg
  , InPre(..)
  , isPtr
  , assume
  , assert
  , getSharedContext
  , withSharedContext
  , cryTerm
  , cryConst
  , PreExtra(..)
  -- , registerSymFuns
  -- , SymFunTerms(..)
  , lookupCry
  ) where

import Control.Monad(liftM,ap)
import           Data.Map ( Map )
import qualified Data.Map as Map

import Data.Parameterized.Context(Assignment)

import What4.Interface
  (natLit,notPred,natEq,getCurrentProgramLoc)

import SAWScript.CrucibleLLVM
  ( EndianForm(LittleEndian)
  , Mem, emptyMem, LLVMPointerType
  , pattern LLVMPointer, LLVMPtr, ppPtr
  )
import Lang.Crucible.Simulator.RegValue(RegValue,RegValue'(..))
import Lang.Crucible.Simulator.SimError(SimErrorReason(..), SimError(..))
import Lang.Crucible.Backend
  (addAssertion,addAssumption,AssumptionReason(..),LabeledPred(..))
import Lang.Crucible.Backend.SAWCore (sawBackendSharedContext)

import Verifier.SAW.SharedTerm(Term,SharedContext,scApplyAll)

import Verifier.SAW.CryptolEnv(CryptolEnv(..), lookupIn, getAllIfaceDecls)

import Cryptol.ModuleSystem.Name(Name)
import Cryptol.ModuleSystem.Interface(ifTySyns)
import Cryptol.TypeCheck.AST(TySyn(tsDef))
import Cryptol.TypeCheck.TypePat(aNat)
import Cryptol.Utils.PP(alwaysQualify,runDoc,pp)
import Cryptol.Utils.Patterns(matchMaybe)

import Data.Macaw.Memory(RegionIndex)
import Data.Macaw.Symbolic(MacawCrucibleRegTypes, ToCrucibleType)
import Data.Macaw.X86.ArchTypes(X86_64)
import Data.Macaw.X86.Symbolic(lookupX86Reg)
import Data.Macaw.X86.X86Reg(X86Reg)


import SAWScript.X86Spec.Types

-- | Is this a pre- or post-condition specificiation.
data {- kind -} SpecType = Pre | Post

-- | We are specifying a pre-condition.
type Pre  = 'Pre

-- | We are specifying a post-condition.
type Post = 'Post


-- | A monad for definingin specifications.
newtype Spec (p :: SpecType) a =
  Spec ((Sym, CryptolEnv) ->
        RR p ->
        (RegValue Sym Mem, SS p) -> IO (a, (RegValue Sym Mem, SS p)))

-- | Interanl state to be passed from the pre-spec to the post-spec
data PreExtra = PreExtra { theMem     :: RegValue Sym Mem
                         , theRegions :: Map RegionIndex (LLVMPtr Sym 64)
                         }

-- | Execute a pre-condition specification.
runPreSpec ::
  Sym ->
  CryptolEnv  {- ^ Contains Cryptol declarations we may use -} ->
  Spec Pre a -> IO (a, PreExtra)
runPreSpec sym cs (Spec f) =
  do m0 <- emptyMem LittleEndian
     (a,(m,rs)) <- f (sym,cs) () (m0, Map.empty)
     return (a, PreExtra { theMem = m, theRegions = rs })



-- | Execute a post-condition specification.
runPostSpec ::
  Sym ->
  CryptolEnv ->
  Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64) ->
  RegValue Sym Mem ->
  Spec Post () ->
  IO ()
runPostSpec sym cry rs mem (Spec f) = fst <$> f (sym, cry) rs (mem, ())

type family RR (x :: SpecType) where
  RR Pre = ()
  RR Post = Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)

type family SS (x :: SpecType) where
  SS Pre = Map RegionIndex (LLVMPtr Sym 64)
  SS Post = ()

instance Functor (Spec p) where fmap = liftM

instance Applicative (Spec p) where
  pure a = Spec (\_ _ m -> return (a,m))
  (<*>) = ap

instance Monad (Spec p) where
  Spec m >>= k = Spec (\r x s -> do (a, s1) <- m r x s
                                    let Spec m1 = k a
                                    m1 r x s1)

io :: IO a -> Spec p a
io m = Spec (\_ _ s -> do a <- m
                          return (a,s))

getSym :: Spec p Sym
getSym = Spec (\(r,_) _ s -> return (r,s))

withSym :: (Sym -> IO a) -> Spec p a
withSym f =
  do s <- getSym
     io (f s)

getSharedContext :: Spec p SharedContext
getSharedContext = withSym sawBackendSharedContext

withSharedContext :: (SharedContext -> IO a) -> Spec p a
withSharedContext f =
  do s <- getSharedContext
     io (f s)

-- | Lookup a cryptol term, and apply it to the given arguments,
-- returning the result.
cryTerm :: String -> [Term] -> Spec p Term
cryTerm x xs = Spec (\(sym,cs) _ s ->
  do t <- lookupCry x (eTermEnv cs)
     sc <- sawBackendSharedContext sym
     t1 <- scApplyAll sc t xs
     return (t1,s))

-- | Lookup a Crytpol type synonym, which should resolve to a constant.
cryConst :: String -> Spec p Integer
cryConst x = Spec (\(_,cs) _ s ->
  do let mp = ifTySyns (getAllIfaceDecls (eModuleEnv cs))
     t <- lookupCry x mp
     case matchMaybe (aNat (tsDef t)) of
       Just n  -> return (n,s)
       Nothing -> fail (x ++ " is not a fixed constant type synonym.")
  )

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


updMem :: (Sym -> RegValue Sym Mem -> IO (a, RegValue Sym Mem)) -> Spec Pre a
updMem f = Spec (\r _ (s1,s2) -> do (a,s1') <- f (fst r) s1
                                    return (a, (s1',s2)))

updMem_ :: (Sym -> RegValue Sym Mem -> IO (RegValue Sym Mem)) -> Spec Pre ()
updMem_ f = updMem (\sym mem -> do mem1 <- f sym mem
                                   return ((),mem1))

withMem :: (Sym -> RegValue Sym Mem -> IO a) -> Spec p a
withMem f = Spec (\r _ s -> f (fst r) (fst s) >>= \a -> return (a,s))

lookupReg ::
  (ToCrucibleType t ~ Rep ty) => X86Reg t -> Spec Post (Value ty)
lookupReg r = Spec (\_ regs s ->
  case lookupX86Reg r regs of
    Nothing     -> fail ("Unknown register: " ++ show r)
    Just (RV v) -> return (Value v,s))

registerRegion :: RegionIndex -> Value APtr -> Spec Pre ()
registerRegion r (Value x) = Spec (\_ _ (s1,s2) ->
  if Map.member r s2
    then fail ("Multiple declarations for global region: " ++ show r)
    else return ((), (s1, Map.insert r x s2)))

class InPre p where
  inPre :: Spec p Bool

instance InPre Pre where
  inPre = return True

instance InPre Post where
  inPre = return False

-- | State if this value should be a pointer.
-- In pre-condition we assume it, in post-conditions we assert it.
isPtr :: (Rep t ~ LLVMPointerType 64, InPre p) =>
         Value t ->
         Bool ->
         Spec p ()
isPtr (Value pt@(LLVMPointer base _off)) yes =
  do sym <- getSym
     ok <- io $ do isBits <- natEq sym base =<< natLit sym 0
                   if yes then notPred sym isBits else return isBits

     pre <- inPre
     loc <- io $ getCurrentProgramLoc sym
     io $ if pre
             then addAssumption sym (LabeledPred ok (AssumptionReason loc "precondition"))
             else addAssertion sym (LabeledPred ok (SimError loc (AssertFailureSimError msg)))
  where
  msg' | yes       = "Expected a pointer, but encounterd a bit value."
       | otherwise = "Expected a bit value, but encounterd a pointer."

  msg = unlines [ msg', show (ppPtr pt) ]

-- The input should be a boolean SAW Core term.
assume :: Value ABool {- ^ Boolean assumption -} -> Spec Pre ()
assume (Value p) =
  do sym <- getSym
     loc <- io $ getCurrentProgramLoc sym
     io $ addAssumption sym (LabeledPred p (AssumptionReason loc "assumption"))

-- | Add an assertion to the post-condition.
assert ::
  Value ABool {- ^ Boolean assertion, should be true -} ->
  String     {- ^ A message to show if the assrtion fails -} ->
  Spec Post ()
assert (Value p) msg =
  do sym <- getSym
     loc <- io $ getCurrentProgramLoc sym
     io $ addAssertion sym (LabeledPred p (SimError loc (AssertFailureSimError msg)))


--------------------------------------------------------------------------------
-- Symbolic terms

{-
{- | The SAW core terms used to implement the given instructions.
During simulation, these instructions are threated as uninterpred
functions, but in the post conditions we use these intepretations.
For the types, plase have a look at "SymFuns" in "Data.Macaw.X86.Crucible"
from the "macaw-x86-symbolic" pacakge. -}
data SymFunTerms = SymFunTerms
  { termAesEnc ::
      SharedContext -> Term{-128-} -> Term{-128-} -> IO Term{-128-}

  , termAesEncLast ::
      SharedContext -> Term{-128-} -> Term{-128-} -> IO Term{-128-}

  , termClMul ::
      SharedContext -> Term{- 64-} -> Term{- 64-} -> IO Term{-128-}
  }

-- | Add interpretations for the symbolic functions.
registerSymFuns :: SymFunTerms -> Spec Pre ()
registerSymFuns defs = Spec $ \(sym,_) symFs st ->
  do let mk2 nm f = \sc xs -> case xs of
                                [a,b] -> f defs sc a b
                                _     -> fail (err nm xs)

     sawRegisterSymFunInterp sym (fnAesEnc symFs) $
        mk2 "aesenc" termAesEnc

     sawRegisterSymFunInterp sym (fnAesEncLast symFs) $
        mk2 "aesenclast" termAesEncLast

     sawRegisterSymFunInterp sym (fnClMul symFs) $
        mk2 "clmul" termClMul

     return ((),st)

  where
  err nm xs =
    unlines [ "Type error in call to " ++ show (nm::String) ++ ":"
            , "*** Expected: 2 arguments"
            , "*** Given:    " ++ show (length xs) ++ " arguments"
            ]



-}
