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
  , getRegs
  , InPre(..)
  , isPtr
  , assume
  , assert
  , getSharedContext
  , withSharedContext
  , cryTerm
  , PreExtra(..)
  ) where

import Control.Monad(liftM,ap)
import           Data.Map ( Map )
import qualified Data.Map as Map

import Data.Parameterized.Context(Assignment)

import Lang.Crucible.LLVM.DataLayout(EndianForm(LittleEndian))
import Lang.Crucible.Simulator.RegValue(RegValue,RegValue')
import Lang.Crucible.Simulator.SimError(SimErrorReason(..))
import Lang.Crucible.Solver.Interface
  (natLit,notPred,addAssertion,addAssumption, natEq)
import Lang.Crucible.Solver.SAWCoreBackend(sawBackendSharedContext)
import Lang.Crucible.LLVM.MemModel ( Mem, emptyMem, LLVMPointerType)
import Lang.Crucible.LLVM.MemModel.Pointer( pattern LLVMPointer )
import Lang.Crucible.LLVM.MemModel.Generic(ppPtr)

import Verifier.SAW.SharedTerm(Term,SharedContext,scApplyAll)

import Verifier.SAW.CryptolEnv(initCryptolEnv,loadCryptolModule,CryptolEnv(..))

import Cryptol.ModuleSystem.Name(nameIdent)
import Cryptol.Utils.Ident(unpackIdent)

import Data.Macaw.Symbolic.CrucGen(MacawCrucibleRegTypes)
import Data.Macaw.X86.ArchTypes(X86_64)


import SAWScript.X86Spec.Types

-- | Is this a pre- or post-condition specificiation.
data {- kind -} SpecType = Pre | Post

-- | We are specifying a pre-condition.
type Pre  = 'Pre

-- | We are specifying a post-condition.
type Post = 'Post


-- | A monad for definingin specifications.
newtype Spec (p :: SpecType) a =
  Spec ((Sym, Map String Term) ->
        RR p ->
        RegValue Sym Mem -> IO (a, RegValue Sym Mem))

-- | Interanl state to be passed from the pre-spec to the post-spec
data PreExtra = PreExtra { theMem :: RegValue Sym Mem
                         , cryTerms :: Map String Term
                         }

-- | Execute a pre-condition specification.
runPreSpec ::
  Sym ->
  Maybe FilePath {- ^ Optional file, containing Cryptol declarations -} ->
  Spec Pre a -> IO (a, PreExtra)
runPreSpec sym mb (Spec f) =
  do cs <- loadCry sym mb
     (a,m) <- f (sym,cs) () =<< emptyMem LittleEndian
     return (a, PreExtra { theMem = m, cryTerms = cs })

-- | Load a file with Cryptol decls.
loadCry :: Sym -> Maybe FilePath -> IO (Map String Term)
loadCry sym mb =
  case mb of
    Nothing -> return Map.empty
    Just file ->
      do ctx <- sawBackendSharedContext sym
         env <- initCryptolEnv ctx
         (_,env1) <- loadCryptolModule ctx env file
         let nameText = unpackIdent . nameIdent
         let cvt (x,v) = (nameText x, v)
         return (Map.fromList $ map cvt $ Map.toList $ eTermEnv env1)

-- | Execute a post-condition specification.
runPostSpec ::
  Sym ->
  Map String Term ->
  Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64) ->
  RegValue Sym Mem ->
  Spec Post () ->
  IO ()
runPostSpec sym cry rs mem (Spec f) = fst <$> f (sym, cry) rs mem

type family RR (x :: SpecType) where
  RR Pre = ()
  RR Post = Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64)

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
  case Map.lookup x cs of
    Nothing -> fail ("Missing Cryptol term: " ++ show x)
    Just t  -> do sc <- sawBackendSharedContext sym
                  t1 <- scApplyAll sc t xs
                  return (t1,s))

updMem :: (Sym -> RegValue Sym Mem -> IO (a, RegValue Sym Mem)) -> Spec Pre a
updMem f = Spec (\r _ s -> f (fst r) s)

updMem_ :: (Sym -> RegValue Sym Mem -> IO (RegValue Sym Mem)) -> Spec Pre ()
updMem_ f = updMem (\sym mem -> do mem1 <- f sym mem
                                   return ((),mem1))

withMem :: (Sym -> RegValue Sym Mem -> IO a) -> Spec p a
withMem f = Spec (\r _ s -> f (fst r) s >>= \a -> return (a,s))

getRegs :: Spec Post (Assignment (RegValue' Sym) (MacawCrucibleRegTypes X86_64))
getRegs = Spec (\_ r s -> return (r,s))

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
     io $ if pre
             then addAssumption sym ok
             else addAssertion sym ok (AssertFailureSimError msg)
  where
  msg' | yes       = "Expected a pointer, but encounterd a bit value."
       | otherwise = "Expected a bit value, but encounterd a pointer."

  msg = unlines [ msg', show (ppPtr pt) ]

-- The input should be a boolean SAW Core term.
assume :: Value ABool {- ^ Boolean assumption -} -> Spec Pre ()
assume (Value p) =
  do sym <- getSym
     io $ addAssumption sym p

-- | Add an assertion to the post-condition.
assert ::
  Value ABool {- ^ Boolean assertion, should be true -} ->
  String     {- ^ A message to show if the assrtion fails -} ->
  Spec Post ()
assert (Value p) msg =
  withSym $ \sym -> addAssertion sym p (AssertFailureSimError msg)




