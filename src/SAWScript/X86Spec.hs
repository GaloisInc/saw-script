{-# Language DataKinds, TypeFamilies, TypeOperators, GADTs #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language TypeApplications #-}
{-# Language PatternSynonyms #-}
{-# Language UndecidableInstances #-}
{-# Language TypeSynonymInstances #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language FlexibleInstances #-}
{-# Language RankNTypes #-}
{-# Language RecordWildCards #-}
module SAWScript.X86Spec
  ( -- * Specifications
    FunSpec(..)
  , Spec

    -- ** Pre conditions
  , Pre
  , fresh
  , assume
  , freshRegs
  , freshGP
  , setupGPRegs, GPSetup(..), GPValue, gpUse
  , GetReg(..)
  , allocBytes
  , allocArray
  , Mutability(..)
  , WriteMem(..)

    -- ** Post conditions
  , Post
  , readMem
  , readArray
  , assert

    -- * Types
  , X86Type
  , AByte, AWord, ADWord, AQWord, AVec, APtr, ABool
  , ABits2, ABits3, ABigFloat
  , X86(..)
  , Infer(..)
  , MemType
  , SizeOf(..)
  , Bytes
  , toBytes
  , bytesToInteger

    -- * Values
  , Value
  , SAW(..), showTerm
  , Literal(..), literal
  , SameVal(..)
  , expectSame
  , preserveGP
  , ptrAdd
  , (.*)

    -- * Registers
  , IP(..)
  , GPReg(..), GPRegUse(..)
  , VecReg(..)
  , FPReg(..)

  , Flag(..)
  , X87Status(..)
  , X87Top(..)
  , X87Tag(..)

  , RegAssign(..), GPRegVal(..)

    -- * Cryptol specs
  , cryTerm

    -- * Misc
  , debug
  , ppVal

  ) where

import qualified Data.Vector as Vector

import Lang.Crucible.Solver.Interface (falsePred, isEq, printSymExpr)
import Lang.Crucible.LLVM.MemModel.Pointer (ptrEq)
import Lang.Crucible.LLVM.MemModel.Generic(ppPtr)

import Verifier.SAW.Term.Pretty(showTerm)

import SAWScript.X86Spec.Types
import SAWScript.X86Spec.Registers
import SAWScript.X86Spec.Monad
import SAWScript.X86Spec.Fresh
import SAWScript.X86Spec.SAW
import SAWScript.X86Spec.Literal
import SAWScript.X86Spec.Memory





debug :: String -> Spec p ()
debug x = io (putStrLn x)

ppValAt :: X86 t -> Value t -> String
ppValAt ty (Value v) =
  case ty of
    Byte      -> show (ppPtr v)
    Word      -> show (ppPtr v)
    DWord     -> show (ppPtr v)
    QWord     -> show (ppPtr v)
    Vec       -> show (ppPtr v)
    Ptr       -> show (ppPtr v)
    Bits2     -> show (ppPtr v)
    Bits3     -> show (ppPtr v)
    BigFloat  -> show (ppPtr v)
    Bool      -> show (printSymExpr v)

ppVal :: Infer t => Value t -> String
ppVal = ppValAt infer

-- | Assert that two values are the same.
expectSame :: (Infer t) =>
  String {- ^ A label to use if the assertion fails" -} ->
  Value t -> Value t -> Spec Post ()
expectSame s x y =
  do ok <- sameVal x y
     assert ok $ unlines [ s ++ " values are not the same:"
                         , "*** Expected: " ++ ppVal x
                         , "*** Actual  : " ++ ppVal y
                         ]

-- | Assert that a given general purpose register is preserved.
preserveGP :: RegAssign {- ^ Initial register assginment -} ->
              GPReg     {- ^ Register to preserve -} ->
              Spec Post ()
preserveGP r g =
  case valGPReg r g of
    GPBits oldV -> expectSame (show g) oldV =<< getReg (g,AsBits)
    GPPtr  oldV -> expectSame (show g) oldV =<< getReg (g,AsPtr)



class SameVal t where
  sameVal :: t -> t -> Spec p (Value ABool)

sameValAt :: X86 t -> Value t -> Value t -> Spec p (Value ABool)
sameValAt t (Value x) (Value y) =
  withSym $ \sym ->
    Value <$> (
    let w = bitSize t
    in case t of
         Byte      -> ptrEq sym w x y
         Word      -> ptrEq sym w x y
         DWord     -> ptrEq sym w x y
         QWord     -> ptrEq sym w x y
         Vec       -> ptrEq sym w x y
         Ptr       -> ptrEq sym w x y
         Bits2     -> ptrEq sym w x y
         Bits3     -> ptrEq sym w x y
         BigFloat  -> ptrEq sym w x y
         Bool      -> isEq sym x y)


instance Infer t => SameVal (Value t) where
  sameVal = sameValAt infer

instance SameVal GPRegVal where
  sameVal x y =
    case (x,y) of
      (GPBits a, GPBits b) -> sameVal a b
      (GPPtr a, GPPtr b)   -> sameVal a b
      _                    -> withSym $ \sym -> return (Value (falsePred sym))


{- | A specifiction for a function.
The outer, "Pre", computiation sets up the initial state of the
computation (i.e., the pre-condition for the function).
As a result, we return the inital register assignemtn,
and the post-condition for the function). -}
data FunSpec = FunSpec
  { spec     :: Spec Pre (RegAssign, Spec Post ())
  , cryDecls :: Maybe FilePath
  }



-- | Generate fresh values for all general purpose registers.
setupGPRegs ::
  (GPReg -> GPSetup) ->
  {- ^ Specifies how to initialize the given GP register -}
  Spec Pre (GPReg -> GPRegVal)
setupGPRegs ty =
  do vs <- Vector.fromList <$> mapM mk elemList
     return (\x -> vs Vector.! fromEnum x)
  where
  mk r = case ty r of
           GPFresh AsBits -> GPBits <$> fresh infer (show r)
           GPFresh AsPtr  -> GPPtr  <$> fresh infer (show r)
           GPUse x        -> return x

-- | A boolean tag to classify the use of a register.
data GPSetup = forall t. GPFresh (GPRegUse t)
             | GPUse GPRegVal


-- | Use the given value to initalize a general purpose register
gpUse :: GPValue t => Value t -> GPSetup
gpUse = GPUse . gpValue



