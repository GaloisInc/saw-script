{-# LANGUAGE ImplicitParams #-}
module Verifier.SAW.SharedTerm
  ( ParamType(..)
--  , Builtin(..)
  , TermF(..)
  , Ident, mkIdent
  , SharedTerm
  , SharedContext(..)
  , mkSharedContext
    -- ** Implicit versions of functions.
  , scApply
  , scApplyAll
  , scLambda
  , scFreshGlobal
  , scRecordSelect
--  , scFreshGlobal
--  , scLocalVar
--  , scBuiltin
  , scInteger
  , scTypeOf
--  , scView
  , scPrettyTerm
    -- ** Utilities.
--  , scGroundSignedType
--  , scGroundSignedValueFn
  , scViewAsBool
  , scViewAsNum
  ) where

import Control.Monad
import Data.Word
import Text.PrettyPrint.HughesPJ

import Verifier.SAW.TypedAST

{-
-- | Builtin operations.
data Builtin
  = BoolType
  | TrueCtor
  | FalseCtor
  | IteFn

  | EqFn -- Equality takes the type and the two arguments to compare.

  | TrueProp
  | AtomicProof
  | FalseProp
  | AssertFn

  | OrdClass
  | LeqFn
  | LtFn
  | GeqFn
  | GtFn
  | BoolOrdInstance

  | NumClass
  | NegOp
  | AddOp
  | SubOp
  | MulOp
  | DivOp
  | RemOp

  | BitsClass
  | NotFn
  | AndFn
  | OrFn
  | XorFn
  | ImpliesFn
  | ShlFn
  | ShrFn
  | BoolBitsInstance

  | IntegerType
  | IntegerOrdInstance
  | IntegerNumInstance
  | IntegerBitsInstance
  
  | ArrayType
  | ArrayOrdInstance
  | ArrayBitsInstance
  | GetFn
  | SetFn
  | GenerateFn
  
  | SignedType
  | SignedOrdInstance
  | SignedNumInstance
  | SignedBitsInstance

  | UnsignedType
  | UnsignedOrdInstance
  | UnsignedNumInstance
  | UnsignedBitsInstance

  | SignedToInteger
  | UnsignedToInteger
  | IntegerToSigned
  | IntegerToUnsigned

  | SignedToArray
  | UnsignedToArray
  | ArrayToSigned
  | ArrayToUnsigned

  | ResizeSigned
  | SignedToUnsigned
  | UnsignedToSigned
  | SignedUShr

  deriving (Eq, Ord)
-}

data SharedTerm s = SharedTerm Word64 (TermF (SharedTerm s))

instance Eq (SharedTerm s) where
  SharedTerm i _ == SharedTerm j _ = i == j

instance Ord (SharedTerm s) where
  compare (SharedTerm i _) (SharedTerm j _) = compare i j

-- | Operations that are defined, but not 

data SharedContext s = SharedContext
  { -- | Returns a lambda expression with the 
    scLambdaFn :: ParamType
               -> Ident
               -> (SharedTerm s -> IO (SharedTerm s))
               -> IO (SharedTerm s)
    -- | @scApplyFn f x@ returns the result of applying @x@ to a lambda function @x@.
  , scApplyFn         :: SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
    -- | Select an element out of a record.
  , scRecordSelectFn  :: SharedTerm s -> String -> IO (SharedTerm s)
  , scIntegerFn       :: Integer -> IO (SharedTerm s)
  , scTypeOfFn        :: SharedTerm s -> IO (SharedTerm s)
  , scPrettyTermDocFn :: SharedTerm s -> Doc
    -- Returns the globals in the current scope as a record of functions.
  --, scGetCurrentModuleFn :: IO (SharedTerm s)
  }

scLambda :: (?sc :: SharedContext s)
         => ParamType
         -> Ident
         -> (SharedTerm s -> IO (SharedTerm s))
         -> IO (SharedTerm s) 
scLambda = scLambdaFn ?sc

scApply :: (?sc :: SharedContext s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply = scApplyFn ?sc

scApplyAll :: (?sc :: SharedContext s) => SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scApplyAll = foldM scApply

scRecordSelect :: (?sc :: SharedContext s) => SharedTerm s -> String -> IO (SharedTerm s)
scRecordSelect = scRecordSelectFn ?sc

scInteger :: (?sc :: SharedContext s) => Integer -> IO (SharedTerm s)
scInteger = scIntegerFn ?sc

scTypeOf :: (?sc :: SharedContext s) => SharedTerm s -> IO (SharedTerm s)
scTypeOf = scTypeOfFn ?sc

-- Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: (?sc :: SharedContext s)
              => Ident -> SharedTerm s 
              -> IO (SharedTerm s)
scFreshGlobal = undefined

{-
-- | Returns signed type with the given bitwidth
scGroundSignedType :: (?sc :: SharedContext s) => Integer -> IO (SharedTerm s)
scGroundSignedType w = do
  s <- scBuiltin SignedType
  scApply s =<< scInteger w

-- Returns a function for creating signed values with specific bitwidths. 
scGroundSignedValueFn :: (?sc :: SharedContext s) => Integer -> IO (Integer -> IO (SharedTerm s))
scGroundSignedValueFn w = do
  f <- scBuiltin IntegerToSigned
  fw <- scApply f =<< scInteger w
  return $ scApply fw <=< scInteger
-}

-- | Returns term as a constant Boolean if it can be evaluated as one.
scViewAsBool :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Bool
scViewAsBool = undefined

-- | Returns term as an integer if it is an integer, signed bitvector, or unsigned
-- bitvector.
scViewAsNum :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Integer
scViewAsNum = undefined

scPrettyTerm :: (?sc :: SharedContext s) => SharedTerm s -> String
scPrettyTerm t = show (scPrettyTermDocFn ?sc t)

mkSharedContext :: IO (SharedContext s)
mkSharedContext = do
  return SharedContext {
       scApplyFn = undefined
     , scLambdaFn = undefined
--     , scGlobalFn = undefined              
--     , scFreshGlobalFn = undefined
--     , scGlobalsWithType = undefined
--     , scLocalVarFn = undefined
--     , scBuiltinFn = undefined
     , scIntegerFn = undefined
     , scTypeOfFn  = undefined
--     , scViewFn = undefined
     , scPrettyTermDocFn = undefined
     }