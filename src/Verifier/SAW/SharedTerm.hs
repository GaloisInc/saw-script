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
  , mkUninterpretedSharedContext
  ) where

import Control.Monad
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word
import Text.PrettyPrint.HughesPJ

import Verifier.SAW.TypedAST

type TermIndex = Word64

data SharedTerm s = SharedTerm TermIndex (TermF (SharedTerm s))

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
  , scMkRecordFn      :: Map String (SharedTerm s) -> IO (SharedTerm s)
    -- | Select an element out of a record.
  , scRecordSelectFn  :: SharedTerm s -> FieldName -> IO (SharedTerm s)
  , scIntegerFn       :: Integer -> IO (SharedTerm s)
  , scTypeOfFn        :: SharedTerm s -> IO (SharedTerm s)
  , scPrettyTermDocFn :: SharedTerm s -> Doc
  , scLoadModule      :: Module -> IO (Map String (SharedTerm s))
    -- Returns the globals in the current scope as a record of functions.
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

scRecordSelect :: (?sc :: SharedContext s) => SharedTerm s -> FieldName -> IO (SharedTerm s)
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

-- 
data AppCache s = AC { acBindings :: !(Map (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !Word64
                     }

emptyAppCache :: AppCache s
emptyAppCache = AC Map.empty 0

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: IORef (AppCache s) -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a = do
  s <- readIORef r
  case Map.lookup a (acBindings s) of
    Just t -> return t
    Nothing -> do
      let t = SharedTerm (acNextIdx s) a
      writeIORef r $! s { acBindings = Map.insert a t (acBindings s)
                        , acNextIdx = acNextIdx s + 1
                        }
      return t

mkUninterpretedSharedContext :: IO (SharedContext s)
mkUninterpretedSharedContext = do
  cr <- newIORef emptyAppCache
  return SharedContext {
       scApplyFn = \f x -> getTerm cr (App f x)         
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
     , scMkRecordFn = undefined
     , scRecordSelectFn = undefined
     , scLoadModule = undefined
     }

mkSharedContext :: Module -> IO (SharedContext s, Map String (SharedTerm s))
mkSharedContext = undefined
