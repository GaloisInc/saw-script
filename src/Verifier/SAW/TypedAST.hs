module Verifier.SAW.TypedAST
 ( Ident
 , Un.ParamType(..)
 , Builtin(..)
 , LambdaVar
 , TermF(..)
 , Term(..)
 ) where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import Verifier.SAW.Position
import qualified Verifier.SAW.UntypedAST as Un


type Ident = String

type ParamType = Un.ParamType

data Builtin
  = TypeType

  | BoolType
  | TrueCtor
  | FalseCtor
  | IteFn
  | AssertFn
  | TrueProp
  | AtomicProof
  | FalseProp

  | EqClass
  | EqFn
  | BoolEqInstance

  | OrdClass
  | LeqFn
  | LtFn
  | GeqFn
  | GtFn
  | BoolOrdInstance

  | NumClass
  | NegFn
  | AddFn
  | SubFn
  | MulFn
  | DivFn
  | RemFn

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
  | IntegerEqInstance
  | IntegerOrdInstance
  | IntegerNumInstance
  | IntegerBitsInstance
  
  | ArrayType
  | ArrayEqInstance
  | ArrayOrdInstance
  | ArrayBitsInstance
  | GetFn
  | SetFn
  | GenerateFn
  
  | SignedType
  | SignedEqInstance
  | SignedOrdInstance
  | SignedNumInstance
  | SignedBitsInstance

  | UnsignedType
  | UnsignedEqInstance
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
  deriving (Eq, Ord)

type LambdaVar e = (Un.ParamType, Ident, e)

-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

data TermF e
  = BuiltinLit Builtin
  | IntegerLit Integer
  | LocalVar Integer   -- ^ Local variables are referenced by deBrujin index.
  | GlobalVar Integer  -- ^ Global variables are referenced by deBrujin level.
  | App e e
  | Lambda (LambdaVar e) e
  | Tuple Integer
  | Record (Map String e)
  | FieldOf e String 
  deriving (Eq,Ord)

data Term = Term Pos (TermF Term)

data Eqn = Eqn { eqnArgs :: [Term], eqnRhs :: Term }

data Def = Def { defPos :: Pos
               , defIdent :: Ident
               , defType :: Term
               , defEqs :: [Eqn]
               }

data Module = Module {
         moduleDefs :: Map Ident Def 
       }

{-
Experiments:

Can I get an untype map from identifiers to type and equations?


Things that need to happen:

* Identify bound variables with their corresponding lambda expression (via deBrujin indices).

2. Validate that type 

TODO: Read Pierce chapter on type inference.


-}

type UnEq = ([Un.Expr],Un.Expr)

data SymDef = SD Ident Un.Expr [UnEq]

data TCState = TCS { symTypes :: Map Ident Un.Expr
                   , tcErrors :: [(Pos,String)]
                   }

data TC a = TC { unTC :: State TCState a }

addGlobalTypes :: [Un.Decl] -> TC ()
addGlobalTypes (Un.TypeDecl _ _:l) = do
  --TODO: Add types
  addGlobalTypes l
addGlobalTypes (Un.DataDecl pi tp ctors:l) = do
  --TODO: Add these
  addGlobalTypes l
addGlobalTypes (Un.TermDef{}:l) = addGlobalTypes l