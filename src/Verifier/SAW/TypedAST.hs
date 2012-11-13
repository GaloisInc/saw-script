{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Verifier.SAW.TypedAST
 ( Un.Ident, Un.mkIdent
 , Un.ParamType(..)
 , Builtin(..)
 , LambdaVar
 , TermF(..)
 , Term(..)
 , PosPair(..)
 , SymDef(..)
 , GroupError(..)
 , groupDecls
 , TCError(..)
-- , tcDefs
 ) where

import Control.Applicative
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Word (Word64)

import Verifier.SAW.Position
import qualified Verifier.SAW.UntypedAST (Sort)
import qualified Verifier.SAW.UntypedAST as Un


type Ident = Un.Ident

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
  = IntLit Pos Integer
  | LocalVar Pos Integer   -- ^ Local variables are referenced by deBrujin index.
  | GlobalRef Pos Integer  -- ^ Global variables are referenced by deBrujin level.
  | Lambda (ParamType, PosPair Ident, e) e
  | App e e
  | Pi (ParamType, PosPair Ident, e) e
  | TupleValue Pos [e]
  | TupleType Pos [e]
  | RecordValue Pos (Map String e)
  | RecordSelector Pos (Map String e)
  | RecordType Pos (Map String e)
  | ArrayValue Pos [e]
  | Sort Pos Un.Sort
 deriving (Eq,Ord)

data Term = Term (TermF Term)

data SymDef t = SD { sdIdent :: PosPair Ident
                   , sdType  :: t
                   , sdDef   :: Maybe t
                   } deriving (Functor, Show)

instance Positioned (SymDef t) where
  pos sd = pos (sdIdent sd)

type Def = SymDef Term

data Module = Module {
         moduleDefs :: Map Ident (SymDef Term)
       }

{-
Experiments:

Can I get an untype map from identifiers to type and equations?


Things that need to happen:

* Identify bound variables with their corresponding lambda expression (via deBrujin indices).

2. Validate that type 

TODO: Read Pierce chapter on type inference.


-}

data GroupError
 = PrevDefined (PosPair Ident) -- ^ Identifier and old position.
 | NoSignature Ident -- ^ Identifier is missing signature.
 | DuplicateDef Ident Pos -- ^ Equation for defintion already appeared.
   -- ^ An internal limitation resulted in an error.
 | Limitation String
 deriving (Show)

groupDecls :: [Un.Decl] -> ([PosPair GroupError], Map Ident (SymDef Un.Expr))
groupDecls d = (reverse (gsErrors so), gsDefs so)
  where si = GS { gsDefs = Map.empty, gsErrors = [] }
        so = execState (collectGroups d) si

type UnEqn = (Pos, [Un.LambdaBinding Un.Expr], Un.Expr)

-- Extract equations for identifier an return them along with remaining equations.
gatherEqs :: Ident -> [Un.Decl] -> ([UnEqn], [Un.Decl])
gatherEqs i = go []
  where go eqs (Un.TermDef (PosPair p j) lhs rhs : decls)
          | i == j = go ((p,lhs,rhs):eqs) decls
        go eqs decls = (reverse eqs, decls)

-- Extract declarations from list of functions.
gatherManyEqs :: Set Ident -> [Un.Decl] -> (Map Ident [UnEqn], [Un.Decl])
gatherManyEqs s = go Map.empty
  where go m (Un.TermDef (PosPair p i) lhs rhs : decls)
          | Set.member i s = go (Map.insert i ((p,lhs,rhs):feqs) m) rest
              where (feqs, rest) = gatherEqs i decls
        go m decls = (m, decls)

data GroupState = GS { gsDefs :: Map Ident (SymDef Un.Expr)
                     , gsErrors :: [PosPair GroupError]
                     }

type Grouper a = State GroupState a

addGroupError :: Pos -> GroupError -> Grouper ()
addGroupError p e = do
  modify $ \s -> s { gsErrors = PosPair p e : gsErrors s }

addSymDef :: SymDef Un.Expr -> Grouper ()
addSymDef sd = do
  let sym = val (sdIdent sd)
  dm <- gets gsDefs
  case Map.lookup sym dm of
    Just old -> addGroupError (pos sd) $ PrevDefined (sdIdent old)
    Nothing -> modify $ \s -> s { gsDefs = Map.insert sym sd (gsDefs s) } 

collectGroups :: [Un.Decl] -> Grouper ()
collectGroups (Un.TypeDecl idl tp: decls) = do
  let (meqs,rest) = gatherManyEqs (Set.fromList (val <$> idl)) decls
  forM_ idl $ \psym -> do
    def <-
        case Map.lookup (val psym) meqs of
          Just ((p,lhs,rhs):r) -> do
            case r of
              [] -> return ()
              (p2,_,_):_ -> addGroupError p2 (DuplicateDef (val psym) p) 
            unless (null lhs) $
              addGroupError p $
                Limitation "Terms on left-hand side of assignment are unsupported."
            return (Just rhs)
          _ -> return Nothing
    addSymDef SD { sdIdent = psym
                 , sdType = tp
                 , sdDef = def
                 }
  collectGroups rest
collectGroups (Un.DataDecl psym tp ctors: decls) = do
  -- Add type symbol
  addSymDef SD { sdIdent = psym
               , sdType = tp
               , sdDef = Nothing
               }
  -- Add ctor symbols
  forM_ ctors $ \(Un.Ctor ctorId ctorTp) -> do
    addSymDef SD { sdIdent = ctorId
                 , sdType = ctorTp
                 , sdDef = Nothing
                 }
  collectGroups decls
collectGroups (Un.TermDef psym _ _ : decls) = do
  let (_, rest) = gatherEqs (val psym) decls
  addGroupError (pos psym) (NoSignature (val psym))
  collectGroups rest
collectGroups [] = return ()

data TypeConstraint
  = EqualTypes Term Term
  | HasType Term Un.Expr

data TCError = UnknownError

data TCContext = TCC { tcLocalCount :: Integer
                     , tccLocals :: Map Ident Integer
                     }

tcFindLocalVar :: Ident -> TCContext -> Maybe Integer
tcFindLocalVar nm ctx = fn <$> Map.lookup nm (tccLocals ctx)
  where fn i = tcLocalCount ctx - i - 1

initialTCContext :: TCContext 
initialTCContext = TCC 0 Map.empty

--TODO: Verify that un expression only refers to valid expressions.

{-
data TypeCheckerState = TCS {
                            }

type TypeChecker a = State TypeCheckerState a


execTypechecker :: TypeChecker () -> 

unexpectedBadExpression :: Pos -> a
unexpectedBadExpression p =
    error "internal: Bad expression from " ++ show p ++ " appears during typechecking"
-}

{-
tc :: Un.Expr -> TypeChecker (Term, Term)
tc ex =
  case ex of
    Un.IntLit  p i -> undefined p i
    Un.Var psym ->
      case tcFindLocalVar (val psym) ctx of
        Just i -> Term (LocalVar (pos psym) i)
        Nothing -> findGlobal psym
    Un.Con psym -> findGlobal psym
    Un.Sort p s ->  undefined p s
    Un.Lambda p args e -> undefined p args e
    Un.App x _ y -> undefined x y
    Un.Pi _ _ _ _ _ -> undefined
    Un.TupleValue p args -> undefined p args
    Un.TupleType p args -> undefined p args
    Un.RecordValue p args -> undefined p args
    Un.RecordSelector p s -> undefined p s
    Un.RecordType p args  -> undefined p args
    Un.ArrayValue p args -> undefined p args
    Un.Paren _ e -> tcExpr ctx e
    Un.TypeConstraint e _ _ -> tcExpr ctx e
    -- Ignore bad expressions, as they are the result of parse errors.
    Un.BadExpression p -> unexpectedBadExpression p
-}

{-      
tcDefs :: Map Ident (SymDef Un.Expr) -> Either [PosPair TCError] [SymDef Term]
tcDefs mi | null errs = Right (Map.elems mo)
          | otherwise = Left errs
  where indexMap = Map.fromList (Map.keys mi `zip` [0..])
        findGlobal psym =
          case Map.lookup (val psym) indexMap of
            Just i -> Term (GlobalRef (pos psym) i)
            Nothing -> error $ "internal: Failed to find global " ++ show (val psym)
        tcExpr :: TCContext -> Un.Expr -> Term
        tcExpr ctx ex =
          case ex of
            Un.IntLit p i -> Term (IntLit p i)
            Un.Var psym ->
              case tcFindLocalVar (val psym) ctx of
                Just i -> Term (LocalVar (pos psym) i)
                Nothing -> findGlobal psym
            Un.Con psym -> findGlobal psym
            Un.Sort p s ->  undefined p s
            Un.Lambda p args e -> undefined p args e
            Un.App x _ y -> undefined x y
            Un.Pi _ _ _ _ _ -> undefined
            Un.TupleValue p args -> undefined p args
            Un.TupleType p args -> undefined p args
            Un.RecordValue p args -> undefined p args
            Un.RecordSelector p s -> undefined p s
            Un.RecordType p args  -> undefined p args
            Un.ArrayValue p args -> undefined p args
            Un.Paren _ e -> tcExpr ctx e
            Un.TypeConstraint e _ _ -> tcExpr ctx e
            Un.BadExpression p -> unexpectedBadExpression p
        
        tcSymDef :: SymDef Un.Expr -> SymDef Term
        tcSymDef = fmap (tcExpr initialTCContext)
        mo = tcSymDef <$> mi
        errs = 

-}