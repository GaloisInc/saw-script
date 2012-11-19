{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor #-}
module Verifier.SAW.TypedAST
 ( Un.Ident, Un.mkIdent
 , Un.ParamType(..)
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

type LambdaVar e = (Un.ParamType, Ident, e)

-- The TermF representation requires that record and field expressions contain
-- the arguments to the record and a term for applying the field to.  Both of
-- these decisions were made so that terms have a well-specified type, and we do
-- not need to be concerned about record subtyping.

type DeBrujinIndex = Integer

-- Patterns are used to match equations.
data Pat e = PVar DeBrujinIndex -- ^ Variable and it's type (variables should appear at most once)
           | PCtor Ident [Pat e]
           | PTuple [Pat e]
           | PRecord (Map String (Pat e))
             -- An arbitrary term that matches anything, but needs to be later
             -- verified to be equivalent.
           | PInaccessible e
  deriving (Eq,Ord)

data DefEqn e
  = DefEqn [(Ident,e)] -- ^ List of variables introduced in definition and their types (context)
           [Pat e]  -- ^ List of patterns
           e -- ^ Right hand side.
  deriving (Eq, Ord)

-- A Definition contains an identifier, the type of the definition, and a list of equations.
data Def e = Def Ident e [DefEqn e]
  deriving (Eq,Ord)

data TermF e
  = IntLit Integer
  | LocalVar Integer   -- ^ Local variables are referenced by deBrujin index.
  | GlobalRef Integer  -- ^ Global variables are referenced by label.

  | Lambda (ParamType, Ident, e) e
  | App e e
  | Pi (ParamType, Ident, e) e

    -- Tuples may be 0 or 2+ elements.  The empty tuple is not allowed.
  | TupleValue [e]
  | TupleType [e]

  | RecordValue (Map String e)
  | RecordSelector e String
  | RecordType (Map String e)

  | ArrayValue [e]
    -- ^ List of bindings and the let expression itself.
    -- Let expressions introduce variables for each identifier.
  | Let [Def e] e

  | Sort Un.Sort
 deriving (Eq,Ord)

data Term = Term (TermF Term)

data SymEqn t = SymEqn [Un.LambdaBinding Un.Pat] t
  deriving (Eq,Ord,Functor,Show)

data SymDef t = SD { sdIdent :: PosPair Ident
                   , sdType  :: t
                   , sdDef   :: [SymEqn t]
                   } deriving (Functor, Show)

instance Positioned (SymDef t) where
  pos sd = pos (sdIdent sd)

--type Def = SymDef Term

data Module = Module {
         moduleDefs :: Map Ident (SymDef Term)
       }

data GroupError
 = PrevDefined (PosPair Ident) -- ^ Identifier and old position.
 | NoSignature Ident -- ^ Identifier is missing signature.
 | DuplicateDef Ident Pos -- ^ Equation for defintion already appeared.
   -- ^ An internal limitation resulted in an error.
 | Limitation String
 deriving (Show)

groupDecls :: [Un.Decl] -> ([PosPair GroupError], Map Ident (SymDef Un.Term))
groupDecls d = (reverse (gsErrors so), gsDefs so)
  where si = GS { gsDefs = Map.empty, gsErrors = [] }
        so = execState (identifySymDefs d) si

type UnEqn = (Pos, [Un.LambdaBinding Un.Pat], Un.Term)

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

data GroupState = GS { gsDefs :: Map Ident (SymDef Un.Term)
                     , gsErrors :: [PosPair GroupError]
                     }

type Grouper a = State GroupState a

addGroupError :: Pos -> GroupError -> Grouper ()
addGroupError p e = do
  modify $ \s -> s { gsErrors = PosPair p e : gsErrors s }

addSymDef :: SymDef Un.Term -> Grouper ()
addSymDef sd = do
  let sym = val (sdIdent sd)
  dm <- gets gsDefs
  case Map.lookup sym dm of
    Just old -> addGroupError (pos sd) $ PrevDefined (sdIdent old)
    Nothing -> modify $ \s -> s { gsDefs = Map.insert sym sd (gsDefs s) } 

-- | Collect individual untyped declarations into symbol definitions.
identifySymDefs :: [Un.Decl] -> Grouper ()
identifySymDefs (Un.TypeDecl idl tp: decls) = do
  let (meqs,rest) = gatherManyEqs (Set.fromList (val <$> idl)) decls
  forM_ idl $ \psym -> do
    let eqs = fromMaybe [] $ Map.lookup (val psym) meqs
    let mapEqn (_, lhsl, rhs) = SymEqn lhsl rhs
    addSymDef SD { sdIdent = psym
                 , sdType = tp
                 , sdDef = mapEqn <$> eqs
                 }
  identifySymDefs rest
identifySymDefs (Un.DataDecl psym tp ctors: decls) = do
  -- Add type symbol
  addSymDef SD { sdIdent = psym
               , sdType = tp
               , sdDef = []
               }
  -- Add ctor symbols
  forM_ ctors $ \(Un.Ctor ctorId ctorTp) -> do
    addSymDef SD { sdIdent = ctorId
                 , sdType = ctorTp
                 , sdDef = []
                 }
  identifySymDefs decls
identifySymDefs (Un.TermDef psym _ _ : decls) = do
  let (_, rest) = gatherEqs (val psym) decls
  addGroupError (pos psym) (NoSignature (val psym))
  identifySymDefs rest
identifySymDefs [] = return ()

data TypeConstraint
  = EqualTypes Term Term
  | HasType Term Un.Term

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

unexpectedBadTermession :: Pos -> a
unexpectedBadTermession p =
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
    Un.BadTerm p -> unexpectedBadTerm p
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