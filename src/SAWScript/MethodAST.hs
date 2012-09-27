{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : jhendrix, lerkok
-}

module SAWScript.MethodAST where

import SAWScript.Utils
import qualified Data.Map as M
import SAWScript.Token

data Input v = Input { inpPos :: Pos, inpVal :: v }
  deriving (Show)

inp :: Token Pos -> v -> Input v
inp tok v = Input (tokPos tok) v

-- result of parsing a bunch of method specs
type SSPgm = M.Map FilePath ([Input SAWScriptCommand])

type BitWidth = Int

data ExprWidth
  = WidthVar Pos String
  | WidthConst Pos BitWidth
  | WidthAdd Pos ExprWidth ExprWidth
  deriving (Show)

-- | Java types for symbolic simulator.
data JavaType
    = BoolType Pos
    | ByteType Pos
    | CharType Pos
    | DoubleType Pos
    | FloatType Pos
    | IntType Pos
    | LongType Pos
    | ShortType Pos
    | RefType Pos [String] -- ^ Class with given dots.
    | ArrayType JavaType Int -- ^ array with given element type and length
  deriving (Show)

javaTypePos :: JavaType -> Pos
javaTypePos (BoolType p) = p
javaTypePos (ByteType p) = p
javaTypePos (CharType p) = p
javaTypePos (DoubleType p) = p
javaTypePos (FloatType p) = p
javaTypePos (IntType p) = p
javaTypePos (LongType p) = p
javaTypePos (ShortType p) = p
javaTypePos (RefType p _) = p
javaTypePos (ArrayType tp _) = javaTypePos tp

-- | Expressions types for AST.
data ExprType
  = BitType Pos
  | BitvectorType Pos ExprWidth
  | Array Pos ExprWidth ExprType
  | Record Pos [(Pos, String, ExprType)]
  | ShapeVar Pos String
 deriving (Show)

data FnType = FnType [ExprType] ExprType
  deriving (Show)

-- | Roughly correspond to Cryptol expressions, but can also reference
-- Java variables.
data Expr
    = Var Pos String
    | ConstantBool Pos Bool
    | ConstantInt  Pos Integer
    | ThisExpr Pos
    -- * Highest precedence
    -- | Array comprehension.
    | MkArray Pos [Expr]
    -- | Making a record
    | MkRecord Pos [(Pos, String, Expr)]
    | ArgExpr Pos Int
    | LocalExpr Pos Integer
    -- Precedence 13
    -- | Type annotation on an expression.
    | TypeExpr Pos Expr ExprType
    -- | Dereference field
    | DerefField Pos Expr String
    -- Precedence 12
    -- | Extract value from array.
    | GetArray Pos Expr Expr
    -- | Uninterpreted functions.
    | ApplyExpr Pos String [Expr]
    -- Precedence 11
    -- | Boolean negation (not)
    | NotExpr  Pos Expr
    -- | Bitwise complement (~)
    | BitComplExpr Pos Expr
    -- | Integer negation (-)
    | NegExpr Pos Expr
    -- Precedence 10
    -- | Multiplication
    | MulExpr Pos Expr Expr
    -- | Signed division  (/s)
    | SDivExpr Pos Expr Expr
    -- | Signed remainder  (%s)
    | SRemExpr Pos Expr Expr
    -- Precedence 9
    -- | Addition
    | PlusExpr Pos Expr Expr
    -- | Subtraction
    | SubExpr Pos Expr Expr
    -- Precedence 8
    -- | Shift left (<<)
    | ShlExpr  Pos Expr Expr
    -- | Signed shift right (>>s)
    | SShrExpr Pos Expr Expr
    -- | Unsigned shift right (>>u)
    | UShrExpr Pos Expr Expr
    -- Precedence 7
    -- | Bitwise and (&)
    | BitAndExpr  Pos Expr Expr
    -- Precedence 6
    -- | Bitwise xor (^)
    | BitXorExpr  Pos Expr Expr
    -- Precedence 5
    -- | Bitwise or (|)
    | BitOrExpr  Pos Expr Expr
    -- Precedence 4
    -- | Cryptol append operator (#)
    | AppendExpr Pos Expr Expr
    -- Precedence 3
    -- | Equality (==)
    | EqExpr   Pos Expr Expr
    -- | Inequality
    | IneqExpr Pos Expr Expr
    -- Precedence 2
    -- | Signed greater than or equal operation (>=s)
    | SGeqExpr Pos Expr Expr
    -- | Unsigned greater than or equal operation (>=u)
    | UGeqExpr Pos Expr Expr
    -- | Signed greater than operation (>s)
    | SGtExpr  Pos Expr Expr
    -- | Unsigned greater than operation (>u)
    | UGtExpr  Pos Expr Expr
    -- | Signed less than or equal operation (<=s)
    | SLeqExpr Pos Expr Expr
    -- | Unsigned less than or equal operation (<=u)
    | ULeqExpr Pos Expr Expr
    -- | Signed less than operation (<s).
    | SLtExpr  Pos Expr Expr
    -- | Unsigned less than operation (<u).
    | ULtExpr  Pos Expr Expr
    -- Precedence 1
    -- | Boolean and (&&)
    | AndExpr  Pos Expr Expr
    -- Precedence 0.5
    -- | Boolean or (||)
    | OrExpr   Pos Expr Expr
    -- Precedence 0
    -- | Implication
    | ImpExpr  Pos Expr Expr
    -- Precedence 0
    -- | If-then-else
    | IteExpr  Pos Expr Expr Expr
  deriving (Show)

exprPos :: Expr -> Pos
exprPos (Var p _) = p
exprPos (ConstantBool p _) = p
exprPos (ConstantInt p _) = p
exprPos (MkArray p _) = p
exprPos (GetArray p _ _) = p
exprPos (MkRecord p _) = p
exprPos (ThisExpr p) = p
exprPos (ArgExpr p _) = p
exprPos (LocalExpr p _) = p
exprPos (TypeExpr p _ _) = p
exprPos (DerefField p _ _) = p
exprPos (ApplyExpr p _ _) = p
exprPos (NotExpr p _) = p
exprPos (BitComplExpr p _) = p
exprPos (NegExpr p _) = p
exprPos (MulExpr p _ _) = p
exprPos (SDivExpr p _ _) = p
exprPos (SRemExpr p _ _) = p
exprPos (PlusExpr p _ _) = p
exprPos (SubExpr p _ _) = p
exprPos (ShlExpr p _ _) = p
exprPos (SShrExpr p _ _) = p
exprPos (UShrExpr p _ _) = p
exprPos (BitAndExpr p _ _) = p
exprPos (BitXorExpr p _ _) = p
exprPos (BitOrExpr  p _ _) = p
exprPos (AppendExpr p _ _) = p
exprPos (EqExpr   p _ _) = p
exprPos (IneqExpr p _ _) = p
exprPos (SGeqExpr p _ _) = p
exprPos (UGeqExpr p _ _) = p
exprPos (SGtExpr  p _ _) = p
exprPos (UGtExpr  p _ _) = p
exprPos (SLeqExpr p _ _) = p
exprPos (ULeqExpr p _ _) = p
exprPos (SLtExpr  p _ _) = p
exprPos (ULtExpr  p _ _) = p
exprPos (AndExpr  p _ _) = p
exprPos (OrExpr   p _ _) = p
exprPos (ImpExpr  p _ _) = p
exprPos (IteExpr  p _ _ _) = p

type JavaFieldName = String

data RewriteVar = RewriteVar Pos String
  deriving (Show)

type SpecName = String

data MethodLocation
   = PC Integer
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

data VerifyCommand
   = Rewrite
   | ABC
   | SmtLib (Maybe Int) (Maybe String) -- version, file
   | Yices (Maybe Int)
   | Expand Expr
   | VerifyAt Pos MethodLocation VerifyCommand
     -- | Enable use of a rule or extern definition.
   | VerifyEnable Pos String
     -- | Disable use of a rule or extern definition.
   | VerifyDisable Pos String
   | VerifyBlock [VerifyCommand]
  deriving (Show)

data BehaviorDecl
  = VarDecl Pos [Expr] JavaType
    -- | Local binding within a method spec.
  | MethodLet Pos String Expr
  | MayAlias Pos [Expr]
    -- | Assert a given precondition is true when method is called.
  | AssertPred Pos Expr
  | AssertImp Pos Expr Expr
  | EnsureImp Pos Expr Expr
  | Modify Pos [Expr]
  | Return Pos Expr
  | MethodIf Pos Expr BehaviorDecl
  | MethodIfElse Pos Expr BehaviorDecl BehaviorDecl
  | Block [BehaviorDecl]
  deriving (Show)

data ValidationPlan 
  = QuickCheck Integer (Maybe Integer)
  | Blif (Maybe String) -- file
  | Verify VerifyCommand
  deriving (Show)

-- | Commands in a method spec.
data MethodSpecDecl
  -- | List of Java expressions that may alias.
  = SpecAt Pos MethodLocation BehaviorDecl
  | SpecPlan Pos ValidationPlan
  | Behavior BehaviorDecl
 deriving (Show)

type RuleName = String

type VarBinding = (String, ExprType)

data SAWScriptCommand
  -- | Import declarations from another Java verifier file.
  = ImportCommand FilePath
  -- | Load a SBV function from the given file path, and give
  -- it the corresponding name in this context.
  -- The function will be uninterpreted in future SBV function reads.
  -- This additionally introduces a rule named "<function_name>.def"
  | ExternSBV String FilePath FnType
  -- | Global constant binding.
  | GlobalLet String Expr
  -- | Global function binding.
  | GlobalFn String [Input VarBinding] ExprType Expr
  -- | Pragma to bind a function to an SBV input (automatic with ExternSBV).
  | SBVPragma String -- ^ SAWScript function name
              String -- ^ SBV function name.
  -- | Verification option ("on" == True && "off" == False)
  | SetVerification Bool
  -- | Define a Java method spec.
  | DeclareMethodSpec [String] [MethodSpecDecl]
  -- | Define a rewrite rule with the given name, left-hand-side and right-hand
  -- side.
  | Rule RuleName [Input VarBinding] Expr Expr
  -- | Enable use of a rule or extern definition.
  | Enable String
  -- | Disable use of a rule or extern definition.
  | Disable String
 deriving (Show)
