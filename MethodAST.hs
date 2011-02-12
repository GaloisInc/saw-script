{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : jhendrix, lerkok
-}

module SAWScript.MethodAST where

import SAWScript.Utils
import qualified Data.Map as M

-- result of parsing a bunch of method specs
type SSPgm = M.Map FilePath [VerifierCommand]

{-Notes.
To integerate this into the current symbolic simulator, we need to
change the type system so that:
 * Array types do not contain the type of the index.
 * Records are structural rather than nominal (may be implemented in SAWScript.exe).
-}

type BitWidth = Int

data ExprWidth
  = WidthVar Pos String
  | WidthConst Pos BitWidth
  | WidthAdd Pos ExprWidth ExprWidth
  deriving (Show)

-- | Java types for symbolic simulator.
data JavaType
    = RefType Pos [String] -- ^ Class with given dots.
    | IntArray Pos Int -- ^ Int array with given length
    | LongArray Pos Int -- ^ Long array with given length.
    | BoolScalar Pos
    | IntScalar Pos
    | LongScalar Pos
  deriving (Show)

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

    -- * Highest precedence

    -- | Array comprehension.
    | MkArray Pos [Expr]
    -- | Making a record
    | MkRecord Pos [(Pos, String, Expr)]

    -- Precedence 13
    -- | Type annotation on an expression.
    | TypeExpr Pos Expr ExprType
    -- | Dereference field
    | DerefField Pos Expr String

    -- Precedence 12
    -- | Java Value
    | JavaValue Pos JavaRef
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
    -- | If-then-else
    | IteExpr  Pos Expr Expr Expr
  deriving (Show)

type JavaFieldName = String

-- | An expression representing a particular JVM value.
data JavaRef
    = This Pos
    -- | "args[0]" corresponds to argument in Java function.
    | Arg Pos Int
    -- | @InstanceField x "foo"@ corresponds to Java "x.foo"
    -- Same precedence as deref field.
    | InstanceField Pos JavaRef JavaFieldName
  deriving (Show)

data RewriteVar = RewriteVar Pos String
  deriving (Show)

type SpecName = String

data VerificationMethod = ABC | Rewrite | Auto | Skip
  deriving (Eq, Show)

-- | Commands in a method spec.
data MethodSpecDecl
  = Type Pos [JavaRef] JavaType
  -- | List of Java expressions that may alias.
  | MayAlias Pos [JavaRef]
  -- | Contant value in reference.
  | Const Pos JavaRef Expr
  -- | Local binding within a method spec.
  | MethodLet Pos String Expr
  -- | Assume a given precondition is true when method is called.
  | Assume Pos Expr
  | Ensures Pos JavaRef Expr
  | Arbitrary Pos [JavaRef]
  | Returns Pos Expr
  | VerifyUsing Pos VerificationMethod
 deriving (Show)

type RuleName = String

data VerifierCommand
  -- | Import declarations from another Java verifier file.
  = ImportCommand Pos FilePath
  -- | Load a SBV function from the given file path, and give
  -- it the corresponding name in this context.
  -- The function will be uninterpreted in future SBV function reads.
  -- This additionally introduces a rule named "<function_name>.def"
  | ExternSBV Pos String FilePath FnType
  -- | Global binding.
  | GlobalLet Pos String Expr
  -- | Verification option ("on" == True && "off" == False)
  | SetVerification Pos Bool
  -- | Define a Java method spec.
  | DeclareMethodSpec Pos [String] [MethodSpecDecl]
  -- | Define a rewrite rule with the given name, left-hand-side and right-hand
  -- side.
  | Rule Pos RuleName [(Pos, String, ExprType)] Expr Expr
  -- | Disable use of a rule or extern definition.
  | Disable Pos String
  -- | Enable use of a rule or extern definition.
  | Enable Pos String
 deriving (Show)
