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
  = WidthVar String
  | WidthConst BitWidth
  | WidthAdd ExprWidth ExprWidth
  deriving (Show)

-- | Java types for symbolic simulator.
data JavaType
  = RefType [String] -- ^ Class with given dots. 
  | IntArray Int -- ^ Int array with given length
  | LongArray Int -- ^ Long array with given length.   
  deriving (Show)

-- | Expressions types for AST.
data ExprType
  = BitType
  | BitvectorType ExprWidth
  | Array Int ExprType
  | Record [(Pos, String, ExprType)]
  | ShapeVar String
 deriving (Show)

data FnType = FnType [ExprType] ExprType
  deriving (Show)

-- | Roughly correspond to Cryptol expressions, but can also reference
-- Java variables.
data MixExpr v
    = Extern v
    | Var Pos String
    | ConstantBool Pos Bool
    | ConstantInt  Pos Integer

    -- * Highest precedence
   
    -- | Array comprehension.
    | MkArray Pos [MixExpr v]
    -- | Making a record
    | MkRecord   Pos [(Pos, String, MixExpr v)]
    
    -- Precedence 13
    -- | Type annotation on an expression.
    | TypeExpr Pos (MixExpr v) ExprType
    -- | Dereference field
    | DerefField Pos (MixExpr v) String

    -- Precedence 12
    -- | Uninterpreted functions.
    | ApplyExpr Pos String [MixExpr v]

    -- Precedence 11
    -- | Boolean negation (~)
    | NotExpr  Pos (MixExpr v)
    -- | Integer negation (-)
    | NegExpr Pos (MixExpr v)

    -- Precedence 10
    -- | Multiplication
    | MulExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed division  (/s)
    | SDivExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed remainder  (%s)
    | SRemExpr Pos (MixExpr v) (MixExpr v)

    -- Precedence 9
    -- | Addition
    | PlusExpr Pos (MixExpr v) (MixExpr v)
    -- | Subtraction
    | SubExpr Pos (MixExpr v) (MixExpr v)

    -- Precedence 8
    -- | Shift left (<<)
    | ShlExpr  Pos (MixExpr v) (MixExpr v)
    -- | Signed shift right (>>s)
    | SShrExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned shift right (>>u)
    | UShrExpr Pos (MixExpr v) (MixExpr v)

    -- Precedence 7
    -- | Bitwise and (&)
    | BitAndExpr  Pos (MixExpr v) (MixExpr v)

    -- Precedence 6
    -- | Bitwise xor (^)
    | BitXorExpr  Pos (MixExpr v) (MixExpr v)

    -- Precedence 5
    -- | Bitwise or (|)
    | BitOrExpr  Pos (MixExpr v) (MixExpr v)

    -- Precedence 4
    -- | Cryptol append operator (#)
    | AppendExpr Pos (MixExpr v) (MixExpr v)

    -- Precedence 3
    -- | Equality (==)
    | EqExpr   Pos (MixExpr v) (MixExpr v)
    -- | Inequality
    | IneqExpr Pos (MixExpr v) (MixExpr v)

    -- Precedence 2
    -- | Signed greater than or equal operation (>=s)
    | SGeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned greater than or equal operation (>=u)
    | UGeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed greater than operation (>s)
    | SGtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Unsigned greater than operation (>u)
    | UGtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Signed less than or equal operation (<=s)
    | SLeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned less than or equal operation (<=u)
    | ULeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed less than operation (<s).
    | SLtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Unsigned less than operation (<u).
    | ULtExpr  Pos (MixExpr v) (MixExpr v)

    -- Precedence 1
    -- | Boolean and (&&)
    | AndExpr  Pos (MixExpr v) (MixExpr v)
    -- | Boolean or (||)
    | OrExpr   Pos (MixExpr v) (MixExpr v)

    -- Precedence 0
    -- | If-then-else
    | IteExpr  Pos (MixExpr v) (MixExpr v) (MixExpr v)
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

-- | A method spec term is an expression that may refer to 
-- Java expressions.
type JavaExpr = MixExpr JavaRef

data RewriteVar = RewriteVar Pos String
  deriving (Show)

-- | A rewrite term is an expression that may refer to named and
-- typed variables.
type RewriteTerm = MixExpr RewriteVar

type SpecName = String

data VerificationMethod = Blast | Rewrite
  deriving (Show)

-- | Commands in a method spec.
data MethodSpecDecl 
  = Type Pos [JavaRef] JavaType
  -- | List of Java expressions that may alias.
  | MayAlias Pos [JavaRef]
  -- | Contant value in reference.
  | Const Pos JavaRef JavaExpr
  -- | Local binding within a method spec.
  | MethodLet Pos String JavaExpr
  | Assume Pos JavaExpr
  | Ensures Pos JavaRef JavaExpr
  | Arbitrary Pos [JavaRef]
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
  | GlobalLet Pos String JavaExpr
  -- | Verification option ("on" == True && "off" == False)
  | SetVerification Pos Bool
  -- | Define a Java method spec.
  | DeclareMethodSpec Pos [String] [MethodSpecDecl]
  -- | Define a rewrite rule with the given name, left-hand-side and right-hand
  -- side.
  | Rule Pos String RewriteTerm RewriteTerm
  -- | Disable use of a rule or extern definition.
  | Disable Pos String
  -- | Enable use of a rule or extern definition.
  | Enable Pos String
 deriving (Show)
