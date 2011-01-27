module SAWScript.MethodAST where

import SAWScript.Utils
import qualified Data.Map as M

-- result of parsing a bunch of method specs
type JVPrograms = M.Map FilePath [VerifierCommand]
data JVPgm      = JVPgm FilePath JVPrograms

type JavaFieldName = String

{-Notes.
To integerate this into the current symbolic simulator, we need to
change the type system so that:
 * Array types do not contain the type of the index.
 * Records are structural rather than nominal (may be implemented in SAWScript.exe).
-}

-- | An expression representing a particular JVM value.
data JavaExpression
    = This Pos
    -- | "Arg 0" corresponds to argument in Java function.
    | Arg Pos Int
    -- | @InstanceField x "foo"@ corresponds to Java "x.foo"
    | InstanceField Pos JavaExpression JavaFieldName
  deriving (Show)

type BitWidth = Int

-- | Expressions types for AST.
data ExprType 
  = BoolType
  | BitvectorType BitWidth
  | Array Int ExprType
  | Record [(String, ExprType)]
 deriving (Eq, Ord, Show)

-- | Roughly correspond to Cryptol expressions, but can also reference
-- Java variables.
data MixExpr v
    -- * External values
    = Extern v 
    -- * Primitive constants.
    | ConstantBool Pos Bool
    | ConstantInt  Pos BitWidth Integer
    -- * Arrays
    | MkArray Pos [MixExpr v] 
    -- * Records
    | MkRecord   Pos [(String, MixExpr v)]
    | DerefField Pos (MixExpr v) String
    -- * Uninterpreted functions.
    | UinterpretedExpr Pos String [MixExpr v]
    -- * Builtin operators.
    | EqExpr    Pos (MixExpr v) (MixExpr v)
    | IteExpr   Pos (MixExpr v) (MixExpr v) (MixExpr v)
    | TruncExpr Pos BitWidth (MixExpr v)
    -- | Signed extend bitwidth.
    | SExtExpr Pos BitWidth (MixExpr v)
    -- | Unsigned extend bitwidth.
    | UExtExpr Pos BitWidth (MixExpr v)
    | NotExpr  Pos (MixExpr v)
    | AndExpr  Pos (MixExpr v) (MixExpr v)
    | OrExpr   Pos (MixExpr v) (MixExpr v)
    | XorExpr  Pos (MixExpr v) (MixExpr v)
    | ShlExpr  Pos (MixExpr v) (MixExpr v)
    -- | Signed shift right (>>s) for syntax.
    | SShrExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned shift right (>>u) for syntax.
    | UShrExpr Pos (MixExpr v) (MixExpr v)
    -- | Cryptol append operator (#)
    | AppendExpr Pos (MixExpr v) (MixExpr v)
    | NegExpr Pos (MixExpr v)
    | AddExpr Pos (MixExpr v) (MixExpr v)
    | MulExpr Pos (MixExpr v) (MixExpr v)
    | SubExpr Pos (MixExpr v) (MixExpr v)
    | SDivExpr Pos (MixExpr v) (MixExpr v)
    | SRemExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed greater than or equal operation.
    | SGeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned greater than or equal operation.
    | UGeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed greater than operation.
    | SGtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Unsigned greater than operation.
    | UGtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Signed less than or equal operation.
    | SLeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Unsigned less than or equal operation.
    | ULeqExpr Pos (MixExpr v) (MixExpr v)
    -- | Signed less than operation.
    | SLtExpr  Pos (MixExpr v) (MixExpr v)
    -- | Unsigned less than operation.
    | ULtExpr  Pos (MixExpr v) (MixExpr v)
    | GetArrayValueExpr Pos (MixExpr v) (MixExpr v)
    | SetArrayValueExpr Pos (MixExpr v) (MixExpr v) (MixExpr v)
  deriving (Show)

-- | A method spec term is an expression that may refer to 
-- Java expressions.
type MethodSpecTerm = MixExpr JavaExpression

data RewriteVar = RewriteVar Pos String ExprType
  deriving (Show)

-- | A rewrite term is an expression that may refer to named and
-- typed variables.
type RewriteTerm = MixExpr RewriteVar

-- | The type assigned to a Java value for symbolic simulation purposes.
data MethodSpecType
    -- | A constant array.
    = SpecArrayConstant ![Integer]
    -- | A specific class for a reference (objects must be non-null).
    | SpecRefClass !String
    -- | Array of integer or long values with given length.
    | SpecArray !Int
  deriving (Show)

-- | Change to the JVM state made by running method.
data MethodSpecUpdate
  -- | Update value in array to given expression or new fresh terms
  -- if no expression is given.
  -- N.B. At most one update expression should be given for each potential
  -- aliases, and the Java expressions appearing in the left and right hand
  -- sides are evaluated in the context of the original state.
  = Update JavaExpression (Maybe MethodSpecTerm)
 deriving (Show)

type SpecName = String

data JavaMethodSpec = JavaMethodSpec {
         specName :: SpecName
      -- | Class this method is for.
      , specClass :: String
      -- | Key for method this spec is for.
      , specMethodName :: String
      -- | List of classes that are assumed to be initialized before method executes.
      -- Note: This should be optional to define.
      , specInitializedClasses :: [String]
      -- | Types of references declared in specification.
      , specRefs :: [(JavaExpression, MethodSpecType)]
      -- | Sets of Java values that may reference each other.
      , specMayAliasClasses :: [[JavaExpression]]
      -- | Condition on arguments before method is called.
      , specPrecondition :: MethodSpecTerm
      -- | Changes to Java state.
      , specUpdates :: [MethodSpecUpdate]
      } deriving (Show)

type RuleName = String

data VerifierCommand
  -- | Import declarations from another Java verifier file.
  = ImportCommand Pos FilePath
  -- | Load a SBV function from the given file path, and give
  -- it the corresponding name in this context.
  -- The function will be uninterpreted in future SBV function reads.
  -- This additionally introduces a rule named "<function_name>.def"
  | LoadSBVFunction Pos String FilePath
  -- | Define a record.
  | DefineRecord Pos String [(String, ExprType)]
  -- | Define a Java method spec.
  | DefineJavaMethodSpec Pos JavaMethodSpec
  -- | Define a rewrite rule with the given name.
  | DefineRule Pos RuleName RewriteTerm RewriteTerm
  -- | Disable use of a rule
  | DisableRule Pos RuleName
  -- | Enable use of a rule.
  | EnableRule Pos RuleName
  -- | Bitblast a method spec.
  | BlastJavaMethodSpec Pos SpecName
  -- | Apply rewriting to eliminate a method spec.
  | ReduceJavaMethodSpec Pos SpecName
 deriving (Show)
