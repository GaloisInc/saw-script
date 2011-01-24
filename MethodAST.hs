module MethodAST where

type JavaFieldName = String

{-Notes.
To integerate this into the current symbolic simulator, we need to
change the type system so that:
 * Array types do not contain the type of the index.
 * Records are structural rather than nominal (may be implemented in SAWScript.exe).
-}

-- | An expression representing a particular JVM value.
data JavaExpression
    = This
    -- | "Arg 0" corresponds to argument in Java function.
    | Arg Int
    -- | @InstanceField x "foo"@ corresponds to Java "x.foo"
    | InstanceField JavaExpression JavaFieldName
  deriving (Eq, Ord, Show)

type UninterpretedOp = String

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
    | ConstantBool Bool
    | ConstantInt BitWidth Integer
    -- * Arrays
    | MkArray [MixExpr v]
    -- * Records
    | MkRecord [(String, MixExpr v)]
    | DerefField (MixExpr v) String
    -- * Uninterpreted functions.
    | UinterpretedFn String [MixExpr v]
    -- * Builtin operators.
    | EqFn    (MixExpr v) (MixExpr v)
    | IteFn   (MixExpr v) (MixExpr v) (MixExpr v)
    | TruncFn BitWidth (MixExpr v)
    | SignedExtFn BitWidth (MixExpr v)
    | NotFn (MixExpr v)
    | AndFn (MixExpr v) (MixExpr v)
    | OrFn (MixExpr v) (MixExpr v)
    | XorFn (MixExpr v) (MixExpr v)
    | ShlFn (MixExpr v) (MixExpr v)
    | ShrFn (MixExpr v) (MixExpr v)
    | UShrFn (MixExpr v) (MixExpr v)
    | AppendIntFn (MixExpr v) (MixExpr v)
    | NegFn (MixExpr v)
    | AddFn (MixExpr v) (MixExpr v)
    | MulFn (MixExpr v) (MixExpr v)
    | SubFn (MixExpr v) (MixExpr v)
    | SignedDivFn (MixExpr v) (MixExpr v)
    | SignedRemFn (MixExpr v) (MixExpr v)
    | SignedLeqFn (MixExpr v) (MixExpr v)
    | SignedLtFn  (MixExpr v) (MixExpr v)
    | UnsignedLeqFn (MixExpr v) (MixExpr v)
    | UnsignedLtFn  (MixExpr v) (MixExpr v)
    | GetArrayValueFn (MixExpr v) (MixExpr v)
    | SetArrayValueFn (MixExpr v) (MixExpr v) (MixExpr v)
  deriving (Eq, Ord, Show)

type MethodSpecTerm = MixExpr JavaExpression

-- | This is essential a mixed expression 
type RewriteTerm = MixExpr (String, ExprType)


-- | The type assigned to a Java value for symbolic simulation purposes.
data MethodSpecType
    -- | A constant array.
    = SpecArrayConstant ![Integer]
    -- | A specific class for a reference (objects must be non-null).
    | SpecRefClass !String
    -- | Array of integer or long values with given length.
    | SpecArray !Int
  deriving (Eq, Ord, Show)

-- | Change to the JVM state made by running method.
data MethodSpecUpdate
  -- | Update value in array to given expression or new fresh terms
  -- if no expression is given.
  -- N.B. At most one update expression should be given for each potential
  -- aliases, and the Java expressions appearing in the left and right hand
  -- sides are evaluated in the context of the original state.
  = Update JavaExpression (Maybe MethodSpecTerm)
 deriving (Eq, Ord, Show)

type SpecName = String

data RewriteRule = Rule RewriteTerm RewriteTerm
  deriving (Eq, Ord, Show)

data VerifierCommand 
  -- | Import declarations from another Java verifier file.
  = ImportCommand FilePath
  -- | Load a SBV function from the given file path, and give
  -- it the corresponding name in this context.
  -- The function will be uninterpreted in future SBV function reads.
  | LoadSBVFunction String FilePath
  | DeclareJavaMethodSpec {
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
      }
  | BlastJavaMethodSpec SpecName
  | ReduceJavaMethodSpec SpecName [RewriteRule]
 deriving (Eq, Ord, Show)
