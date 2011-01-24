module MethodAST where

type JavaFieldName = String


-- | An expression representing a particular JVM value.
data JavaExpression
    = This
    -- | "Arg 0" corresponds to argument in Java function.
    | Arg Int
    -- | @InstanceField x "foo"@ corresponds to Java "x.foo"
    | InstanceField JavaExpression JavaFieldName
  deriving (Eq, Ord)

type UninterpretedOp = String

-- | Name of records.
type RecordName = String

type BitWidth = Int

data ExprType 
  = Bool
  | SignedBitVector 


-- | Roughly correspond to Cryptol expressions, but can also reference
-- Java variables.
data MixExpr
    -- | Returns value of Java expression as a Cryptol value.
    -- Java arrays are dereferenced and treated as a list of words.
    -- Integers and longs are treated as bit vectors with corresponding length.
    = JavaValue JavaExpression
    -- * Variables
    | Var String ExprType
    -- * Primitive constants.
    | ConstantBool Bool
    | ConstantInt BitWidth Int
    -- * Arrays
    | MkArray [MixExpr]
    -- * Records
    | MkRecord RecordName [MixExpr]
    | DerefField MixExpr String
    -- * Uninterpreted functions.
    | UinterpretedFn String [MixExpr]
    -- * Builtin operators.
    | EqFn    MixExpr MixExpr
    | IteFn   MixExpr MixExpr MixExpr
    | TruncFn BitWidth MixExpr
    | SignedExtFn BitWidth MixExpr
    | NotFn MixExpr
    | AndFn MixExpr MixExpr
    | OrFn MixExpr MixExpr
    | XorFn MixExpr MixExpr
    | ShlFn MixExpr MixExpr
    | ShrFn MixExpr MixExpr
    | UShrFn MixExpr MixExpr
    | AppendIntFn MixExpr MixExpr
    | NegFn MixExpr
    | AddFn MixExpr MixExpr
    | MulFn MixExpr MixExpr
    | SubFn MixExpr MixExpr
    | SignedDivFn MixExpr MixExpr
    | SignedRemFn MixExpr MixExpr
    | SignedLeqFn MixExpr MixExpr
    | SignedLtFn  MixExpr MixExpr
    | UnsignedLeqFn MixExpr MixExpr
    | UnsignedLtFn  MixExpr MixExpr
    | GetArrayValueFn MixExpr MixExpr
    | SetArrayValueFn MixExpr MixExpr MixExpr
  deriving (Eq, Ord)

-- | This is essential a mixed expression 
type CryptolExpression = MixedExpression.

-- | The type assigned to 
data JavaReferenceSymbolicType
    -- | A constant array.
    = SpecArrayConstant !(Vector Integer)
    -- | A specific class for a reference (objects must be non-null).
    | SpecRefClass !String
    -- | Array of integer or long values with given length.
    | SpecArray !Int32
  deriving (Eq, Ord, Show)

-- | Change to the JVM state made by running method.
data JavaUpdate
  -- | Update value in array to given expression or new fresh terms
  -- if no expression is given.
  -- N.B. At most one update expression should be given for each potential
  -- aliases, and the Java expressions appearing in the left and right hand
  -- sides are evaluated in the context of the original state.
  = Update JavaExpression (Maybe CryptolExpression)
 deriving (Eq, Ord, Show)

type SpecName = String

data CryptolRule = Rule CryptolTerm CryptolTerm

data VerifierCommand 
  -- | Import declarations from another Java verifier file.
  = ImportCommand FilePath
  -- | Load a SBV function from the given file path, and give
  -- it the corresponding name in this context.
  -- The function will be uninterpreted in future SBV function reads.
  | LoadSBVFunction String FilePath
  | DeclareSBVRecord TODO
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
      , specRefs :: [(JavaExpression
                    , JavaReferenceSymbolicType)]
      -- | Sets of Java values that may reference each other.
      , specMayAliasClasses :: [[JavaExpression]]
      -- | Condition on arguments before method is called.
      , specPrecondition :: CryptolExpression
      -- | Changes to Java state.
      , specUpdates :: [JavaUpdate]
      }
  | BlastJavaMethodSpec SpecName
  | ReduceJavaMethodSpec SpecName [CryptolRule]
 deriving (Eq, Ord, Show)
