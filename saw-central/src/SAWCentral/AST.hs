{- |
Module      : SAWCentral.AST
Description : Datatypes representing SAWScript statements, expressions, and types.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module SAWCentral.AST
       ( PrimitiveLifecycle(..)
       , everythingAvailable
       , defaultAvailable
       , Name
       , Import(..)
       , Expr(..)
       , Pattern(..)
       , Stmt(..)
       , Rebindable(..)
       , DeclGroup(..)
       , Decl(..)
       , Context(..)
       , Type(..), TypeIndex
       , TyCon(..)
       , Schema(..)
       , SchemaPattern(..)
       , NamedType(..)
       , Kind(..)
       , kindStar, kindStarToStar
       , tMono, tForall, tUnit, tTuple, tRecord, tArray, tFun
       , tString, tTerm, tType, tBool, tInt, tAIG, tCFG
       , tJVMSpec, tLLVMSpec, tMIRSpec
       , tBlock, tContext, tVar
       , isContext

       , prettyWholeModule
       ) where

import qualified SAWSupport.Pretty as PPS (PrettyPrec(..), prettyTypeSig, commaSepAll, replicate)

import SAWCentral.Position (Pos(..), Positioned(..), maxSpan)

import Data.Text (Text)
import Data.List (genericReplicate)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)

import qualified Prettyprinter as PP
import           Prettyprinter (Pretty)

import qualified Cryptol.Parser.AST as P (ImportSpec(..), ModName)
import qualified Cryptol.Utils.Ident as P (identText, modNameChunks)

-- Lifecycle / Deprecation {{{

-- | Position in the life cycle of a primitive.
data PrimitiveLifecycle
  = Current         {- ^ Currently available in all modes. -}
  | WarnDeprecated  {- ^ Removal planned, available but causes a warning -}
  | HideDeprecated  {- ^ Will be removed soon, and available only when
                         requested. -}
  | Experimental    {- ^ Will be made @Current@ soon, but available only by
                         request at the moment. -}
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Set of all lifecycle values.
everythingAvailable :: Set PrimitiveLifecycle
everythingAvailable = Set.fromList [minBound .. maxBound]

-- | Default set of lifecycle values.
--   Keep this with its type to make sure it stays current.
defaultAvailable :: Set PrimitiveLifecycle
defaultAvailable = Set.fromList [Current, WarnDeprecated]

-- }}}

-- Names {{{

type Name = Text

-- }}}

-- Expr Level {{{

data Import = Import
  { iIsSubmodule :: Bool
  , iModule    :: Either FilePath P.ModName
  , iAs        :: Maybe P.ModName
  , iSpec      :: Maybe P.ImportSpec
  , iPos       :: Pos
  } deriving Show

instance Positioned Import where
  getPos = iPos

data Expr
  -- Constants
  = Bool Pos Bool
  | String Pos Text
  | Int Pos Integer
  | Code Pos Text
  | CType Pos Text
  -- Structures
  | Array  Pos [Expr]
    -- | A do-block, with zero or more statements and a final expression.
    --   The body is a pair so it can be carried around as a single object,
    --   which is convenient in a few places.
  | Block  Pos ([Stmt], Expr)
  | Tuple  Pos [Expr]
  | Record Pos (Map Name Expr)
  -- Accessors
  | Index   Pos Expr Expr
  | Lookup  Pos Expr Name
  | TLookup Pos Expr Integer
  -- LC
  | Var Pos Name
  -- | All functions are handled as lambdas. We hang onto the name
  --   from the function declaration (if there was one) for use in
  --   stack traces.
  | Lambda Pos (Maybe Name) Pattern Expr
  | Application Pos Expr Expr
  -- Sugar
  | Let Pos DeclGroup Expr
  | TSig Pos Expr Type
  | IfThenElse Pos Expr Expr Expr
  deriving Show

instance Positioned Expr where
  getPos (Bool pos _) = pos
  getPos (String pos _) = pos
  getPos (Int pos _) = pos
  getPos (Code pos _) = pos
  getPos (CType pos _) = pos
  getPos (Array pos _) = pos
  getPos (Block pos _) = pos
  getPos (Tuple pos _) = pos
  getPos (Record pos _) = pos
  getPos (Index pos _ _) = pos
  getPos (Lookup pos _ _) = pos
  getPos (TLookup pos _ _) = pos
  getPos (Var pos _) = pos
  getPos (Lambda pos _ _ _) = pos
  getPos (Application pos _ _) = pos
  getPos (Let pos _ _) = pos
  getPos (TSig pos _ _) = pos
  getPos (IfThenElse pos _ _ _) = pos

-- | Patterns.
--
--   In `PVar` the first `Pos` is the position of the whole pattern
--   (including any type) and the second is the position of just the
--   name itself.
data Pattern
  = PWild Pos (Maybe Type)
  | PVar Pos Pos Name (Maybe Type)
  | PTuple Pos [Pattern]
  deriving Show

instance Positioned Pattern where
  getPos (PWild pos _) = pos
  getPos (PVar fullpos _namepos _ _) = fullpos
  getPos (PTuple pos _) = pos

-- | Statements.
--
--   In `StmtCode` the first `Pos` is the position of the whole
--   construct (including the initial "let") and the second is the
--   position of just the Cryptol text.
--
--   Similarly, in `StmtTypedef` the first `Pos` is the position of
--   the whole construct (including the expansion) and the second is
--   the position of the name.
data Stmt
  = StmtBind     Pos Pattern Expr
  | StmtLet      Pos Rebindable DeclGroup
  | StmtCode     Pos Pos Text
  | StmtImport   Pos Import
  | StmtInclude  Pos Text
  | StmtTypedef  Pos Pos Text Type
  | StmtPushdir  Pos FilePath
  | StmtPopdir   Pos
  deriving Show

-- | Tracking/state type for the @let rebindable@ behavior.
data Rebindable
    = RebindableVar -- ^ produced by @let rebindable@
    | ReadOnlyVar   -- ^ produced by ordinary @let@ and by @rec@
  deriving (Eq, Show)

instance Positioned Stmt where
  getPos (StmtBind pos _ _)  = pos
  getPos (StmtLet pos _ _)       = pos
  getPos (StmtCode allpos _spos _str) = allpos
  getPos (StmtImport pos _)    = pos
  getPos (StmtInclude pos _)    = pos
  getPos (StmtTypedef allpos _apos _a _ty) = allpos
  getPos (StmtPushdir pos _) = pos
  getPos (StmtPopdir pos) = pos

-- | Systems of mutually recursive declarations.
--
--   Note that `Recursive` declarations never use `RebindableVar`.
data DeclGroup
  = Recursive [Decl]   -- ^ produced by @rec ... and ...@
  | NonRecursive Decl  -- ^ produced by @let ...@
  deriving Show

instance Positioned DeclGroup where
  getPos (Recursive ds) = maxSpan ds
  getPos (NonRecursive d) = getPos d

-- | Single declaration.
--
--   These appear in let expressions and statements; but _not_ in
--   monad-bind position; those have only patterns and can't be
--   polymorphic.
data Decl
  = Decl { dPos :: Pos, dPat :: Pattern, dType :: Maybe Schema, dDef :: Expr }
  deriving Show

instance Positioned Decl where
  getPos = dPos

-- }}}

-- Type Level {{{

-- | Type for the hardwired monad types. Note that these days the
--   @LLVMSetup@, @JVMSetup@, and @MIRSetup@ monad types are ordinary
--   abstract types defined in the builtin types list.
data Context
  = ProofScript
  | TopLevel
  deriving (Eq, Ord, Show)

-- The position information in a type should be thought of as its
-- provenance; for a type annotation in the input it'll be a concrete
-- file position. For types we infer, we want the position to record
-- not just where but also how the inference happened, so that when we
-- report this to the user they can see what's going on. (For example,
-- if we infer that a type must be a function because it's applied to
-- an argument, we record that it's inferred from context and the
-- position of the context is the position of the term that was
-- applied.) When the type flows around during type inference it
-- carries the position info with it.
--
-- Note that for a non-primitive type the various layers of the type
-- may have totally different provenance. (E.g. we might have List Int
-- where List was inferred from a term "[x]" somewhere but Int came
-- from an explicit annotation somewhere completely different.) So
-- printing this information usefully requires some thought. As of
-- this writing most of that thought hasn't been put in yet and we
-- just stuff the inference info into the Show instance output. See
-- notes in Position.hs.
data Type
  = TyCon Pos TyCon [Type]
  | TyRecord Pos (Map Name Type)
  | TyVar Pos Name
  | TyUnifyVar Pos TypeIndex       -- ^ For internal typechecker use only
  deriving Show

instance Positioned Type where
  getPos (TyCon pos _ _) = pos
  getPos (TyRecord pos _) = pos
  getPos (TyVar pos _) = pos
  getPos (TyUnifyVar pos _) = pos

type TypeIndex = Integer

data TyCon
  = TupleCon Integer
  | ArrayCon
  | FunCon
  | StringCon
  | TermCon
  | TypeCon
  | BoolCon
  | IntCon
  | BlockCon
  | AIGCon
  | CFGCon
  | JVMSpecCon
  | LLVMSpecCon
  | MIRSpecCon
  | ContextCon Context
  deriving (Eq, Ord, Show)

data Schema = Forall [(Pos, Name)] Type
  deriving Show

-- | A schema pattern is like a schema but has potentially multiple
-- type entries that are meant to match fragments of a complete
-- schema. (We don't, for now at least, need a separate type for type
-- patterns and can just use Type.)
data SchemaPattern = SchemaPattern [(Pos, Name)] [Type]

-- | The things a (named) TyVar can refer to by its name.
--
-- A ConcreteType is a direct substitution for the type variable,
-- such as one generated by a typedef statement.
--
-- AbstractType is an opaque type whose only semantics are the
-- operations available for it, if any. The name identifies it; the
-- AbstractType constructor is a placeholder that only serves to
-- carry the kind information.
data NamedType = ConcreteType Type | AbstractType Kind

-- }}}

------------------------------------------------------------
-- Kinds {{{

--
-- For the time being we can handle kinds using the number of expected
-- type arguments. That is, Kind 0 is *. Apart from tuples the only
-- things we have are of kinds *, * -> *, and * -> * -> *, but we do
-- have tuples of arbitrary arity.
--
-- If we ever want additional structure (e.g. distinguishing the
-- monad/context types from other types) we can extend this
-- representation easily enough.
--

newtype Kind = Kind { kindNumArgs :: Word }
  deriving Eq

kindStar :: Kind
kindStar = Kind 0

kindStarToStar :: Kind
kindStarToStar = Kind 1

-- this isn't currently used
--kindStarToStarToStar :: Kind
--kindStarToStarToStar = Kind 2

instance PPS.PrettyPrec Kind where
  prettyPrec _ (Kind n) =
     PP.viaShow $ intercalate " -> " $ genericReplicate (n + 1) "*"


-- }}}


-- Pretty Printing {{{

prettyWholeModule :: [Stmt] -> PP.Doc ann
prettyWholeModule = (PP.<> PP.line') . vcatWithSemi . map PP.pretty

vcatWithSemi :: [PP.Doc ann] -> PP.Doc ann
vcatWithSemi = PP.vcat . map (PP.<> PP.semi)

instance Pretty Expr where
  pretty expr0 = case expr0 of
    Bool _ b   -> PP.viaShow b
    String _ s -> PP.dquotes (PP.pretty s)
    Int _ i    -> PP.pretty i
    Code _ s   -> PP.braces $ PP.braces $ PP.pretty s
    CType _ s  -> PP.braces $ PP.pretty $ "|" <> s <> "|"
    Array _ xs -> PP.list (map PP.pretty xs)
    Block _ (stmts, lastexpr) ->
      let stmts' = map PP.pretty stmts
          lastexpr' = PP.pretty lastexpr
          body = PP.align $ vcatWithSemi (stmts' ++ [lastexpr'])
          body' = PP.indent 3 body
      in
      "do" PP.<+> PP.lbrace PP.<> PP.line' PP.<> body' PP.<> PP.line' PP.<> PP.rbrace
    Tuple _ exprs -> PP.tupled (map PP.pretty exprs)
    Record _ mapping ->
      PP.braces . (PP.space PP.<>) . (PP.<> PP.space) . PP.align . PP.sep . PP.punctuate PP.comma $
      map (\(name, value) -> PP.pretty name PP.<+> "=" PP.<+> PP.pretty value)
      (Map.assocs mapping)
    Index _ _ _ -> error "No concrete syntax for AST node 'Index'"
    Lookup _ expr name -> PP.pretty expr PP.<> PP.dot PP.<> PP.pretty name
    TLookup _ expr int -> PP.pretty expr PP.<> PP.dot PP.<> PP.pretty int
    Var _ name ->
      PP.pretty name
    Lambda _ _mname pat expr ->
      "\\" PP.<+> PP.pretty pat PP.<+> "->" PP.<+> PP.pretty expr
    -- FIXME, use precedence to minimize parentheses
    Application _ f a -> PP.parens (PP.pretty f PP.<+> PP.pretty a)
    Let _ (NonRecursive decl) expr ->
      PP.fillSep
      [ "let" PP.<+> prettyDef decl
      , "in" PP.<+> PP.pretty expr
      ]
    Let _ (Recursive decls) expr ->
      PP.fillSep
      [ "let" PP.<+>
        PP.cat (PP.punctuate
                (PP.fillSep [PP.emptyDoc, "and" PP.<> PP.space])
                (map prettyDef decls))
      , "in" PP.<+> PP.pretty expr
      ]
    TSig _ expr typ -> PP.parens $ PP.pretty expr PP.<+> PP.colon PP.<+> PPS.prettyPrec 0 typ
    IfThenElse _ e1 e2 e3 ->
      "if" PP.<+> PP.pretty e1 PP.<+>
      "then" PP.<+> PP.pretty e2 PP.<+>
      "else" PP.<+> PP.pretty e3

instance PPS.PrettyPrec Expr where
  prettyPrec _ e = PP.pretty e

instance Pretty Pattern where
  pretty pat = case pat of
    PWild _ mType ->
      prettyMaybeTypedArg ("_", mType)
    PVar _ _ name mType ->
      prettyMaybeTypedArg (name, mType)
    PTuple _ pats ->
      PP.tupled (map PP.pretty pats)

instance Pretty Stmt where
   pretty = \case
      StmtBind _ (PWild _ _ty) expr ->
         PP.pretty expr
      StmtBind _ pat expr ->
         PP.pretty pat PP.<+> "<-" PP.<+> PP.align (PP.pretty expr)
      StmtLet _ rebindable (NonRecursive decl) ->
         let header = case rebindable of
               RebindableVar -> "let rebindable"
               ReadOnlyVar -> "let"
         in
         header PP.<+> prettyDef decl
      StmtLet _ _ (Recursive decls) ->
         "rec" PP.<+>
         PP.cat (PP.punctuate
            (PP.fillSep [PP.emptyDoc, "and" PP.<> PP.space])
            (map prettyDef decls))
      StmtCode _ _ code ->
         "let" PP.<+>
            (PP.braces . PP.braces $ PP.pretty code)
      StmtImport _ Import{iModule,iAs,iSpec} ->
         "import" PP.<+>
         (case iModule of
            Left filepath ->
               PP.dquotes . PP.pretty $ filepath
            Right modName ->
               ppModName modName) PP.<>
         (case iAs of
            Just modName ->
               PP.space PP.<> "as" PP.<+> ppModName modName
            Nothing -> PP.emptyDoc) PP.<>
         (case iSpec of
            Just (P.Hiding names) ->
               PP.space PP.<> "hiding" PP.<+> PP.tupled (map ppIdent names)
            Just (P.Only names) ->
               PP.space PP.<> PP.tupled (map ppIdent names)
            Nothing -> PP.emptyDoc)
      StmtInclude _ name ->
          "include" PP.<+> PP.dquotes (PP.pretty name)
      StmtTypedef _ _ name ty ->
         "typedef" PP.<+> PP.pretty name PP.<+> PPS.prettyPrec 0 ty
      StmtPushdir _ dir ->
         ".pushdir" PP.<+> PP.pretty dir
      StmtPopdir _ ->
         ".popdir"
      --expr -> PP.cyan . PP.viaShow expr

      where
        ppModName mn = PP.pretty (intercalate "." (P.modNameChunks mn))
        ppIdent i = PP.pretty (P.identText i)
        --ppName n = ppIdent (P.nameIdent n)

prettyDef :: Decl -> PP.Doc ann
prettyDef (Decl _ pat0 _ def) =
   let dissectLambda :: Expr -> ([Pattern], Expr)
       dissectLambda = \case
          Lambda _pos _name pat (dissectLambda -> (pats, expr)) -> (pat : pats, expr)
          expr -> ([], expr)
       (args, body) = dissectLambda def
       pat0' = PP.pretty pat0
       args' =
           if not (null args) then
               PP.hsep (map PP.pretty args) PP.<> PP.space
           else
               PP.emptyDoc
       body' = PP.pretty body
   in
   pat0' PP.<+> args' PP.<> "=" PP.<+> body'

prettyMaybeTypedArg :: (Name, Maybe Type) -> PP.Doc ann
prettyMaybeTypedArg (name,Nothing) =
   PP.pretty name
prettyMaybeTypedArg (name,Just typ) =
   PP.parens $ PP.pretty name PP.<+> PP.colon PP.<+> PPS.prettyPrec 0 typ


instance PPS.PrettyPrec Schema where
  prettyPrec _ (Forall ns t) = case ns of
    [] -> PPS.prettyPrec 0 t
    _  -> PP.braces (PPS.commaSepAll $ map PP.pretty ns') PP.<+> PPS.prettyPrec 0 t
          where ns' = map (\(_pos, n) -> n) ns

instance PPS.PrettyPrec Type where
  prettyPrec par t@(TyCon _ tc ts) = case (tc,ts) of
    (_,[])                 -> PPS.prettyPrec par tc
    (TupleCon _,_)         -> PP.parens $ PPS.commaSepAll $ map (PPS.prettyPrec 0) ts
    (ArrayCon,[typ])       -> PP.brackets (PPS.prettyPrec 0 typ)
    (FunCon,[f,v])         -> (if par > 0 then PP.parens else id) $
                                PPS.prettyPrec 1 f PP.<+> "->" PP.<+> PPS.prettyPrec 0 v
    (BlockCon,[cxt,typ])   -> (if par > 1 then PP.parens else id) $
                                PPS.prettyPrec 1 cxt PP.<+> PPS.prettyPrec 2 typ
    _ -> error $ "malformed TyCon: " ++ show t
  prettyPrec _par (TyRecord _ fs) =
      PP.braces
    $ PPS.commaSepAll
    $ map (\(n,t) -> PP.pretty n `PPS.prettyTypeSig` PPS.prettyPrec 0 t)
    $ Map.toList fs
  prettyPrec _par (TyUnifyVar _ i)    = "t." PP.<> PP.pretty i
  prettyPrec _par (TyVar _ n)         = PP.pretty n

instance PPS.PrettyPrec TyCon where
  prettyPrec par tc = case tc of
    TupleCon n     -> PP.parens $ PPS.replicate (n - 1) $ PP.pretty ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.emptyDoc
    FunCon         -> PP.parens $ "->"
    StringCon      -> "String"
    TermCon        -> "Term"
    TypeCon        -> "Type"
    BoolCon        -> "Bool"
    IntCon         -> "Int"
    AIGCon         -> "AIG"
    CFGCon         -> "CFG"
    JVMSpecCon     -> "JVMSpec"
    LLVMSpecCon    -> "LLVMSpec"
    MIRSpecCon     -> "MIRSpec"
    BlockCon       -> "<Block>"
    ContextCon cxt -> PPS.prettyPrec par cxt

instance PPS.PrettyPrec Context where
  prettyPrec _ c = case c of
    ProofScript  -> "ProofScript"
    TopLevel     -> "TopLevel"

instance PPS.PrettyPrec NamedType where
  prettyPrec par ty = case ty of
    ConcreteType ty' -> PPS.prettyPrec par ty'
    AbstractType kind -> "<opaque " PP.<> PPS.prettyPrec 0 kind PP.<> ">"

-- }}}

-- Type Constructors {{{

tMono :: Type -> Schema
tMono = Forall []

tForall :: [(Pos, Name)] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t

tUnit :: Pos -> Type
tUnit pos = tTuple pos []

tTuple :: Pos -> [Type] -> Type
tTuple pos ts = TyCon pos (TupleCon $ fromIntegral $ length ts) ts

tRecord :: Pos -> [(Name, Type)] -> Type
tRecord pos fields = TyRecord pos (Map.fromList fields)

tArray :: Pos -> Type -> Type
tArray pos t = TyCon pos ArrayCon [t]

tFun :: Pos -> Type -> Type -> Type
tFun pos f v = TyCon pos FunCon [f,v]

tString :: Pos -> Type
tString pos = TyCon pos StringCon []

tTerm :: Pos -> Type
tTerm pos = TyCon pos TermCon []

tType :: Pos -> Type
tType pos = TyCon pos TypeCon []

tBool :: Pos -> Type
tBool pos = TyCon pos BoolCon []

tAIG :: Pos -> Type
tAIG pos = TyCon pos AIGCon []

tCFG :: Pos -> Type
tCFG pos = TyCon pos CFGCon []

tInt :: Pos -> Type
tInt pos = TyCon pos IntCon []

tJVMSpec :: Pos -> Type
tJVMSpec pos = TyCon pos JVMSpecCon []

tLLVMSpec :: Pos -> Type
tLLVMSpec pos = TyCon pos LLVMSpecCon []

tMIRSpec :: Pos -> Type
tMIRSpec pos = TyCon pos MIRSpecCon []

tBlock :: Pos -> Type -> Type -> Type
tBlock pos c t = TyCon pos BlockCon [c,t]

tContext :: Pos -> Context -> Type
tContext pos c = TyCon pos (ContextCon c) []

tVar :: Pos -> Name -> Type
tVar pos n = TyVar pos n

-- }}}

-- Type Classifiers {{{

-- The idea is that calling these is/should be less messy than direct
-- pattern matching, and also help a little to avoid splattering the
-- internal representation of types all over the place.

-- | Check if type 'ty' is a 'Context' type of context 'c'.
isContext ::
       Context          -- ^ The context 'c' to look for
    -> Type             -- ^ The type 'ty' to inspect
    -> Bool
isContext c ty = case ty of
  TyCon _pos (ContextCon c') [] | c' == c -> True
  _ -> False

-- }}}
