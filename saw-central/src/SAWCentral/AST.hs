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

     , Kind(..)
     , kindStar, kindStarToStar

     , TypeIndex
     , Context(..)
     , TyCon(..)
     , Type(..)
     , Schema(..)
     , SchemaPattern(..)
     , NamedType(..)

     , Expr(..)

     , Pattern(..)

     , Rebindable(..)
     , Import(..)
     , Stmt(..)

     , Decl(..)
     , DeclGroup(..)

     , ppKind
     , ppTyCon
     , ppType, prettyType
     , ppSchema, prettySchema
     , prettyNamedType
     , ppExpr, prettyExpr
     , ppPattern, prettyPattern
     , prettyWholeModule

     , tUnit, tTuple, tArray, tFun
     , tString, tTerm, tType, tBool, tInt, tBlock
     , tAIG, tCFG, tJVMSpec, tLLVMSpec, tMIRSpec
     , tContext
     , tRecord, tVar
     , tMono, tForall

     , isContext
     ) where

import qualified SAWSupport.Pretty as PPS

import SAWCentral.Panic (panic)
import SAWCentral.Position (Pos(..), Positioned(..), maxSpan)

import Data.Text (Text)
import qualified Data.Text as Text
import Data.List (genericReplicate)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)

import qualified Prettyprinter as PP
import           Prettyprinter ((<+>))

import qualified Cryptol.Parser.AST as P (ImportSpec(..), ModName)
import qualified Cryptol.Utils.Ident as P (identText, modNameChunks)


------------------------------------------------------------
-- Lifecycle / Deprecation

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


------------------------------------------------------------
-- Names

type Name = Text


------------------------------------------------------------
-- Kinds

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


------------------------------------------------------------
-- Types

type TypeIndex = Integer

-- | Type for the hardwired monad types. Note that these days the
--   @LLVMSetup@, @JVMSetup@, and @MIRSetup@ monad types are ordinary
--   abstract types defined in the builtin types list.
data Context
  = ProofScript
  | TopLevel
  deriving (Eq, Ord, Show)

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


------------------------------------------------------------
-- Expressions

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


------------------------------------------------------------
-- Patterns

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


------------------------------------------------------------
-- Statements

-- | Tracking/state type for the @let rebindable@ behavior.
data Rebindable
  = RebindableVar -- ^ produced by @let rebindable@
  | ReadOnlyVar   -- ^ produced by ordinary @let@ and by @rec@
  deriving (Eq, Show)

data Import = Import
  { iIsSubmodule :: Bool
  , iModule    :: Either FilePath P.ModName
  , iAs        :: Maybe P.ModName
  , iSpec      :: Maybe P.ImportSpec
  , iPos       :: Pos
  } deriving Show

-- | Statements.
--
--   In `StmtCode` the first `Pos` is the position of the whole
--   construct (including the initial "let") and the second is the
--   position of just the Cryptol text.
--
--   Similarly, in `StmtTypedef` the first `Pos` is the position of
--   the whole construct (including the expansion) and the second is
--   the position of the name.
--
--   `StmtPushdir` and `StmtPopdir` have no concrete syntax; they are
--   generated by the @include@ handling. See notes in the interpreter
--   for why they're needed.
--
--   The `Bool` in `StmtInclude` is `True` for @include_once@ and
--   `False` for ordinary @include@.
--
data Stmt
  = StmtBind     Pos Pattern Expr
  | StmtLet      Pos Rebindable DeclGroup
  | StmtCode     Pos Pos Text
  | StmtImport   Pos Import
  | StmtInclude  Pos Text Bool
  | StmtTypedef  Pos Pos Text Type
  | StmtPushdir  Pos FilePath
  | StmtPopdir   Pos
  deriving Show


------------------------------------------------------------
-- Declarations

-- | Single declaration.
--
--   These appear in let expressions and statements; but _not_ in
--   monad-bind position; those have only patterns and can't be
--   polymorphic.
data Decl
  = Decl { dPos :: Pos, dPat :: Pattern, dType :: Maybe Schema, dDef :: Expr }
  deriving Show

-- | Systems of mutually recursive declarations.
--
--   Note that `Recursive` declarations never use `RebindableVar`.
data DeclGroup
  = Recursive [Decl]   -- ^ produced by @rec ... and ...@
  | NonRecursive Decl  -- ^ produced by @let ...@
  deriving Show


------------------------------------------------------------
-- Position extraction

instance Positioned Type where
  getPos (TyCon pos _ _) = pos
  getPos (TyRecord pos _) = pos
  getPos (TyVar pos _) = pos
  getPos (TyUnifyVar pos _) = pos

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

instance Positioned Pattern where
  getPos (PWild pos _) = pos
  getPos (PVar fullpos _namepos _ _) = fullpos
  getPos (PTuple pos _) = pos

instance Positioned Import where
  getPos = iPos

instance Positioned Stmt where
  getPos (StmtBind pos _ _)  = pos
  getPos (StmtLet pos _ _)       = pos
  getPos (StmtCode allpos _spos _str) = allpos
  getPos (StmtImport pos _)    = pos
  getPos (StmtInclude pos _ _)    = pos
  getPos (StmtTypedef allpos _apos _a _ty) = allpos
  getPos (StmtPushdir pos _) = pos
  getPos (StmtPopdir pos) = pos

instance Positioned DeclGroup where
  getPos (Recursive ds) = maxSpan ds
  getPos (NonRecursive d) = getPos d

instance Positioned Decl where
  getPos = dPos


------------------------------------------------------------
-- Printing

ppKind :: Kind -> Text
ppKind (Kind n) =
    Text.intercalate " -> " $ genericReplicate (n + 1) "*"

ppContext :: Context -> Text
ppContext c = case c of
    ProofScript  -> "ProofScript"
    TopLevel     -> "TopLevel"

-- XXX: currently the typechecker calls this directly; however, it
-- would probably be better if it didn't, at which point we don't
-- need the somewhat unfortunate cases for tuple/array/function and
-- the rest can be folded into prettyType.
prettyTyCon :: TyCon -> PP.Doc ann
prettyTyCon tc = case tc of
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
    ContextCon cxt -> PP.pretty $ ppContext cxt

ppTyCon :: TyCon -> Text
ppTyCon tc = PPS.renderText PPS.defaultOpts $ prettyTyCon tc

prettyType :: Type -> PPS.Doc
prettyType = PP.group . visit 0
  where
    visit :: Int -> Type -> PPS.Doc
    visit prec ty0 = case ty0 of
      TyCon _ ctor args -> case (ctor, args) of
          (TupleCon n, _) ->
              if fromIntegral (length args) /= n then
                  -- These is no way to produce this state
                  croak "tuple" n args
              else
                  PP.align $ PP.parens $ PP.fillSep $ PP.punctuate "," $ map (visit 0) args
          (ArrayCon, [ty1]) ->
              PP.brackets $ visit 0 ty1
          (FunCon, [fun, arg]) ->
              let fun' = visit 1 fun
                  arg' = visit 0 arg
                  body = fun' <+> "->" <> PP.line <> arg'
              in
              if prec > 0 then PP.parens (PP.group body) else body
          (BlockCon, [m, arg]) ->
              let m' = visit 1 m
                  arg' = visit 2 arg
                  body = m' <+> arg'
              in
              if prec > 1 then PP.parens body else body
          (ArrayCon, _) -> croak "array" 1 args
          (FunCon, _) -> croak "function" 2 args
          (BlockCon, _) -> croak "block" 2 args
          (_, _) ->
              let ctor' = prettyTyCon ctor in
              case args of
                  [] -> ctor'
                  _ ->
                      let ctor'' = PPS.renderText PPS.defaultOpts ctor' in
                      croak ctor'' 0 args

      TyRecord _ fields ->
          let prettyField (name, ty) =
                let name' = PP.pretty name
                    ty' = visit 0 ty
                in
                PP.group $ PPS.prettyTypeSig name' ty'
              fields' = map prettyField $ Map.assocs fields
              body = PP.sep $ PP.punctuate "," $ fields'
              body' = PP.flatAlt (PP.indent 3 body) body
          in
          PP.braces (PP.line <> body' <> PP.line)

      TyUnifyVar _ i ->
          "t." <> PP.pretty i
      TyVar _ n ->
          PP.pretty n

    croak :: Text -> Integer -> [Type] -> a
    croak what n args =
        let ppArg arg = "   " <> (PPS.renderText PPS.defaultOpts $ visit 0 arg)
            args' = map ppArg args
        in
        panic "prettyType" $ [
            "Malformed " <> what <> " type constructor",
            "Expected " <> Text.pack (show n) <> " arguments, found:"
        ] ++ args'

ppType :: Type -> Text
ppType ty =
    PPS.renderText PPS.defaultOpts $ prettyType ty

prettySchema :: Schema -> PPS.Doc
prettySchema (Forall ns t) =
    let t' = prettyType t in
    case ns of
      [] -> t'
      _  ->
          let prettyQuant (_pos, n) = PP.pretty n
              ns' = PP.braces $ PP.hsep $ PP.punctuate "," $ map prettyQuant ns
          in
          ns' <+> t'

ppSchema :: Schema -> Text
ppSchema ty =
    PPS.renderText PPS.defaultOpts $ prettySchema ty

prettyNamedType :: NamedType -> PPS.Doc
prettyNamedType ty = case ty of
    ConcreteType ty' -> prettyType ty'
    AbstractType kind -> "<opaque " <> PP.pretty (ppKind kind) <> ">"

{- not used
ppNamedType :: NamedType -> Text
ppNamedType ty =
    PPS.renderText PPS.defaultOpts $ prettyNamedType ty
-}

prettyExpr :: Expr -> PPS.Doc
prettyExpr expr0 = case expr0 of
    Bool _ b   -> PP.viaShow b
    String _ s -> PP.dquotes (PP.pretty s)
    Int _ i    -> PP.pretty i
    Code _ s   -> PP.braces $ PP.braces $ PP.pretty s
    CType _ s  -> PP.braces $ "|" <> PP.pretty s <> "|"
    Array _ xs -> PP.brackets $ PP.fillSep $ PP.punctuate "," (map prettyExpr xs)
    Block _ (stmts, lastexpr) ->
        let stmts' = map prettyStmt stmts
            lastexpr' = prettyExpr lastexpr <> ";"
            body = PP.align $ PP.vsep (stmts' ++ [lastexpr'])
            -- You would think this could unconditionally be `PP.nest 3
            -- body`. But that doesn't work. If you use `PP.nest`,
            -- `PP.group` throws away the indentation entirely (whether
            -- or not it groups successfully); if you use `PP.indent`
            -- instead, it indents when not grouped, but also generates
            -- spaces when grouped. Explicit use of `PP.flatAlt` seems
            -- to fix this, but ew. And you'd think this would work by
            -- default, since folding small blocks to single lines is
            -- one of the most basic prettyprinting operations.
            body' = PP.flatAlt (PP.indent 3 body) body
        in
        PP.group $ "do" <+> PP.braces (PP.line <> body' <> PP.line)
    Tuple _ exprs ->
        PP.parens $ PP.fillSep $ PP.punctuate "," (map prettyExpr exprs)
    Record _ members ->
        let prettyMember (name, value) =
                PP.pretty name <+> "=" <+> prettyExpr value
            members' = map prettyMember $ Map.assocs members
            body = PP.sep $ PP.punctuate PP.comma members'
            body' = PP.flatAlt (PP.indent 3 body) body
        in
        PP.group $ PP.braces (PP.line <> body' <> PP.line)
    Index _ _ _ ->
        panic "prettyExpr" ["There is no concrete syntax for AST node 'Index'"]
    Lookup _ expr name ->
        let expr' = prettyExpr expr
            name' = PP.pretty name
        in
        expr' <> PP.dot <> name'
    TLookup _ expr n ->
        let expr' = prettyExpr expr
            n' = PP.viaShow n
        in      
        expr' <> PP.dot <> n'
    Var _ name ->
        PP.pretty name
    Lambda _ _mname pat expr ->
        let pat' = prettyPattern pat
            expr' = prettyExpr expr
            line1 = "\\" <+> pat' <+> "->"
            line2 = PP.flatAlt (PP.indent 3 expr') expr'
        in
        PP.group $ line1 <> PP.line <> line2
    Application _ f arg ->
        -- XXX FIXME: use precedence to minimize parentheses
        let f' = prettyExpr f
            arg' = prettyExpr arg
        in
        PP.parens f' <+> arg'
    Let _ (NonRecursive decl) expr ->
        let decl' = prettyDef decl
            expr' = prettyExpr expr
            -- Break after the "in" when it doesn't fit. Maybe I've
            -- gotten too used to reading OCaml?
            line1 = "let" <+> decl' <+> "in"
            line2 = expr'
        in
        PP.group $ line1 <> PP.line <> line2
    Let _ (Recursive decls) expr ->
        let decls' = map prettyDef decls
            expr' = prettyExpr expr
            decls'' = case decls' of
              [] -> []  -- (not actually possible)
              first : rest -> ("rec" <+> first) : map (\d -> "and" <+> d) rest
        in
        PP.vsep decls'' <> PP.hardline <> "in" <> PP.hardline <> PP.nest 3 expr'
    TSig _ expr ty ->
        let expr' = prettyExpr expr
            ty' =  prettyType ty
        in
        PP.parens (expr' <+> PP.colon <+> ty')
    IfThenElse _ e1 e2 e3 ->
        let e1' = prettyExpr e1
            e2' = prettyExpr e2
            e3' = prettyExpr e3
            -- plan for four lines
            line1 = "if" <+> e1' <+> "then"
            line2 = PP.flatAlt (PP.indent 3 e2') e2'
            line3 = "else"
            line4 = PP.flatAlt (PP.indent 3 e3') e3'
        in
        -- Use PP.sep so it'll fold to one line if it fits
        PP.group $ PP.sep [line1, line2, line3, line4]

ppExpr :: Expr -> Text
ppExpr e =
    PPS.renderText PPS.defaultOpts $ prettyExpr e

prettyPattern :: Pattern -> PPS.Doc
prettyPattern pat =
    let prettyArg name' mty = case mty of
          Nothing -> name'
          Just ty -> PP.parens $ name' <+> PP.colon <+> prettyType ty
    in   
    case pat of
        PWild _ mty ->
          prettyArg "_" mty
        PVar _ _ name mty ->
          prettyArg (PP.pretty name) mty
        PTuple _ pats ->
          PP.parens $ PP.fillSep $ PP.punctuate "," $ map prettyPattern pats

ppPattern :: Pattern -> Text
ppPattern pat =
  PPS.renderText PPS.defaultOpts $ prettyPattern pat

prettyStmt :: Stmt -> PPS.Doc
prettyStmt s0 = case s0 of
    StmtBind _ (PWild _ _ty) expr ->
       -- Drop the _, even if it has an explicit type
       prettyExpr expr <> ";"
    StmtBind _ pat expr ->
       let pat' = prettyPattern pat
           expr' = prettyExpr expr
           line1 = pat' <+> "<-"
           line2 = PP.flatAlt (PP.indent 3 expr') expr'
       in
       PP.group $ line1 <> PP.line <> line2 <> ";"
    StmtLet _ rebindable (NonRecursive decl) ->
       let header = case rebindable of
             RebindableVar -> "let rebindable"
             ReadOnlyVar -> "let"
           decl' = prettyDef decl
       in
       PP.group $ header <+> decl' <> ";"
    StmtLet _ _ (Recursive decls) ->
       let decls' = map prettyDef decls
           decls'' = case decls' of
             [] -> []  -- (not actually possible)
             first : rest -> ("rec" <+> first) : map (\d -> "and" <+> d) rest
       in
       PP.vsep decls'' <> ";"
    StmtCode _ _ code ->
       let code' = PP.braces $ PP.braces $ PP.pretty code in
       "let" <+> code' <> ";"
    StmtImport _ imp ->
       let prettyNames names =
               let prettyIdent name = PP.pretty $ P.identText name
                   names' = PP.fillSep $ {- PP.punctuate "," $ -} map prettyIdent names
                   long = PP.parens $ PP.line <> PP.indent 3 names' <> PP.line
                   short = PP.parens names'
               in
               PP.flatAlt long short
           prettyModName mn =
               PP.pretty (intercalate "::" (P.modNameChunks mn))
           module' = case iModule imp of
               Left filepath -> PP.dquotes $ PP.pretty filepath
               Right modName -> prettyModName modName
           as' = case iAs imp of
               Nothing -> PP.emptyDoc
               Just modName -> " as" <+> prettyModName modName
           spec' = case iSpec imp of
               Nothing -> PP.emptyDoc
               Just (P.Hiding names) ->
                    " hiding" <+> prettyNames names
               Just (P.Only names) ->
                    " " <> prettyNames names
       in
       PP.group $ "import" <+> module' <> as' <> spec' <> ";"
    StmtInclude _ name once ->
        let inc = if once then "include_once" else "include"
            name' = PP.dquotes $ PP.pretty name
        in
        inc <+> name' <> ";"
    StmtTypedef _ _ name ty ->
       let name' = PP.pretty name
           ty' = prettyType ty
       in
       PP.group $ "typedef" <+> name' <+> "=" <+> ty' <> ";"
    StmtPushdir _ dir ->
       ".pushdir" <+> PP.pretty dir <> ";"
    StmtPopdir _ ->
       ".popdir;"

prettyDef :: Decl -> PPS.Doc
prettyDef (Decl _ pat0 _ def) =
   let dissectLambda :: Expr -> ([Pattern], Expr)
       dissectLambda = \case
          Lambda _pos _name pat (dissectLambda -> (pats, expr)) -> (pat : pats, expr)
          expr -> ([], expr)
       (args, body) = dissectLambda def
       pats' = PP.align $ PP.sep $ map prettyPattern (pat0 : args)
       body' = prettyExpr body
       body'' = PP.flatAlt (PP.indent 3 body') body'
   in
   pats' <+> "=" <> PP.line <> body''

prettyWholeModule :: [Stmt] -> PPS.Doc
prettyWholeModule stmts = (PP.vsep $ map prettyStmt stmts) <> PP.line


------------------------------------------------------------
-- Type formers

tUnit :: Pos -> Type
tUnit pos = tTuple pos []

tTuple :: Pos -> [Type] -> Type
tTuple pos ts = TyCon pos (TupleCon $ fromIntegral $ length ts) ts

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

tInt :: Pos -> Type
tInt pos = TyCon pos IntCon []

tBlock :: Pos -> Type -> Type -> Type
tBlock pos c t = TyCon pos BlockCon [c,t]

tAIG :: Pos -> Type
tAIG pos = TyCon pos AIGCon []

tCFG :: Pos -> Type
tCFG pos = TyCon pos CFGCon []

tJVMSpec :: Pos -> Type
tJVMSpec pos = TyCon pos JVMSpecCon []

tLLVMSpec :: Pos -> Type
tLLVMSpec pos = TyCon pos LLVMSpecCon []

tMIRSpec :: Pos -> Type
tMIRSpec pos = TyCon pos MIRSpecCon []

tContext :: Pos -> Context -> Type
tContext pos c = TyCon pos (ContextCon c) []

tRecord :: Pos -> [(Name, Type)] -> Type
tRecord pos fields = TyRecord pos (Map.fromList fields)

tVar :: Pos -> Name -> Type
tVar pos n = TyVar pos n

tMono :: Type -> Schema
tMono = Forall []

tForall :: [(Pos, Name)] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t


------------------------------------------------------------
-- Type Classifiers

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
