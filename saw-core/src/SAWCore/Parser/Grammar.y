{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : SAWCore.Parser.Grammar
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Parser.Grammar
  ( parseSAW
  , parseSAWTerm
  ) where

import Control.Applicative ((<$>))
import Control.Monad ()
import Control.Monad.State (State, get, gets, modify, put, runState, evalState)
import Control.Monad.Except (ExceptT, throwError, runExceptT)
import qualified Data.ByteString.Lazy.UTF8 as B
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LText
import Data.Traversable
import Data.Word
import Numeric.Natural
import System.Directory (getCurrentDirectory)

import Prelude hiding (mapM, sequence)

import SAWCore.Panic
import SAWCore.Parser.AST
import SAWCore.Parser.Lexer

}

-- edit width for this file is 100:
----------------------------------------------------------------------------------------------------

%name parseSAW2 Module
%name parseSAWTerm2 Term

%tokentype { PosPair Token }
%monad { Parser }
%lexer { lexer >>= } { PosPair _ TEnd }
%error { parseError }
%expect 0

%token
  '#'           { PosPair _ (TKey "#") }
  '->'          { PosPair _ (TKey "->") }
  '='           { PosPair _ (TKey "=") }
  '\\'          { PosPair _ (TKey "\\") }
  ';'           { PosPair _ (TKey ";") }
  ':'           { PosPair _ (TKey ":") }
  ','           { PosPair _ (TKey ",") }
  '.'           { PosPair _ (TKey ".") }
  '('           { PosPair _ (TKey "(") }
  ')'           { PosPair _ (TKey ")") }
  '['           { PosPair _ (TKey "[") }
  ']'           { PosPair _ (TKey "]") }
  '{'           { PosPair _ (TKey "{") }
  '}'           { PosPair _ (TKey "}") }
  '|'           { PosPair _ (TKey "|") }
  '*'           { PosPair _ (TKey "*") }
  'data'        { PosPair _ (TKey "data") }
  'hiding'      { PosPair _ (TKey "hiding") }
  'import'      { PosPair _ (TKey "import") }
  'module'      { PosPair _ (TKey "module") }
  'sort'        { PosPair _ (TKey "sort") }
  'isort'       { PosPair _ (TKey "isort") }
  'qsort'       { PosPair _ (TKey "qsort") }
  'qisort'      { PosPair _ (TKey "qisort") }
  'Prop'        { PosPair _ (TKey "Prop") }
  'where'       { PosPair _ (TKey "where") }
  'axiom'       { PosPair _ (TKey "axiom") }
  'primitive'   { PosPair _ (TKey "primitive") }
  'injectCode'  { PosPair _ (TKey "injectCode") }
  'let'         { PosPair _ (TKey "let") }
  'in'          { PosPair _ (TKey "in") }

  nat           { PosPair _ (TNat _) }
  bvlit         { PosPair _ (TBitvector _) }
  '_'           { PosPair _ (TIdent "_") }
  rawident      { PosPair _ (TIdent _) }
  rawidentrec   { PosPair _ (TRecursor _) }
  rawidentind   { PosPair _ (TInductor _) }
  string        { PosPair _ (TString _) }

%%

-- whole module
Module :: { Module } :
  'module' ModuleName 'where' list(Import) list(SAWDecl)        { Module $2 $4 $5 }

-- possibly-qualified module name
ModuleName :: { PosPair ModuleName } :
  sepBy1 (Ident, '.')                                           { mkPosModuleName $1 }

-- import directive
Import :: { Import } :
  'import' ModuleName opt(ModuleImports) ';'                    { Import $2 $3 }

-- top-level declaration
SAWDecl :: { Decl } :
    'data' Ident VarCtx ':' LTerm 'where' '{' list(CtorDecl) '}' { DataDecl $2 $3 $5 $8 }
  | 'primitive' Ident ':' LTerm ';'                             { mkPrimitive $2 $4 }
  | 'axiom' Ident ':' LTerm ';'                                 { mkAxiom $2 $4 }
  | Ident ':' LTerm ';'                                         { mkNoQual $1 $3 }
  | Ident ':' LTerm '=' LTerm ';'                               { TypedDef $1 [] $3 $5 }
  | Ident list(TermVar) '=' LTerm ';'                           { TermDef $1 $2 $4 }
  | Ident VarCtxItem VarCtx ':' LTerm '=' LTerm ';'             { TypedDef $1 ($2 ++ $3) $5 $7 }
  | 'injectCode' string string ';'                              { mkInject $2 $3 }

-- symbol import list in an import directive
ModuleImports :: { ImportConstraint } :
    'hiding' ImportNames                        { HidingImports $2 }
  | ImportNames                                 { SpecificImports $1 }

-- list of imported symbols
ImportNames :: { [String] } :
  '(' sepBy(ImportName, ',') ')'                { $2 }

-- single imported symbol
ImportName :: { String } :
  rawident                                      { tokIdent $ val $1 }

-- A single parameter
TermVar :: { UTermVar } :
    Ident                                       { TermVar $1 }
  | '_'                                         { UnusedVar (pos $1) }

-- A context of variables (parameter list) which may or may not be typed
--
-- XXX: this is unused. Is it intended that declarations can only have
-- either all typed or all untyped parameters, or was it a hack to avoid
-- some grammar problem that's probably fixable?
DefVarCtx :: { [(UTermVar, Maybe UTerm)] } :
  list(DefVarCtxItem)                           { concat $1 }

-- Single entry in a parameter list: either a single variable or
-- possibly several sharing a type. XXX: is it intended that the list
-- can be empty?
DefVarCtxItem :: { [(UTermVar, Maybe UTerm)] } :
    TermVar                                     { [($1, Nothing)] }
  | '(' list(TermVar) ':' LTerm ')'             { map (\var -> (var, Just $4)) $2 }

-- A context of variables (parameter list), all of which must be
-- typed; i.e., a list of syntactic elements of the form
--    (x y z :: tp) (x2 y3 :: tp2) ...
VarCtx :: { [(UTermVar, UTerm)] } :
  list(VarCtxItem)                              { concat $1 }

-- A single entry in a parameter list: several variables that share a type.
-- XXX: is it intended that the list can be empty?
VarCtxItem :: { [(UTermVar, UTerm)] } :
  '(' list(TermVar) ':' LTerm ')'               { map (\var -> (var, $4)) $2 }

-- Constructor declaration of the form "c (x1 x2 :: tp1) ... (z1 :: tpn) :: tp"
CtorDecl :: { CtorDecl } :
  Ident VarCtx ':' LTerm ';'                    { Ctor $1 $2 $4 }

LetBind :: { (UTermVar, UTerm) } :
  TermVar '=' LTerm ';'                         { ($1,$3) }

-- Full term (possibly including a type annotation)
Term :: { UTerm } :
    LTerm                                       { $1 }
  | LTerm ':' LTerm                             { TypeConstraint $1 (pos $2) $3 }

-- Term with uses of pi and lambda, but no type ascriptions
LTerm :: { UTerm } :
    ProdTerm                                    { $1 }
  | ProdTerm '->' LTerm                         { Pi (pos $2) (mkPiArg $1) $3 }
  | '\\' VarCtx '->' LTerm                      { Lambda (pos $1) $2 $4 }
  | 'let' '{' list(LetBind) '}' 'in' LTerm      { Let (pos $1) $3 $6 }

-- Term formed from infix product type operator (right-associative)
ProdTerm :: { UTerm } :
    AppTerm                                     { $1 }
  | AppTerm '*' ProdTerm                        { PairType (pos $1) $1 $3 }

-- Term formed from applications of atomic expressions
AppTerm :: { UTerm } :
    AtomTerm                                    { $1 }
  | AppTerm AtomTerm                            { App $1 $2 }

-- Atomic (base) term
AtomTerm :: { UTerm } :
    nat                                         { NatLit (pos $1) (tokNat (val $1)) }
  | bvlit                                       { BVLit (pos $1) (tokBits (val $1)) }
  | string                                      { mkString $1 }
  | Ident                                       { Name $1 }
  | IdentRec                                    { Recursor (fmap fst $1) (mkSort (snd (val $1))) }
  | IdentInd                                    { Recursor $1 propSort }
  | 'Prop'                                      { Sort (pos $1) propSort noFlags }
  | Sort nat                                   { Sort (pos $1) (mkSort (tokNat (val $2))) (val $1) }
  | AtomTerm '.' Ident                          { RecordProj $1 (val $3) }
  | AtomTerm '.' nat                            {% parseTupleSelector $1 (fmap tokNat $3) }
  | '(' sepBy(Term, ',') ')'                    { mkTupleValue (pos $1) $2 }
  | '#' '(' sepBy(Term, ',') ')'                { mkTupleType (pos $1) $3 }
  |     '[' sepBy(Term, ',') ']'                { VecLit (pos $1) $2 }
  |     '{' sepBy(FieldValue, ',') '}'          { RecordValue (pos $1) $2 }
  | '#' '{' sepBy(FieldType, ',') '}'           { RecordType  (pos $1) $3 }
  | AtomTerm '.' '(' nat ')'                    {% mkTupleProj $1 (tokNat (val $4)) }

-- Identifier (wrapper to extract the text)
Ident :: { PosPair Text } :
  rawident                                      { fmap (Text.pack . tokIdent) $1 }

-- Recursor identifier (wrapper to extract the text)
IdentRec :: { PosPair (Text, Natural) } :
  rawidentrec                                   { fmap ((\(s, n) -> (Text.pack s, n)) . tokRecursor) $1 }

-- Inductor identifier
IdentInd :: { PosPair Text } :
  rawidentind                                   { fmap (Text.pack . tokInductor) $1 }

-- Sort keywords
Sort :: { PosPair SortFlags } :
    'sort'                                      { fmap (const $ SortFlags False False) $1 }
  | 'isort'                                     { fmap (const $ SortFlags True  False) $1 }
  | 'qsort'                                     { fmap (const $ SortFlags False True ) $1 }
  | 'qisort'                                    { fmap (const $ SortFlags True  True ) $1 }

-- Value for a record field
FieldValue :: { (PosPair FieldName, UTerm) } :
  Ident '=' Term                                { ($1, $3) }

-- Type for a record field
FieldType :: { (PosPair FieldName, UTerm) } :
  Ident ':' LTerm                               { ($1, $3) }


------------------------------------------------------------
-- Utility productions

-- optional
opt(q) :: { Maybe q } :
    {- empty -}                                 { Nothing }
  | q                                           { Just $1 }

-- Two elements p and r separated by q and terminated by s
sepPair(p, q, r, s) :: { (p, r) } :
  p q r s                                       { ($1, $3) }

-- A possibly-empty list of p's separated by q.
sepBy(p, q) :: { [p] } :
    {- empty -}                                 { [] }
  | sepBy1(p, q)                                { $1 }

-- A non-empty list of p's separated by q.
sepBy1(p, q) :: { [p] } :
  rsepBy1(p, q)                                 { reverse $1 }

-- A non-empty list of p's separated by q, constructed in reverse order.
rsepBy1(p, q) :: { [p] } :
    p                                           { [$1] }
  | rsepBy1(p, q) q p                           { $3 : $1 }

-- A list of 0 or more p's.
list(p) :: { [p] } :
    {- empty -}                                 { [] }
  | rlist1(p)                                   { reverse $1 }

-- A list of 1 or more p's.
list1(p) :: { [p] } :
  rlist1(p)                                     { reverse $1 }

-- A list of 1 or more p's, constructed in reverse order.
rlist1(p) :: { [p] } :
    p                                           { [$1] }
  | rlist1(p) p                                 { $2 : $1 }

{

data ParseError
  = UnexpectedLex Text
  | UnexpectedToken Token
  | ParseError String
  deriving (Show)

newtype Parser a = Parser { _unParser :: ExceptT (PosPair ParseError) (State LexerState) a }
  deriving (Applicative, Functor, Monad)

addError :: Pos -> ParseError -> Parser a
addError p err = Parser $ throwError (PosPair p err)

parsePos :: Parser Pos
parsePos = Parser $ gets pos

lexer :: Parser (PosPair Token)
lexer = do
  inp <- Parser get
  let (inp', errors, result) = lexSAWCore inp
  Parser $ put inp'
  let issue (pos, msg) = case msg of
        InvalidInput chars -> addError pos $ UnexpectedLex chars
        UnclosedComment -> addError pos $ ParseError "Unclosed Comment"
        MissingEOL ->
          -- XXX: this should be a warning but we have no such ability here yet
          --addWarning pos $ "No newline at end of file"
          return ()
  -- XXX: this can only actually throw one error. Fix this up when we
  -- clean out the error printing infrastructure.
  mapM issue errors
  return result

-- | Run parser given a directory for the base (used for making pathname relative),
-- bytestring to parse, and parser to run.
runParser :: Parser a -> FilePath -> FilePath -> LText.Text -> Either (PosPair ParseError) a
runParser (Parser m) base path txt = evalState (runExceptT m) initState
  where initState = initialLexerState base path txt

parseSAW :: FilePath -> FilePath -> LText.Text -> Either (PosPair ParseError) Module
parseSAW = runParser parseSAW2

parseSAWTerm :: FilePath -> FilePath -> LText.Text -> Either (PosPair ParseError) UTerm
parseSAWTerm = runParser parseSAWTerm2

parseError :: PosPair Token -> Parser a
parseError pt = addError (pos pt) (UnexpectedToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

-- Try to parse an expression as a list of identifiers
exprAsIdentList :: UTerm -> Maybe [UTermVar]
exprAsIdentList (Name x) = return [TermVar x]
exprAsIdentList (App expr (Name x)) =
  (++ [TermVar x]) <$> exprAsIdentList expr
exprAsIdentList _ = Nothing

-- | Pi expressions should have one of the forms:
--
-- * '(' list(Ident) ':' LTerm ')' '->' LTerm
-- * AppTerm '->' LTerm
--
-- This function takes in a term for the LHS and tests if it is of the first
-- form, or, if not, converts the second form into the first by making a single
-- "unused" variable with the name "_"
mkPiArg :: UTerm -> [(UTermVar, UTerm)]
mkPiArg (TypeConstraint (exprAsIdentList -> Just xs) _ t) =
  map (\x -> (x, t)) xs
mkPiArg lhs = [(UnusedVar (pos lhs), lhs)]

-- | Parse a tuple projection of the form @t.(1)@ or @t.(2)@
mkTupleProj :: UTerm -> Natural -> Parser UTerm
mkTupleProj t 1 = return $ PairLeft t
mkTupleProj t 2 = return $ PairRight t
mkTupleProj t _ =
  do addParseError (pos t) "Projections must be either .(1) or .(2)"
     return (badTerm (pos t))

parseTupleSelector :: UTerm -> PosPair Natural -> Parser UTerm
parseTupleSelector t i =
  if val i >= 1 then return (mkTupleSelector t (val i)) else
    do addParseError (pos t) "non-positive tuple projection index"
       return (badTerm (pos t))

-- | Create a module name given a list of strings with the top-most
-- module name given first.
--
-- The empty list case is impossible according to the grammar.
mkPosModuleName :: [PosPair Text] -> PosPair ModuleName
mkPosModuleName [] = panic "mkPosModuleName" ["Empty module name"]
mkPosModuleName l = PosPair p (mkModuleName nms)
  where nms = fmap val l
        p = pos (last l)

mkPrimitive :: PosPair Text -> UTerm -> Decl
mkPrimitive x ty = TypeDecl PrimQualifier x ty

mkAxiom :: PosPair Text -> UTerm -> Decl
mkAxiom x ty = TypeDecl AxiomQualifier x ty

mkNoQual :: PosPair Text -> UTerm -> Decl
mkNoQual x ty = TypeDecl NoQualifier x ty

mkInject :: PosPair Token -> PosPair Token -> Decl
mkInject a b =
  let fixup t = Text.pack (tokString (val t)) in
  InjectCodeDecl (fixup a) (fixup b)

mkString :: PosPair Token -> UTerm
mkString t = StringLit (pos t) (Text.pack (tokString (val t)))

}
