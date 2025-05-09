{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : SAWCore.Grammar
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Grammar
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

import SAWCore.UntypedAST
import SAWCore.Module (DefQualifier(..))
import SAWCore.Lexer

}

%name parseSAW2 Module
%name parseSAWTerm2 Term

%tokentype { PosPair Token }
%monad { Parser }
%lexer { lexer >>= } { PosPair _ TEnd }
%error { parseError }
%expect 0

%token
  '#'     { PosPair _ (TKey "#") }
  '->'    { PosPair _ (TKey "->") }
  '='     { PosPair _ (TKey "=") }
  '\\'    { PosPair _ (TKey "\\") }
  ';'     { PosPair _ (TKey ";") }
  ':'     { PosPair _ (TKey ":") }
  ','     { PosPair _ (TKey ",") }
  '.'     { PosPair _ (TKey ".") }
  '('     { PosPair _ (TKey "(") }
  ')'     { PosPair _ (TKey ")") }
  '['     { PosPair _ (TKey "[") }
  ']'     { PosPair _ (TKey "]") }
  '{'     { PosPair _ (TKey "{") }
  '}'     { PosPair _ (TKey "}") }
  '|'     { PosPair _ (TKey "|") }
  '*'     { PosPair _ (TKey "*") }
  'data'      { PosPair _ (TKey "data") }
  'hiding'    { PosPair _ (TKey "hiding") }
  'import'    { PosPair _ (TKey "import") }
  'module'    { PosPair _ (TKey "module") }
  'sort'      { PosPair _ (TKey "sort") }
  'isort'     { PosPair _ (TKey "isort") }
  'qsort'     { PosPair _ (TKey "qsort") }
  'qisort'    { PosPair _ (TKey "qisort") }
  'Prop'      { PosPair _ (TKey "Prop") }
  'where'     { PosPair _ (TKey "where") }
  'axiom'     { PosPair _ (TKey "axiom") }
  'primitive' { PosPair _ (TKey "primitive") }
  'injectCode' { PosPair _ (TKey "injectCode") }

  nat      { PosPair _ (TNat _) }
  bvlit    { PosPair _ (TBitvector _) }
  '_'      { PosPair _ (TIdent "_") }
  ident    { PosPair _ (TIdent _) }
  identrec { PosPair _ (TRecursor _) }
  string   { PosPair _ (TString _) }

%%

Module :: { Module }
Module : 'module' ModuleName 'where' list(Import) list(SAWDecl) { Module $2 $4 $5 }

ModuleName :: { PosPair ModuleName }
ModuleName : sepBy (Ident, '.') { mkPosModuleName $1 }

Import :: { Import }
Import : 'import' ModuleName opt(ModuleImports) ';'
          { Import $2 $3 }

SAWDecl :: { Decl }
SAWDecl : 'data' Ident VarCtx ':' LTerm 'where' '{' list(CtorDecl) '}'
             { DataDecl $2 $3 $5 $8 }
        | 'primitive' Ident ':' LTerm ';'
             { TypeDecl PrimQualifier $2 $4 }
        | 'axiom' Ident ':' LTerm ';'
             { TypeDecl AxiomQualifier $2 $4 }
        | Ident ':' LTerm opt(DefBody) ';' { maybe (TypeDecl NoQualifier $1 $3)
                                                   (TypedDef $1 [] $3) $4 }
        | Ident list(TermVar) '=' LTerm ';' { TermDef $1 $2 $4 }
        | Ident VarCtxItem VarCtx ':' LTerm '=' LTerm ';' { TypedDef $1 ($2 ++ $3) $5 $7 }
        | 'injectCode' string string ';'
	     { InjectCodeDecl (Text.pack (tokString (val $2))) (Text.pack (tokString (val $3))) }

DefBody :: { Term }
DefBody : '=' LTerm { $2 }

ModuleImports :: { ImportConstraint }
ModuleImports : 'hiding' ImportNames { HidingImports $2 }
              | ImportNames { SpecificImports $1 }

ImportNames :: { [String] }
ImportNames : '(' sepBy(ImportName, ',') ')' { $2 }

ImportName :: { String }
ImportName : ident { tokIdent $ val $1 }

TermVar :: { TermVar }
TermVar
  : Ident { TermVar $1 }
  | '_' { UnusedVar (pos $1) }

-- A context of variables which may or may not be typed
DefVarCtx :: { [(TermVar, Maybe Term)] }
DefVarCtx : list(DefVarCtxItem) { concat $1 }

DefVarCtxItem :: { [(TermVar, Maybe Term)] }
DefVarCtxItem : TermVar { [($1, Nothing)] }
              | '(' list(TermVar) ':'  LTerm ')'
                { map (\var -> (var, Just $4)) $2 }

-- A context of variables, all of which must be typed; i.e., a list syntactic
-- elements of the form (x y z :: tp) (x2 y3 :: tp2) ...
VarCtx :: { [(TermVar, Term)] }
VarCtx : list(VarCtxItem) { concat $1 }

VarCtxItem :: { [(TermVar, Term)] }
VarCtxItem : '(' list(TermVar) ':' LTerm ')' { map (\var -> (var,$4)) $2 }

-- Constructor declaration of the form "c (x1 x2 :: tp1) ... (z1 :: tpn) :: tp"
CtorDecl :: { CtorDecl }
CtorDecl : Ident VarCtx ':' LTerm ';' { Ctor $1 $2 $4 }

Term :: { Term }
Term : LTerm { $1 }
     | LTerm ':' LTerm { TypeConstraint $1 (pos $2) $3 }

-- Term with uses of pi and lambda, but no type ascriptions
LTerm :: { Term }
LTerm : ProdTerm                         { $1 }
      | PiArg '->' LTerm                 { Pi (pos $2) $1 $3 }
      | '\\' VarCtx '->' LTerm           { Lambda (pos $1) $2 $4 }

PiArg :: { [(TermVar, Term)] }
PiArg : ProdTerm { mkPiArg $1 }

-- Term formed from infix product type operator (right-associative)
ProdTerm :: { Term }
ProdTerm
  : AppTerm                        { $1 }
  | AppTerm '*' ProdTerm           { PairType (pos $1) $1 $3 }

-- Term formed from applications of atomic expressions
AppTerm :: { Term }
AppTerm : AtomTerm                 { $1 }
        | AppTerm AtomTerm         { App $1 $2 }

AtomTerm :: { Term }
AtomTerm
  : nat                          { NatLit (pos $1) (tokNat (val $1)) }
  | bvlit                        { BVLit (pos $1) (tokBits (val $1)) }
  | string                       { StringLit (pos $1) (Text.pack (tokString (val $1))) }
  | Ident                        { Name $1 }
  | IdentRec                     { Recursor Nothing $1 }
  | 'Prop'                       { Sort (pos $1) propSort noFlags }
  | Sort nat                     { Sort (pos $1) (mkSort (tokNat (val $2))) (val $1) }
  | AtomTerm '.' Ident           { RecordProj $1 (val $3) }
  | AtomTerm '.' IdentRec        {% parseRecursorProj $1 $3 }
  | AtomTerm '.' nat             {% parseTupleSelector $1 (fmap tokNat $3) }
  | '(' sepBy(Term, ',') ')'     { mkTupleValue (pos $1) $2 }
  | '#' '(' sepBy(Term, ',') ')'       { mkTupleType (pos $1) $3 }
  |     '[' sepBy(Term, ',') ']'       { VecLit (pos $1) $2 }
  |     '{' sepBy(FieldValue, ',') '}' { RecordValue (pos $1) $2 }
  | '#' '{' sepBy(FieldType, ',') '}'  { RecordType  (pos $1) $3 }
  | AtomTerm '.' '(' nat ')'           {% mkTupleProj $1 (tokNat (val $4)) }

Ident :: { PosPair Text }
Ident : ident { fmap (Text.pack . tokIdent) $1 }

IdentRec :: { PosPair Text }
IdentRec : identrec { fmap (Text.pack . tokRecursor) $1 }

Sort :: { PosPair SortFlags }
Sort : 'sort'   { fmap (const $ SortFlags False False) $1 }
     | 'isort'  { fmap (const $ SortFlags True  False) $1 }
     | 'qsort'  { fmap (const $ SortFlags False True ) $1 }
     | 'qisort' { fmap (const $ SortFlags True  True ) $1 }

FieldValue :: { (PosPair FieldName, Term) }
FieldValue : Ident '=' Term { ($1, $3) }

FieldType :: { (PosPair FieldName, Term) }
FieldType : Ident ':' LTerm { ($1, $3) }

opt(q) :: { Maybe q }
  : { Nothing }
  | q { Just $1 }

-- Two elements p and r separated by q and terminated by s
sepPair(p,q,r,s) :: { (p,r) }
  : p q r s { ($1,$3) }

-- A possibly-empty list of p's separated by q.
sepBy(p,q) :: { [p] }
  : {- empty -} { [] }
  | sepBy1(p,q) { $1 }

-- A possibly-empty list of p's separated by q.
sepBy1(p,q) :: { [p] }
  : rsepBy1(p,q) { reverse $1 }

rsepBy1(p,q) :: { [p] }
  : p { [$1] }
  | rsepBy1(p,q) q p { $3 : $1 }

-- A list of 0 or more p's, terminated by q's
list(p) :: { [p] }
  : {- empty -} { [] }
  | rlist1(p) { reverse $1 }

-- A list of 0 or more p's, terminated by q's
list1(p) :: { [p] }
  : rlist1(p) { reverse $1 }

-- A reversed list of at least 1 p's
rlist1(p) :: { [p] }
  : p           { [$1]    }
  | rlist1(p) p { $2 : $1 }

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

parseSAWTerm :: FilePath -> FilePath -> LText.Text -> Either (PosPair ParseError) Term
parseSAWTerm = runParser parseSAWTerm2

parseError :: PosPair Token -> Parser a
parseError pt = addError (pos pt) (UnexpectedToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

-- Try to parse an expression as a list of identifiers
exprAsIdentList :: Term -> Maybe [TermVar]
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
mkPiArg :: Term -> [(TermVar, Term)]
mkPiArg (TypeConstraint (exprAsIdentList -> Just xs) _ t) =
  map (\x -> (x, t)) xs
mkPiArg lhs = [(UnusedVar (pos lhs), lhs)]

-- | Parse a tuple projection of the form @t.(1)@ or @t.(2)@
mkTupleProj :: Term -> Natural -> Parser Term
mkTupleProj t 1 = return $ PairLeft t
mkTupleProj t 2 = return $ PairRight t
mkTupleProj t _ =
  do addParseError (pos t) "Projections must be either .(1) or .(2)"
     return (badTerm (pos t))

-- | Parse a term as a dotted list of strings
parseModuleName :: Term -> Maybe [Text]
parseModuleName (RecordProj t fname) = (++ [fname]) <$> parseModuleName t
parseModuleName _ = Nothing

-- | Parse a qualified recursor @M1.M2...Mn.d#rec@
parseRecursorProj :: Term -> PosPair Text -> Parser Term
parseRecursorProj (parseModuleName -> Just mnm) i =
  return $ Recursor (Just $ mkModuleName mnm) i
parseRecursorProj t _ =
  do addParseError (pos t) "Malformed recursor projection"
     return (badTerm (pos t))

parseTupleSelector :: Term -> PosPair Natural -> Parser Term
parseTupleSelector t i =
  if val i >= 1 then return (mkTupleSelector t (val i)) else
    do addParseError (pos t) "non-positive tuple projection index"
       return (badTerm (pos t))

-- | Create a module name given a list of strings with the top-most
-- module name given first.
mkPosModuleName :: [PosPair Text] -> PosPair ModuleName
mkPosModuleName [] = error "internal: Unexpected empty module name"
mkPosModuleName l = PosPair p (mkModuleName nms)
  where nms = fmap val l
        p = pos (last l)
}
