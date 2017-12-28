{
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

{- |
Module      : Verifier.SAW.Grammar
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Grammar
  ( Decl(..)
  , Term(..)
  , parseSAW
  , parseSAWTerm
  , lexer
  ) where

import Control.Applicative ((<$>))
import Control.Monad ()
import Control.Monad.State (State, get, gets, modify, runState)
import qualified Data.ByteString.Lazy.UTF8 as B
import Data.Maybe (isJust)
import Data.Traversable
import Data.Word
import System.Directory (getCurrentDirectory)

import Prelude hiding (mapM, sequence)

import Verifier.SAW.UntypedAST
import Verifier.SAW.Lexer

}

%name parseSAW2 Module
%name parseSAWTerm2 Term

%tokentype { PosPair Token }
%monad { Parser }
%lexer { lexer } { PosPair _ TEnd }
%error { parseError }
%expect 0

%token
  '#'     { PosPair _ (TKey "#") }
  '->'    { PosPair _ (TKey "->") }
  '='     { PosPair _ (TKey "=") }
  '\\'    { PosPair _ (TKey "\\") }
  ';'     { PosPair _ (TKey ";") }
  '::'    { PosPair _ (TKey "::") }
  ','     { PosPair _ (TKey ",") }
  '.'     { PosPair _ (TKey ".") }
  '..'    { PosPair _ (TKey "..") }
  '?'     { PosPair _ (TKey "?") }
  '??'    { PosPair _ (TKey "??") }
  '???'   { PosPair _ (TKey "???") }
  '('     { PosPair _ (TKey "(") }
  ')'     { PosPair _ (TKey ")") }
  '['     { PosPair _ (TKey "[") }
  ']'     { PosPair _ (TKey "]") }
  '{'     { PosPair _ (TKey "{") }
  '}'     { PosPair _ (TKey "}") }
  '|'     { PosPair _ (TKey "|") }
  'as'        { PosPair _ (TKey "as") }
  'data'      { PosPair _ (TKey "data") }
  'hiding'    { PosPair _ (TKey "hiding") }
  'import'    { PosPair _ (TKey "import") }
  'in'        { PosPair _ (TKey "in") }
  'let'       { PosPair _ (TKey "let") }
  'module'    { PosPair _ (TKey "module") }
  'qualified' { PosPair _ (TKey "qualified") }
  'sort'      { PosPair _ (TKey "sort") }
  'where'     { PosPair _ (TKey "where") }
  'axiom'     { PosPair _ (TKey "axiom") }
  'primitive' { PosPair _ (TKey "primitive") }
  var      { PosPair _ (TVar _) }
  unvar    { PosPair _ (TUnVar _) }
  con      { PosPair _ (TCon _) }
  nat      { PosPair _ (TNat _) }
  string   { PosPair _ (TString _) }

%%

Module :: { Module }
Module : 'module' ModuleName 'where' list(Import) list(SAWDecl) { Module $2 $4 $5 }

ModuleName :: { PosPair ModuleName }
ModuleName : ConDotList { mkPosModuleName $1 }

ConDotList :: { [PosPair String] }
ConDotList : Con { [$1] }
           | ConDotList '.' Con { $3 : $1 }

Import :: { Import }
Import : 'import' opt('qualified') ModuleName opt(AsName) opt(ModuleImports) ';'
          { Import (isJust $2) $3 $4 $5 }

SAWDecl :: { Decl }
SAWDecl : 'data' Con '::' LTerm 'where' '{' list(CtorDecl) '}' { DataDecl $2 $4 $7 }
          | 'primitive' DeclLhs '::' LTerm ';'
               {% mkTypeDecl PrimitiveQualifier $2 $4 }
          | 'axiom' DeclLhs '::' LTerm ';'
               {% mkTypeDecl AxiomQualifier $2 $4 }
          | SAWEqDecl { $1 }

AsName :: { PosPair String }
AsName : 'as' Con { $2 }

ModuleImports :: { ImportConstraint }
ModuleImports : 'hiding' ImportNames { HidingImports $2 }
              | ImportNames { SpecificImports $1 }

ImportNames :: { [ImportName] }
ImportNames : '(' sepBy(ImportName, ',') ')' { $2 }

ImportName :: { ImportName }
ImportName : Symbol                         { SingleImport $1 }
           | Con '(' '..' ')'               { AllImport $1 }
           | Con '(' sepBy(Symbol, ',') ')' { SelectiveImport $1 $3 }

SAWEqDecl :: { Decl }
SAWEqDecl : DeclLhs '::' LTerm ';' {% mkTypeDecl NoQualifier $1 $3 }
          | DeclLhs '='  Term ';'  {% mkTermDef  $1 $3 }

DeclLhs :: { DeclLhs }
DeclLhs : Symbol list(AtomPat) { ($1, $2) }

CtorDecl :: { CtorDecl }
CtorDecl : Con '::' CtorType ';' { Ctor $1 $3 }

Pat :: { Pat }
Pat : AtomPat           { $1 }
    | ConDotList list1(AtomPat) { PCtor (identFromList1 $1) $2 }

AtomPat :: { Pat }
AtomPat : SimplePat                    { PSimple $1 }
        | ConDotList                   { PCtor (identFromList1 $1) [] }
        | '(' sepBy(Pat, ',') ')'      { parseParen (\_ v -> v) mkPTuple (pos $1) $2 }
        | '(' Pat '|' Pat ')'          { PPair (pos $1) $2 $4 }
        | '{' sepBy(FieldPat, ',') '}' { mkPRecord (pos $1) $2 }
        | '{' FieldPat '|' Pat '}'     { PField $2 $4 }

SimplePat :: { SimplePat }
SimplePat : unvar { PUnused (fmap tokVar $1) }
          | Var   { PVar $1 }

LabelPat :: { Pat }
LabelPat : FieldName   { mkFieldNamePat $1 }
         | '(' Pat ')' { $2 }

FieldPat :: { (Pat, Pat) }
FieldPat : LabelPat '=' Pat { ($1, $3) }

Term :: { Term }
Term : LTerm { $1 }
     | LTerm '::' LTerm { TypeConstraint $1 (pos $2) $3 }

-- Term with uses of pi and lambda, but no typing.
LTerm :: { Term }
LTerm : AppTerm                          {  $1 }
      | PiArg '->' LTerm                 {  mkPi (pos $2) $1 $3 }
      | '\\' list1(AtomTerm) '->' LTerm {% mkLambda (pos $1) $2 $4 }

-- Term with uses of pi and lambda, but no typing.
CtorType :: { Term }
CtorType : AppTerm             { $1 }
         | PiArg '->' CtorType { mkPi (pos $2) $1 $3 }

-- Term formed from applications of atomic expressions.
AppTerm :: { Term }
AppTerm : AppArg                   { $1 }
        | AppTerm AppArg           { App $1 $2 }

AppArg :: { Term }
AppArg : RecTerm { $1 }
       | ConDotList { Con (identFromList1 $1) }

RecTerm :: { Term }
RecTerm : AtomTerm              { $1 }
        | ConDotList '.' Var    { Var (identFromList1 ($3 : $1)) }
        | RecTerm '.' Label     { RecordSelector $1 $3 }
        | RecTerm '.' nat       { mkTupleSelector $1 (fmap tokNat $3) }

AtomTerm :: { Term }
AtomTerm : nat                          { NatLit (pos $1) (tokNat (val $1)) }
         | string                       { StringLit (pos $1) (tokString (val $1)) }
         | Var                          { Var (fmap localIdent $1) }
         | unvar                        { Unused (fmap tokVar $1) }
         | 'sort' nat                   { Sort (pos $1) (mkSort (tokNat (val $2))) }
         |     '(' sepBy(Term, ',') ')'       { parseParen Paren mkTupleValue (pos $1) $2 }
         | '#' '(' sepBy(Term, ',') ')'       {% parseTParen (pos $1) $3 }
         |     '[' sepBy(Term, ',') ']'       { VecLit (pos $1) $2 }
         |     '{' sepBy(FieldValue, ',') '}' { mkRecordValue (pos $1) $2 }
         | '#' '{' sepBy(FieldType, ',') '}'  { mkRecordType  (pos $1) $3 }
         |     '(' Term '|' Term ')'          { PairValue (pos $1) $2 $4 }
         | '#' '(' Term '|' Term ')'          { PairType (pos $1) $3 $5 }
         |     '{' FieldValue '|' Term '}'    { FieldValue $2 $4 }
         | '#' '{' FieldType '|' Term '}'     { FieldType $3 $5 }

PiArg :: { PiArg }
PiArg : AppTerm  {% mkPiArg $1 }

Symbol :: { PosPair String }
Symbol : Con { $1 } | Var { $1 }

Con :: { PosPair String }
Con : con { fmap tokCon $1 }

Var :: { PosPair String }
Var : var { fmap tokVar $1 }

FieldName :: { PosPair FieldName }
FieldName : var { fmap tokVar $1 }

Label :: { Term }
Label : FieldName    { mkFieldNameTerm $1 }
      | '(' Term ')' { $2 }

FieldValue :: { (Term, Term) }
FieldValue : Label '=' Term { ($1, $3) }

FieldType :: { (Term, Term) }
FieldType : Label '::' LTerm { ($1, $3) }

opt(q) :: { Maybe q }
  : { Nothing }
  | q { Just $1 }

-- Two elements p and r separated by q and terminated by s
sepPair(p,q,r,s) :: { (p,r) }
  : p q r s { ($1,$3) }

-- A list of record fields with the given separator and element type.
recList(q,r) :: { [(FieldName,r)] }
  : list(sepPair(FieldName,q,r,';')) { $1 }

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
  = UnexpectedLex [Word8]
  | UnexpectedEndOfBlockComment
  | UnexpectedToken Token
  | ParseError String
  | UnexpectedEnd
  deriving (Show)

type ErrorList = [PosPair ParseError]

data ParserState = PS { psInput :: AlexInput
                      , psErrors :: [PosPair ParseError]
                      }

newtype Parser a = Parser { _unParser :: State ParserState a }
  deriving (Applicative, Functor, Monad)

addError :: Pos -> ParseError -> Parser ()
addError p err = Parser $ modify $ \s -> s { psErrors = PosPair p err : psErrors s }

setInput :: AlexInput -> Parser ()
setInput inp = Parser $ modify $ \s -> s { psInput = inp }

parsePos :: Parser Pos
parsePos = Parser $ gets (pos . psInput)

lexer :: (PosPair Token -> Parser a) -> Parser a
lexer f = do
  let go prevErr next = do
        let addErrors =
              case prevErr of
                Nothing -> return ()
                Just (po,l) -> addError po (UnexpectedLex (reverse l))
        s <- Parser get
        let inp@(PosPair p (Buffer _ b)) = psInput s
            end = addErrors >> next (PosPair p TEnd)
        case alexScan inp 0 of
          AlexEOF -> end
          AlexError _ ->
            case alexGetByte inp of
              Just (w,inp') -> do
                setInput inp'
                case prevErr of
                  Nothing -> go (Just (p,[w])) next
                  Just (po,l) -> go (Just (po,w:l)) next
              Nothing -> end
          AlexSkip inp' _ -> addErrors >> setInput inp' >> go Nothing next
          AlexToken inp' l act -> do
            addErrors
            setInput inp'
            let v = act (B.toString (B.take (fromIntegral l) b))
            next (PosPair p v)
  let read i tkn =
        case val tkn of
          TCmntS -> go Nothing (read (i+1))
          TCmntE | i > 0 -> go Nothing (read (i-1))
                 | otherwise -> do
                     addError (pos tkn) (UnexpectedLex (fmap (fromIntegral . fromEnum) "-}"))
                     go Nothing (read 0)
          _ | i > 0 -> go Nothing (read i)
            | otherwise -> f tkn
  go Nothing (read (0::Integer))

-- | Run parser given a directory for the base (used for making pathname relative),
-- bytestring to parse, and parser to run.
runParser :: Parser a -> FilePath -> FilePath -> B.ByteString -> (a,ErrorList)
runParser (Parser m) base path b = (r, reverse (psErrors s))
  where initState = PS { psInput = initialAlexInput base path b, psErrors = [] }
        (r,s) = runState m initState

parseSAW :: FilePath -> FilePath -> B.ByteString -> (Module,ErrorList)
parseSAW = runParser parseSAW2

parseSAWTerm :: FilePath -> FilePath -> B.ByteString -> (Term,ErrorList)
parseSAWTerm = runParser parseSAWTerm2

parseError :: PosPair Token -> Parser a
parseError pt = do
  addError (pos pt) (UnexpectedToken (val pt))
  fail $ (ppPos (pos pt)) ++ " Parse error\n  " ++ (ppToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

unexpectedIntLiteral :: Pos -> Integer -> String -> Parser ()
unexpectedIntLiteral p _ ctxt = do
  addParseError p $ "Unexpected integer literal when parsing " ++ ctxt ++ "."

unexpectedTypeConstraint :: Pos -> Parser ()
unexpectedTypeConstraint p = addParseError p "Unexpected type constraint."

unexpectedPi :: Pos -> Parser ()
unexpectedPi p = addParseError p "Unexpected pi expression"

unexpectedLambda :: Pos -> Parser ()
unexpectedLambda p = addParseError p "Unexpected lambda expression"

unexpectedOpenParen :: Pos -> Parser ()
unexpectedOpenParen p = addParseError p "Unexpected parenthesis"

termAsPat :: Term -> Parser (Maybe Pat)
termAsPat ex = do
    case asApp ex of
      (Var i, []) ->
        case asLocalIdent (val i) of
          Just nm -> ret $ PSimple $ PVar (PosPair (pos i) nm)
          _ -> badPat "Imported expressions"
      (Unused i,[]) -> ret $ PSimple $ PUnused i
      (Con i,l) -> fmap (fmap (PCtor i) . sequence) $ mapM termAsPat l
      (Sort{},_) -> badPat "Sorts"

      (Lambda{},_) -> badPat "Lambda expressions"
      (App{},_) -> error "internal: Unexpected application"
      (Pi{},_) -> badPat "Pi expressions"

      (UnitValue p, []) -> return $ Just (PUnit p)
      (PairValue p x y, []) -> do
        px <- termAsPat x
        py <- termAsPat y
        return (PPair p <$> px <*> py)
      (UnitType{}, _) -> badPat "Tuple types"
      (PairType{}, _) -> badPat "Tuple types"
      (EmptyValue p, []) -> return $ Just (PEmpty p)
      (FieldValue (f, x) y, []) -> do
        pf <- termAsPat f
        px <- termAsPat x
        py <- termAsPat y
        return (curry PField <$> pf <*> px <*> py)
      (RecordSelector{}, []) -> badPat "Record selector"
      (EmptyType{},[]) -> badPat "Record type"
      (FieldType{},[]) -> badPat "Record type"

      (TypeConstraint{}, []) -> badPat "Type constraint"
      (Paren{}, _) -> error "internal: Unexpected paren"
      (BadTerm{}, _) -> return Nothing
      (_, h:_) -> err (pos h) "Unexpected expression"
  where ret r = return (Just r)
        badPat nm = err (pos ex) (nm ++ " may not appear in patterns")
        err p msg = addParseError p msg >> return Nothing


-- Attempts to parses an expression as a list of identifiers.
-- Will return a value on all expressions, but may add errors to parser state.
exprAsPatList :: Term -> Parser [Pat]
exprAsPatList ex = go ex []
  where go (App x y) r = do
          mp <- termAsPat y
          go x (maybe r (:r) mp)
        go x r = do
          mp <- termAsPat x
          return (maybe r (:r) mp)

termAsSimplePat :: Term -> Parser (Maybe SimplePat)
termAsSimplePat ex = do
    case asApp ex of
      (Var i, []) ->
        case asLocalIdent (val i) of
          Just nm -> ret $ PVar (PosPair (pos i) nm)
          _ -> badPat "Imported expressions"
      (Unused i, []) -> ret $ PUnused i
      (BadTerm{}, _) -> return Nothing
      (_, h:_) -> err (pos h) "Unexpected expression"
  where ret r = return (Just r)
        badPat nm = err (pos ex) (nm ++ " may not appear in patterns")
        err p msg = addParseError p msg >> return Nothing

-- Attempts to parses an expression as a list of identifiers.
-- Will return a value on all expressions, but may add errors to parser state.
exprAsSimplePatList :: Term -> Parser [SimplePat]
exprAsSimplePatList ex = go ex []
  where go (App x y) r = do
          mp <- termAsSimplePat y
          go x (maybe r (:r) mp)
        go x r = do
          mp <- termAsSimplePat x
          return (maybe r (:r) mp)


type PiArg = ([SimplePat], Term)

-- | Pi expressions should have one of the forms:
-- * '(' list(Pat) '::' LTerm ')' '->' LTerm
-- * AppTerm '->' LTerm
mkPiArg :: Term -> Parser PiArg
mkPiArg (Paren _ (TypeConstraint x _ t)) =
  (\pats -> (pats, t)) <$> exprAsSimplePatList x
mkPiArg lhs =
  return ([PUnused (PosPair (pos lhs) "_")], lhs)

-- | Pi expressions should have one of the forms:
-- * '(' list(Pat) '::' LTerm ')' '->' LTerm
-- * AppTerm '->' LTerm
mkPi :: Pos -> PiArg -> Term -> Term
mkPi ptp (pats,tp) r = Pi pats tp ptp r

mkLambda :: Pos -> [Term] -> Term -> Parser Term
mkLambda ptp lhs rhs = parseLhs lhs []
  where parseLhs [] r = return $ Lambda ptp r rhs
        parseLhs ((Paren _ (TypeConstraint ux _ ut)):ul) r = do
          pl <- exprAsSimplePatList ux
          parseLhs ul ((pl, ut):r)

-- | Parse a parenthesized expression which may actually be a tuple.
parseParen :: (Pos -> a -> b) -- ^ singleton case.
           -> (Pos -> [a] -> b) -- ^ Tuple case
           -> Pos
           -> [a]
           -> b
parseParen f _ p [e] = f p e
parseParen _ g p l = g p l

parseTParen :: Pos -> [Term] -> Parser Term
parseTParen p [expr] = do
  addParseError p "Tuple may not contain a single value."
  return (badTerm p)
parseTParen p l = return $ mkTupleType p l

asAppList :: Term -> (Term,[Term])
asAppList = \x -> impl x []
  where impl (App x y) r = impl x (y:r)
        impl x r = (x,r)

type DeclLhs = (PosPair String, [Pat])

mkTypeDecl :: DeclQualifier -> DeclLhs -> Term -> Parser Decl
mkTypeDecl qual (op,args) rhs = fmap (\l -> TypeDecl qual (op:l) rhs) $ filterArgs args []
  where filterArgs ((PSimple (PVar (PosPair p i))):l) r =
          filterArgs l (PosPair p i:r)
        filterArgs (e:l) r = do
          addParseError (pos e) "Expected variable identifier in type declaration."
          filterArgs l r
        filterArgs [] r = return (reverse r)

-- | Crete a module name given a list of strings with the top-most
-- module name given first.
mkPosModuleName :: [PosPair String] -> PosPair ModuleName
mkPosModuleName [] = error "internal: Unexpected empty module name"
mkPosModuleName l = PosPair p (mkModuleName nms)
  where nms = fmap val l
        p = pos (last l)

identFromList1 :: [PosPair String] -> PosPair Ident
identFromList1 [] = error "internal: identFromList1 expected non-empty list"
identFromList1 [PosPair p sym] = PosPair p (mkIdent Nothing sym)
identFromList1 (PosPair _ sym:l) = PosPair p (mkIdent (Just m) sym)
  where PosPair p m = mkPosModuleName l

mkTermDef :: DeclLhs -> Term -> Parser Decl
mkTermDef (op,args) rhs = return (TermDef op args rhs)
}
