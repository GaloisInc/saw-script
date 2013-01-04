{
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Grammar 
  ( Decl(..)
  , Term(..)
  , parseSAW
  , runParser
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

import Debug.Trace

}

%name parseSAW
--%expect 0
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
  var      { PosPair _ (TVar _) }
  unvar    { PosPair _ (TUnVar _) }
  con      { PosPair _ (TCon _) }
  nat      { PosPair _ (TNat _) }

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
SAWEqDecl : DeclLhs '::' LTerm ';' {% mkTypeDecl $1 $3 }
          | DeclLhs '='  Term ';'  {% mkTermDef  $1 $3 }

DeclLhs :: { DeclLhs }
DeclLhs : Symbol list(LhsArg) { ($1, $2) }

LhsArg :: { (ParamType, Pat) }
LhsArg : AtomPat           { (NormalParam, $1) }
       | ParamType AtomPat { ($1, $2) }

CtorDecl :: { CtorDecl }
CtorDecl : Con '::' CtorType ';' { Ctor $1 $3 }

Pat :: { Pat }
Pat : AtomPat           { $1 }
    | ConDotList list(AtomPat) { PCtor (identFromList1 $1) $2 }

AtomPat :: { Pat }
AtomPat : unvar { PUnused (fmap tokVar $1) }
        | Var   { PVar $1 }
        | '(' sepBy(Pat, ',') ')'   { parseParen (\_ v -> v) PTuple (pos $1) $2 }
        | '{' recList('=', Pat) '}' { PRecord (pos $1) $2 }

Term :: { Term }
Term : TTerm { $1 }
     | 'let' '{' list(SAWEqDecl) '}' 'in' Term { LetTerm (pos $1) $3 $6 }

TTerm :: { Term }
TTerm : LTerm { $1 }
      | LTerm '::' LTerm { TypeConstraint $1 (pos $2) $3 }

-- Term with uses of pi and lambda, but no typing.
LTerm :: { Term }
LTerm : AppTerm                          {  $1 }
      | PiArg '->' LTerm                 {  mkPi (pos $2) $1 $3 }
      | '\\' list1(LambdaArg) '->' LTerm {% mkLambda (pos $1) $2 $4 }

-- Term with uses of pi and lambda, but no typing.
CtorType :: { Term }
CtorType : AppTerm             { $1 }
         | PiArg '->' CtorType { mkPi (pos $2) $1 $3 }

LambdaArg :: { (ParamType, Term) }
LambdaArg : AtomTerm           { (NormalParam, $1) }
          | ParamType AtomTerm { ($1, $2) }

-- Term formed from applications of atomic expressions.
AppTerm :: { Term }
AppTerm : AppArg                   { $1 }
        | AppTerm AppArg           { App $1 NormalParam $2 }
        | AppTerm ParamType AppArg { App $1 $2 $3 }

AppArg :: { Term }
AppArg : RecTerm { $1 } 
       | ConDotList { Con (identFromList1 $1) }

RecTerm :: { Term }
RecTerm : AtomTerm              { $1 }
        | ConDotList '.' Var    { Var (identFromList1 ($3 : $1)) }
        | RecTerm '.' FieldName { RecordSelector $1 $3 }

AtomTerm :: { Term }
AtomTerm : nat                          { IntLit (pos $1) (tokNat (val $1)) }
         | Var                          { Var (fmap localIdent $1) }
         | unvar                        { Unused (fmap tokVar $1) }
         | 'sort' nat                   { Sort (pos $1) (mkSort (tokNat (val $2))) }
         |     '(' sepBy(Term, ',') ')'     { parseParen Paren TupleValue (pos $1) $2 }
         | '#' '(' sepBy(Term, ',') ')'    {% parseTParen (pos $1) $3 }
         |     '{' recList('=',   Term) '}' { RecordValue (pos $1) $2 } 
         | '#' '{' recList('::', LTerm) '}' { RecordType  (pos $1) $3 }

PiArg :: { PiArg }
PiArg : ParamType AppArg {% mkPiArg ($1, $2) } 
      | AppTerm          {% mkPiArg (NormalParam, $1) }

ParamType :: { ParamType }
ParamType : '?'   { ImplicitParam }
          | '??'  { InstanceParam }
          | '???' { ProofParam    }

Symbol :: { PosPair String }
Symbol : Con { $1 } | Var { $1 }

Con :: { PosPair String }
Con : con { fmap tokCon $1 }

Var :: { PosPair String }
Var : var { fmap tokVar $1 }

FieldName :: { PosPair FieldName }
FieldName : var { fmap tokVar $1 }

opt(q) : { Nothing }
       | q { Just $1 }

-- Two elements p and r separated by q and terminated by s
sepPair(p,q,r,s) : p q r s { ($1,$3) }

-- A list of record fields with the given separator and element type.
recList(q,r) : list(sepPair(FieldName,q,r,';')) { $1 }

-- A possibly-empty list of p's separated by q.
sepBy(p,q) : {- empty -} { [] }
           | sepBy1(p,q) { $1 }

-- A possibly-empty list of p's separated by q.
sepBy1(p,q) : rsepBy1(p,q) { reverse $1 }

rsepBy1(p,q) : p { [$1] }
             | rsepBy1(p,q) q p { $3 : $1 }

-- A list of 0 or more p's, terminated by q's
list(p) : {- empty -} { [] }
        | rlist1(p) { reverse $1 }

-- A reversed list of at least 1 p's
rlist1(p) : p           { [$1]    }
          | rlist1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rlist1(p) { reverse $1 }

{
paramTypeToken :: ParamType -> String
paramTypeToken tp =
  case tp of
    NormalParam -> ""
    ImplicitParam -> "?"
    InstanceParam -> "??"
    ProofParam -> "???"

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
  deriving (Functor, Monad)

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

runParser :: FilePath -> FilePath -> B.ByteString -> Parser a -> (a,ErrorList)
runParser base path b (Parser m) = (r, reverse (psErrors s))
  where initState = PS { psInput = initialAlexInput base path b, psErrors = [] }
        (r,s) = runState m initState

parseError :: PosPair Token -> Parser a
parseError pt = do
  addError (pos pt) (UnexpectedToken (val pt))
  fail $ (ppPos (pos pt)) ++ " Parse error\n  " ++ (ppToken (val pt))

addParseError :: Pos -> String -> Parser ()
addParseError p s = addError p (ParseError s)

unexpectedIntLiteral :: Pos -> Integer -> String -> Parser ()
unexpectedIntLiteral p _ ctxt = do
  addParseError p $ "Unexpected integer literal when parsing " ++ ctxt ++ "."

unexpectedParameterAnnotation :: Pos -> ParamType -> Parser ()
unexpectedParameterAnnotation p _ = 
  addParseError p "Multiple parameter annotations are not supported."

unexpectedTypeConstraint :: Pos -> Parser ()
unexpectedTypeConstraint p = addParseError p "Unexpected type constraint."

unexpectedPi :: Pos -> Parser ()
unexpectedPi p = addParseError p "Unexpected pi expression"

unexpectedLambda :: Pos -> Parser ()
unexpectedLambda p = addParseError p "Unexpected lambda expression"

unexpectedOpenParen :: Pos -> Parser ()
unexpectedOpenParen p = addParseError p "Unexpected parenthesis"

mergeParamType :: ParamType -> Pos -> ParamType -> Parser ParamType
mergeParamType NormalParam _ tp = return tp
mergeParamType pt p mpt = do
  unexpectedParameterAnnotation p mpt >> return pt

termAsPat :: Term -> Parser (Maybe Pat)
termAsPat ex = do
    case asApp ex of
      (Var i, []) ->
        case asLocalIdent (val i) of
          Just nm -> ret $ PVar (PosPair (pos i) nm)
          _ -> badPat "Imported expressions"
      (Unused i,[]) -> ret $ PUnused i
      (Con i,l) -> fmap (fmap (PCtor i) . sequence) $ mapM termAsPat l
      (Sort{},_) -> badPat "Sorts"

      (Lambda{},_) -> badPat "Lambda expressions"
      (App{},_) -> error "internal: Unexpected application"
      (Pi{},_) -> badPat "Pi expressions"

      (TupleValue p l,[]) ->
        fmap (fmap (PTuple p) . sequence) $ mapM termAsPat l
      (TupleType{}, _) -> badPat "Tuple types"

      (RecordValue p l,[]) ->
          fmap (fmap (PRecord p . zip flds) . sequence) $ mapM termAsPat terms
        where (flds,terms) = unzip l
      (RecordSelector{}, []) -> badPat "Record selector"
      (RecordType{},[]) -> badPat "Record type"

      (TypeConstraint{}, []) -> badPat "Type constraint"
      (Paren{}, _) -> error "internal: Unexpected paren"
      (LetTerm{}, _) -> badPat "Let expression"
--      (IntLit p i, []) -> ret $ PIntLit p i
      (BadTerm{}, _) -> return Nothing
      (_, h:_) -> err (pos h) "Unexpected expression"
  where ret r = return (Just r)
        badPat nm = err (pos ex) (nm ++ " may not appear in patterns")
        err p msg = addParseError p msg >> return Nothing
        


-- Attempts to parses an expression as a list of identifiers.
-- Will return a value on all expressions, but may add errors to parser state.
exprAsPatList :: Term -> Parser [Pat]
exprAsPatList ex = go ex []
  where go (App x _ y) r = do
          mp <- termAsPat y
          go x (maybe r (:r) mp)
        go x r = do
          mp <- termAsPat x
          return (maybe r (:r) mp)


type PiArg = (ParamType,[Pat],Term)

-- | Pi expressions should have one of the forms:
-- * opt(ParamType) '(' list(Pat) '::' LTerm ')' '->' LTerm
-- * opt(ParamType) AppTerm '->' LTerm
mkPiArg :: (ParamType, Term) -> Parser PiArg
mkPiArg (ppt, Paren _ (TypeConstraint x _ t)) =
  (\pats -> (ppt, pats, t)) <$> exprAsPatList x
mkPiArg (ppt,lhs) =
  return (ppt, [PUnused (PosPair (pos lhs) "_")], lhs)

-- | Pi expressions should have one of the forms:
-- * opt(ParamType) '(' list(Pat) '::' LTerm ')' '->' LTerm
-- * opt(ParamType) AppTerm '->' LTerm
mkPi :: Pos -> PiArg -> Term -> Term
mkPi ptp (ppt,pats,tp) r = Pi ppt pats tp ptp r   

mkLambda :: Pos -> [(ParamType, Term)] -> Term -> Parser Term
mkLambda ptp lhs rhs = parseLhs lhs []
  where parseLhs [] r = return $ Lambda ptp r rhs
        parseLhs ((ppt,Paren _ (TypeConstraint ux _ ut)):ul) r = do
          pl <- exprAsPatList ux
          parseLhs ul ((ppt,pl, ut):r)

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
parseTParen p l = return $ TupleType p l

asAppList :: Term -> (Term,[Term])
asAppList = \x -> impl x []
  where impl (App x _ y) r = impl x (y:r)
        impl x r = (x,r)

type DeclLhs = (PosPair String, [(ParamType, Pat)])

mkTypeDecl :: DeclLhs -> Term -> Parser Decl
mkTypeDecl (op,args) rhs = fmap (\l -> TypeDecl (op:l) rhs) $ filterArgs args []
  where filterArgs ((NormalParam,PVar (PosPair p i)):l) r =
          filterArgs l (PosPair p i:r)
        filterArgs ((NormalParam,e):l) r = do
          addParseError (pos e) "Expected variable identifier in type declaration."
          filterArgs l r
        filterArgs ((pt,e):l) r = do
          addParseError (pos e) $ "Unexpected token " ++ paramTypeToken pt ++ "."
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
