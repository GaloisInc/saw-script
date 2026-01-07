{
{-# LANGUAGE OverloadedStrings #-}
module SAWScript.Parser
  ( parseModule
  , parseREPLText
  , parseExpression
  , parseSchema
  , parseSchemaPattern
  , ParseError(..)
  , prettyParseError
  ) where

import Control.Applicative
import Control.Exception
import Data.List
import qualified Data.Map as Map (fromList)
import qualified Data.Text as Text
import Data.Text (Text, pack, unpack)

import qualified Prettyprinter as PP

import qualified SAWSupport.Pretty as PPS
import SAWScript.Token
import SAWScript.Lexer
import SAWCentral.AST
import SAWCentral.Position
import SAWCentral.Utils

import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Utils.Ident as P (mkIdent, packModName)

}

%name parseModule StmtsSemiEOF
%name parseREPLText StmtsOptSemiEOF
%name parseExpression ExpressionEOF
%name parseSchema PolyTypeEOF
%name parseSchemaPattern SchemaPatternEOF
%error { parseError }
%error.expected
%tokentype { Token Pos }
%monad { Either ParseError }
%expect 0

%token
  'import'       { TReserved _ "import"         }
  'submodule'    { TReserved _ "submodule"      }
  'include'      { TReserved _ "include"        }
  'include_once' { TReserved _ "include_once"   }
  'and'          { TReserved _ "and"            }
  'as'           { TReserved _ "as"             }
  'hiding'       { TReserved _ "hiding"         }
  'let'          { TReserved _ "let"            }
  'rec'          { TReserved _ "rec"            }
  'in'           { TReserved _ "in"             }
  'do'           { TReserved _ "do"             }
  'if'           { TReserved _ "if"             }
  'then'         { TReserved _ "then"           }
  'else'         { TReserved _ "else"           }
  'typedef'      { TReserved _ "typedef"        }
  'rebindable'   { TReserved _ "rebindable"     }
  'ProofScript'  { TReserved _ "ProofScript"    }
  'TopLevel'     { TReserved _ "TopLevel"       }
  'CrucibleSetup'{ TReserved _ "CrucibleSetup"  }
  'CrucibleMethodSpec' { TReserved _ "CrucibleMethodSpec" }
  'LLVMSpec'     { TReserved _ "LLVMSpec"       }
  'JVMMethodSpec'{ TReserved _ "JVMMethodSpec"  }
  'JVMSpec'      { TReserved _ "JVMSpec"        }
  'MIRSpec'      { TReserved _ "MIRSpec"        }
  'Bool'         { TReserved _ "Bool"           }
  'Int'          { TReserved _ "Int"            }
  'String'       { TReserved _ "String"         }
  'Term'         { TReserved _ "Term"           }
  'Type'         { TReserved _ "Type"           }
  'AIG'          { TReserved _ "AIG"            }
  'CFG'          { TReserved _ "CFG"		}
  ';'            { TPunct    _ ";"              }
  '['            { TPunct    _ "["              }
  ']'            { TPunct    _ "]"              }
  '('            { TPunct    _ "("              }
  ')'            { TPunct    _ ")"              }
  '{'            { TPunct    _ "{"              }
  '}'            { TPunct    _ "}"              }
  ':'            { TPunct    _ ":"              }
  '::'           { TPunct    _ "::"             }
  ','            { TPunct    _ ","              }
  '.'            { TPunct    _ "."              }
  '\\'           { TPunct    _ "\\"             }
  '='            { TPunct    _ "="              }
  '->'           { TPunct    _ "->"             }
  '<-'           { TPunct    _ "<-"             }
  string         { TLit      _ _                }
  code           { TCode     _ _                }
  ctype          { TCType    _ _                }
  num            { TNum      _ _ _              }
  name           { TVar      _ _                }
  EOF            { TEOF      _ _                }

%right 'else'
%left ':'
%left '['
%left '.'

%%

StmtsSemiEOF :: { [Stmt] }
 : EOF                                  { [] }
 | Stmts ';' EOF                        { reverse $1 }

StmtsOptSemiEOF :: { [Stmt] }
 : EOF                                  { [] }
 | Stmts EOF                            { reverse $1 }
 | Stmts ';' EOF                        { reverse $1 }

ExpressionEOF :: { Expr }
 : Expression EOF                       { $1 }

PolyTypeEOF :: { Schema }
 : PolyType EOF                         { $1 }

SchemaPatternEOF :: { SchemaPattern }
 : SchemaPattern EOF                    { $1 }

-- accumulates in reverse order
Stmts :: { [Stmt] }
 : Stmt                                 { [$1] }
 | Stmts ';' Stmt                       { $3 : $1 }

Import :: { Import }
 : MName mbAs mbImportSpec              { buildImport False $1 $2 $3 }
 | 'submodule' MName mbAs mbImportSpec  { buildImport True $2 $3 $4 }

MName :: { (Either FilePath P.ModName, Pos) }
: string                                { (Left $ unpack $ tokStr $1, tokPos $1) }
| QName                                 { (Right $ P.packModName $ fst $1, snd $1) }

mbAs :: { (Maybe P.ModName, Pos) }
: 'as' QName                            { (Just (P.packModName (fst $2)), maxSpan' $1 (snd $2)) }
 | {- empty -}                          { (Nothing, Unknown) }

mbImportSpec :: { (Maybe P.ImportSpec, Pos) }
 : '(' list(name) ')'                   { (Just $ P.Only   [ P.mkIdent (tokStr n) | n <- $2 ], maxSpan [tokPos $1, tokPos $3]) }
 | 'hiding' '(' list(name) ')'          { (Just $ P.Hiding [ P.mkIdent (tokStr n) | n <- $3 ], maxSpan [tokPos $1, tokPos $4]) }
 | {- empty -}                          { (Nothing, Unknown) }

Stmt :: { Stmt }
 : Expression                           { StmtBind (getPos $1) (PWild (leadingPos $ getPos $1) Nothing) $1 }
 | AExpr '<-' Expression                {% fmap (\x -> StmtBind (maxSpan' x $3) x $3) (toPattern $1) }
 | 'rec' sepBy1(Declaration, 'and')     { buildRec (maxSpan [tokPos $1, maxSpan $2]) $2 }
 | 'let' Declaration                    { buildLet (maxSpan [tokPos $1, getPos $2]) $2 }
 | 'let' 'rebindable' Declaration       { buildLetRB (maxSpan [tokPos $1, getPos $3]) $3 }
 | 'let' code                           { StmtCode (maxSpan [tokPos $1, tokPos $2]) (tokPos $2) (tokStr $2) }
 | 'import' Import                      { StmtImport (maxSpan [tokPos $1, getPos $2]) $2 }
 | 'include' string                     { StmtInclude (maxSpan [tokPos $1, tokPos $2]) (tokStr $2) False }
 | 'include_once' string                { StmtInclude (maxSpan [tokPos $1, tokPos $2]) (tokStr $2) True }
 | 'typedef' name '=' Type              { StmtTypedef (maxSpan [tokPos $1, getPos $4]) (tokPos $2) (tokStr $2) $4 }

Declaration :: { Decl }
 : Arg list(Arg) '=' Expression         { Decl (maxSpan' $1 $4) $1 Nothing (buildFunction (Just $1) $2 $4) }
 | Arg list(Arg) ':' Type '=' Expression
                                        { Decl (maxSpan' $1 $6) $1 Nothing (buildFunction (Just $1) $2 (TSig (maxSpan' $4 $6) $6 $4)) }

Pattern :: { Pattern }
 : Arg                                  { $1 }
 | name ':' Type                        { buildPVar (maxSpan [tokPos $1, getPos $3]) (tokPos $1) (tokStr $1) (Just $3) }

Arg :: { Pattern }
 : name                                 { buildPVar (tokPos $1) (tokPos $1) (tokStr $1) Nothing }
 | '(' ')'                              { PTuple (maxSpan [tokPos $1, tokPos $2]) [] }
 | '(' commas(Pattern) ')'              { case $2 of [p] -> p; _ -> PTuple (maxSpan [tokPos $1, tokPos $3]) $2 }

Expression :: { Expr }
 : IExpr                                { $1 }
 | IExpr ':' Type                       { TSig (maxSpan' $1 $3) $1 $3 }
 | '\\' list1(Arg) '->' Expression      { buildFunction Nothing $2 $4 }
 | 'let' Declaration 'in' Expression    { Let (maxSpan [tokPos $1, getPos $4]) (NonRecursive $2) $4 }
 | 'rec' sepBy1(Declaration, 'and')
   'in' Expression                      { Let (maxSpan [tokPos $1, getPos $4]) (Recursive $2) $4 }
 | 'if' Expression 'then' Expression
                   'else' Expression    { IfThenElse (maxSpan [tokPos $1, getPos $6]) $2 $4 $6 }

IExpr :: { Expr }
 : AExprs                               { $1 }

AExprs :: { Expr }
 : list1(AExpr)                         { buildApplication $1 }

AExpr :: { Expr }
: '(' ')'                               { Tuple (maxSpan [tokPos $1, tokPos $2]) [] }
 | '[' ']'                              { Array (maxSpan [tokPos $1, tokPos $2]) [] }
 | string                               { String (tokPos $1) (tokStr $1) }
 | code                                 { Code (tokPos $1) (tokStr $1) }
 | ctype                                { CType (tokPos $1) (tokStr $1) }
 | num                                  { Int (tokPos $1) (tokNum $1) }
 | name                                 { Var (tokPos $1) (tokStr $1) }
 | '(' Expression ')'                   { $2 } -- { Parens (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '(' commas2(Expression) ')'          { Tuple (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '[' commas(Expression) ']'           { Array (maxSpan [tokPos $1, tokPos $3]) $2 }
 | '{' commas(Field) '}'                { Record (maxSpan [tokPos $1, tokPos $3]) (Map.fromList $2) }
 | 'do' '{' termBy(Stmt, ';') '}'       {% buildBlock (maxSpan [tokPos $1, tokPos $4]) $3 }
 | AExpr '.' name                       { Lookup (maxSpan [getPos $1, tokPos $3]) $1 (tokStr $3) }
 | AExpr '.' num                        { TLookup (maxSpan [getPos $1, tokPos $3]) $1 (tokNum $3) }

Field :: { (Name, Expr) }
 : name '=' Expression                  { (tokStr $1, $3) }

Names :: { [(Pos, Name)] }
 : name                                 { [(getPos $1, tokStr $1)] }
 | name ',' Names                       { (getPos $1, tokStr $1) : $3 }

PolyType :: { Schema }
 : Type                                 { tMono $1     }
 | '{' Names '}' Type                   { Forall $2 $4 }

-- this is used by :search so you can write multiple match criteria:
-- it allows either t1 -> t2 -> ... or t1 t2 t3, including (t1 -> t1') t2 t3
SchemaPattern :: { SchemaPattern }
 : BaseFunType                          { SchemaPattern [] [$1]       }
 | BaseType list(BaseType)              { SchemaPattern [] ($1 : $2)  }
 | '{' Names '}' BaseFunType            { SchemaPattern $2 [$4]       }
 | '{' Names '}' BaseType list(BaseType) { SchemaPattern $2 ($4 : $5) }

Type :: { Type }
 : AppliedType                          { $1                      }
 | AppliedType '->' Type                { tFun (maxSpan [$1, $3]) $1 $3 }

AppliedType :: { Type }
 : BaseType                             { $1                            }
 | AppliedType BaseType                 { tBlock (maxSpan' $1 $2) $1 $2 }

-- special case of function type that can be followed by more base types
-- without requiring parens
BaseFunType :: { Type }
 : BaseType '->' Type                   { tFun (maxSpan [$1, $3]) $1 $3 }

BaseType :: { Type }
 : name                                 { tVar (getPos $1) (tokStr $1)     }
 | '(' ')'                              { tTuple (maxSpan [$1, $2]) []     }
 | 'Bool'                               { tBool (getPos $1)                }
 | 'Int'                                { tInt (getPos $1)                 }
 | 'String'                             { tString (getPos $1)              }
 | 'Term'                               { tTerm (getPos $1)                }
 | 'Type'                               { tType (getPos $1)                }
 | 'AIG'                                { tAIG (getPos $1)                 }
 | 'CFG'                                { tCFG (getPos $1)                 }
 | 'CrucibleMethodSpec'                 { tLLVMSpec (getPos $1)            }
 | 'LLVMSpec'                           { tLLVMSpec (getPos $1)            }
 | 'JVMMethodSpec'                      { tJVMSpec (getPos $1)             }
 | 'JVMSpec'                            { tJVMSpec (getPos $1)             }
 | 'MIRSpec'                            { tMIRSpec (getPos $1)             }
 | 'ProofScript'                        { tContext (getPos $1) ProofScript }
 | 'TopLevel'                           { tContext (getPos $1) TopLevel    }
 | 'CrucibleSetup'                      { tVar (getPos $1) "LLVMSetup"     }
 | '(' Type ')'                         { $2                               }
 | '(' commas2(Type) ')'                { tTuple (maxSpan [$1, $3]) $2     }
 | '[' Type ']'                         { tArray (maxSpan [$1, $3]) $2     }
 | '{' commas(FieldType) '}'            { tRecord (maxSpan [$1, $3]) $2    }

FieldType :: { (Name, Type) }
  : name ':' Type                       { (tokStr $1, $3)         }

QName :: { ([Text], Pos) }
   : sepBy1(name, '::')			{ (map tokStr $1, maxSpan (map tokPos $1)) }

-- Parameterized productions, most come directly from the Happy manual.
fst(p, q)  : p q   { $1 }
snd(p, q)  : p q   { $2 }
both(p, q) : p q   { ($1, $2) }

phrase(p) : p EOF { $1 }

-- p bracketed with some delims o-c
bracketed(o, p, c) : o p c { $2 }

-- p and q, connected by some connective c
connected(p, c, q) : p c q { ($1, $3) }

-- an optional p
opt(p) : p            { Just $1 }
       | {- empty -}  { Nothing }

-- A reversed list of at least 1 p's
rev_list1(p) : p              { [$1]    }
             | rev_list1(p) p { $2 : $1 }

-- A list of at least 1 p's
list1(p) : rev_list1(p)   { reverse $1 }

-- A potentially empty list of p's
list(p) : {- empty -}    { [] }
        | list1(p)       { $1 }

-- A reversed list of at least 1 p's
seprev_list(p,q) : seprev_list(p,q) p { $2 : $1 }
                 | seprev_list(p,q) q { $1 }
                 | {- empty -}    { [] }

-- A potentially empty list of p's separated by zero or more qs (which are ignored).
seplist(p,q) : seprev_list(p,q)  { reverse $1 }

-- A list of at least one 1 p's, separated by q's
sepBy1(p, q) : p list(snd(q, p)) { $1 : $2 }

sepBy2(p, q) : p q sepBy1(p, q) { $1 : $3 }

-- A list of 0 or more p's, separated by q's
sepBy(p, q) : {- empty -}  { [] }
            | sepBy1(p, q) { $1 }

-- A list of at least one 1 p's, terminated by q's
termBy1(p, q) : list1(fst(p, q)) { $1 }

-- A list of 0 or more p's, terminated by q's
termBy(p, q) : {- empty -}    { [] }
             | termBy1(p, q)  { $1 }

-- one or the other
either(p, q) : p  { Left  $1 }
             | q  { Right $1 }

commas(p) : sepBy1(p, ',') { $1 }
commas2(p) : sepBy2(p, ',') { $1 }

{

-- | Structured error type for parser-level errors.
--
--   `HappyError` is generated when Happy calls its @%error@ function.
--   The other cases are generated by our own code below.
data ParseError
  = HappyError [Token Pos] [String]
  | InvalidPattern Pos Expr
  | EmptyBlock Pos
  | InvalidBlock Pos

-- | Render a parse error.
--
-- For `HappyError` (the other messages are straightforward):
--
-- Happy's error reporting model is that it gives you the remaining
-- tokens, and the error message is effectively just "syntax error".
--
-- When the "%error.expected" flag is set, an extra argument is passed
-- to the parse error function. It's a list of strings that represent,
-- in some unspecified way, the legal next tokens at the point where
-- the error happened.
--
-- Why it doesn't just produce a list of tokens, IDK. I guess it has
-- no way to manufacture a value for a token that has a value and they
-- didn't want to come up with a mechanism to get one?
--
-- There is also apparently no way to discover
--    - the last token consumed
--    - the nonterminal(s) we're currently in the middle of
--    - which parser entry point we started from
--
-- all of which are things it's quite reasonable to kind of want to
-- know to produce a decent message. In place of the latter we have
-- the loader pass us the string to use as the token name for EOF.
--
-- So what we do is:
--    - If there is exactly one legal possible next input, we report
--      it as missing.
--    - Otherwise we say "Unexpected foo" and print the list of
--      possible inputs.
--
-- We trust that the strings Happy sends us will be meaningful to
-- the user. Good luck with that.
--
-- Note: we return the position and the document separately so they
-- can be passed to the error infrastructure separately.
--
prettyParseError :: Text -> ParseError -> (Maybe Pos, PPS.Doc)
prettyParseError eofName pe = case pe of
    HappyError nextToks possibles ->
        let (optpos, tstr) = case nextToks of
	      [] -> (Nothing, eofName)
	      t : _ts -> (Just (tokPos t), tokStr t)
            tstr' = PPS.squotesMatching $ PP.pretty tstr
	    doc = case possibles of
	      [] -> "Syntax error: unexpected" PP.<+> tstr'
	      [p] -> "Syntax error: missing" PP.<+> PP.pretty p
	      ps ->
                  let ps' =
                        "Some legal inputs at this point:" : map PP.pretty ps
                  in
		  PP.vsep [
                      "Syntax error: unexpected" PP.<+> tstr',
		      PP.nest 3 $ PP.group $ PP.fillSep $ ps'
		  ]
        in
	(optpos, doc)
    InvalidPattern pos e ->
        (Just pos, "Parse error: invalid pattern" PP.<+> PPS.prettyPrec 0 e)
    EmptyBlock pos ->
        (Just pos, "do block must include at least one expression")
    InvalidBlock pos ->
        (Just pos, "do block must end with expression")

parseError :: [Token Pos] -> [String] -> Either ParseError b
parseError toks possibles =
  Left (HappyError toks possibles)

-- | Cons up an import.
buildImport ::
    Bool ->
    (Either FilePath P.ModName, Pos) ->
    (Maybe P.ModName, Pos) ->
    (Maybe P.ImportSpec, Pos) ->
    Import
buildImport issub (modName, namePos) (mbAsName, asPos) (mbSpec, specPos) =
  Import {
    iIsSubmodule = issub,
    iModule = modName,
    iAs = mbAsName,
    iSpec = mbSpec,
    iPos = maxSpan [namePos, asPos, specPos]
  }

-- | As seen by the parser, a "function name" is an arbitrary pattern.
--   This is because we use the same syntax for function and value bindings:
--   in "let (a, b) = e" the "(a, b)" can and should be an arbitrary pattern.
--   For functions it doesn't make sense for it to be anything but a plain
--   name, as in "let f () = e". You can write "let (a, b) () = e" and the
--   parser will accept it, but it won't typecheck.
--
--   This function extracts the actual name, if any, for annotating
--   the lambda expressions we turn further arguments into. It will
--   return Nothing if the name is something other than an actual
--   name, which is fine for value bindings since the result won't be
--   used and also fine for nonsense like "let (a, b) () = e" that'll
--   be rejected by the typechecker. The annotations in question are
--   used only at eval time.
--
--   Runs in the Maybe monad for convenience.
fixFunctionName :: Maybe Pattern -> Maybe Text
fixFunctionName mname = do
  name <- mname
  case name of
      PWild {} -> Nothing
      PVar _allpos _namepos name _ty -> Just name
      PTuple {} -> Nothing

buildFunction :: Maybe Pattern -> [Pattern] -> Expr -> Expr
buildFunction mname args e =
  let mname' = fixFunctionName mname
      once :: Pattern -> Expr -> Expr
      once pat e = Lambda (maxSpan' pat e) mname' pat e
  in
  foldr once e args

buildApplication :: [Expr] -> Expr
buildApplication es =
  foldl1 (\e body -> Application (maxSpan' e body) e body) es

-- | Build a let-statement.
buildLet :: Pos -> Decl -> Stmt
buildLet pos d =
  StmtLet pos ReadOnlyVar (NonRecursive d)

-- | Build a rebindable let-statement.
buildLetRB :: Pos -> Decl -> Stmt
buildLetRB pos d =
  StmtLet pos RebindableVar (NonRecursive d)

-- | Build a rec-statement.
buildRec :: Pos -> [Decl] -> Stmt
buildRec pos ds =
  StmtLet pos ReadOnlyVar (Recursive ds)

-- | Build a variable-pattern. Discard the variable if it's _.
--
--   Note: it is probably more appropriate to discard all variables
--   that _begin_ with an underscore; however, the traditional usage
--   in ML, Haskell, and also Rust is to treat variables beginning
--   with underscore as placeholder variables that can still be used
--   behind your back. That's wrong; however, SAWScript is not the
--   place to fight this battle...
--
buildPVar :: Pos -> Pos -> Text -> Maybe Type -> Pattern
buildPVar allpos xpos x mty =
  case x of
    "_" -> PWild allpos mty
    _ -> PVar allpos xpos x mty

-- | Pop off the last statement in a do-block, which is required to
--   be a plain expression, and unpack it to an expression.
buildBlock :: Pos -> [Stmt] -> Either ParseError Expr
buildBlock pos stmts = case reverse stmts of
  StmtBind _spos (PWild _patpos _noty) e : revstmts' ->
    Right $ Block pos (reverse revstmts', e)
  [] ->
    Left $ EmptyBlock pos
  _ ->
    Left $ InvalidBlock pos

toPattern :: Expr -> Either ParseError Pattern
toPattern expr =
  case expr of
    Tuple pos es ->
        PTuple pos `fmap` mapM toPattern es
    TSig pos (Var xpos x) t ->
        return (buildPVar pos xpos x (Just t))
    Var pos x ->
        return (buildPVar pos pos x Nothing)
    _ ->
        Left (InvalidPattern (getPos expr) expr)

}
