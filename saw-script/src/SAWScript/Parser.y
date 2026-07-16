{
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
-- Beware: the Happy-generated output disables all compiler warnings
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
import Control.Monad (foldM)
import Data.List hiding (unsnoc) -- FUTURE: don't need to do this for GHC 9.8+
import Data.List.Extra (unsnoc)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Text (Text, pack, unpack)

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import qualified SAWSupport.Pretty as PPS
import SAWScript.Panic (panic)
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
  'CFG'          { TReserved _ "CFG"            }
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
  '?'            { TPunct    _ "?"              }
  '@'            { TPunct    _ "@"              }
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
 : '(' sepList(name, ',') ')'           { (Just $ P.Only   [ P.mkIdent (tokStr n) | n <- $2 ], maxSpan [tokPos $1, tokPos $3]) }
| 'hiding' '(' sepList(name, ',') ')'   { (Just $ P.Hiding [ P.mkIdent (tokStr n) | n <- $3 ], maxSpan [tokPos $1, tokPos $4]) }
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
 : PlainPattern list(PlainParam) '=' Expression          {% declFunc $1 $2 Nothing $4 }
 | PlainPattern list(PlainParam) ':' Type '=' Expression {% declFunc $1 $2 (Just $4) $6 }

ParamName :: { (Pos, Text, Maybe Pattern, Expr) }
ParamName
 : name '?' '=' AExpr                   { (tokPos $1, tokStr $1, Nothing, $4) }
 | name '@' PlainPattern '?' '=' AExpr  { (tokPos $1, tokStr $1, Just $3, $6) }

TypedParam :: { (Maybe ParamLabel, Pattern) }
 : ParamName                            {% mkNamedParam $1 Nothing   }
 | ParamName ':' Type                   {% mkNamedParam $1 (Just $3) }

PlainParam :: { (Maybe ParamLabel, Pattern) }
 : ParamName                            {% mkNamedParam $1 Nothing }
 | '(' TypedParam ')'                   { $2 }
 | PlainPattern                         { (Nothing, $1) }

TypedPattern :: { Pattern }
 : PlainPattern                         { $1 }
 | name ':' Type                        { mkVarPattern (tokPos $1) (tokStr $1) (Just $3) }

PlainPattern :: { Pattern }
 : name                                 { mkVarPattern (tokPos $1) (tokStr $1) Nothing }
 | '(' ')'                              { PTuple (maxSpan [tokPos $1, tokPos $2]) [] }
 | '(' commas(TypedPattern) ')'         { mkTupleParam $1 $2 $3 }

Expression :: { Expr }
 : IExpr                                { $1 }
 | IExpr ':' Type                       { TSig (maxSpan' $1 $3) $1 $3 }
 | '\\' list1(PlainParam) '->' Expression {% buildFunction Nothing $2 $4 }
 | 'let' Declaration 'in' Expression    { Let (maxSpan [tokPos $1, getPos $4]) (NonRecursive $2) $4 }
 | 'rec' sepBy1(Declaration, 'and')
   'in' Expression                      { Let (maxSpan [tokPos $1, getPos $4]) (Recursive $2) $4 }
 | 'if' Expression 'then' Expression
                   'else' Expression    { IfThenElse (maxSpan [tokPos $1, getPos $6]) $2 $4 $6 }

IExpr :: { Expr }
 : Arguments                            { $1 }

Arguments :: { Expr }
 : AExpr list(ArgumentExpr)             { buildApplication $1 $2 }

ArgumentExpr :: { (Maybe (Pos, Text), Expr) }
 : AExpr                                { (Nothing, $1) }
 | name '=' AExpr                       { (Just (tokPos $1, tokStr $1), $3) }
 | '(' name '=' Expression ')'          { (Just (tokPos $2, tokStr $2), $4) }

AExpr :: { Expr }
 : '(' ')'                              { Tuple (maxSpan [tokPos $1, tokPos $2]) [] }
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
 : AppliedType                          { $1 }
 | AppliedType '->' FunctionType        {% mkFuncType ((Nothing, $1) : $3) }
 | name '?' AppliedType '->' FunctionType {% mkFuncType ((Just $1, $3) : $5) }

FunctionType :: { [(Maybe (Token Pos), Type)] }
 : AppliedType                          { [(Nothing, $1)] }
 | AppliedType '->' FunctionType        { (Nothing, $1) : $3 }
 | name '?' AppliedType '->' FunctionType { (Just $1, $3) : $5 }

AppliedType :: { Type }
 : BaseType                             { $1                            }
 | AppliedType BaseType                 { tBlock (maxSpan' $1 $2) $1 $2 }

-- special case of function type that can be followed by more base types
-- without requiring parens
BaseFunType :: { Type }
 : BaseType '->' FunctionType           {% mkFuncType ((Nothing, $1) : $3) }
 | name '?' BaseType '->' FunctionType  {% mkFuncType ((Just $1, $3) : $5) }

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

-- A reversed list of one or more p's, separated by q's
sepRevList1(p,q) : p                    { [$1] }
                 | sepRevList1(p,q) q p { $3 : $1 }

-- A reversed list of zero or more p's, separated by q's
sepRevList(p,q) : {- empty -}      { [] }
                | sepRevList1(p,q) { $1 }

-- A potentially empty list of p's, separated by q's
sepList(p,q) : sepRevList(p,q)  { reverse $1 }

-- A list of at least one p, separated by q's
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
  | InvalidPatternAnnotation Pos
  | InvalidNamedParam Pos
  | DuplicateNamedParam Pos Text Pos
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
prettyParseError :: PPS.Opts -> Text -> ParseError -> (Maybe Pos, PPS.Doc)
prettyParseError ppopts eofName pe = case pe of
    HappyError nextToks possibles ->
        let (optpos, tstr) = case nextToks of
              [] -> (Nothing, eofName)
              t : _ts -> (Just (tokPos t), tokStr t)
            tstr' = PPS.squotesMatching $ PP.pretty tstr
            doc = case possibles of
              [] -> "Syntax error: unexpected" <+> tstr'
              [p] -> "Syntax error: missing" <+> PP.pretty p
              ps ->
                  let ps' =
                        "Some legal inputs at this point:" : map PP.pretty ps
                  in
                  PP.vsep [
                      "Syntax error: unexpected" <+> tstr',
                      PP.nest 3 $ PP.group $ PP.fillSep $ ps'
                  ]
        in
        (optpos, doc)
    InvalidPattern pos e ->
        (Just pos, "Parse error: invalid pattern" <+> prettyExpr ppopts e)
    InvalidPatternAnnotation pos ->
        (Just pos, "Parse error: invalid pattern type annotation")
    InvalidNamedParam pos ->
        (Just pos, "Invalid name for named parameter")
    DuplicateNamedParam pos name _prevpos ->
        (Just pos, "Duplicate named parameter" <+> PP.pretty name)
        -- FUTURE: maybe add this sometime
        -- (requires the ability to issue more than one message here)
        -- (Just prevpos, "Previous instance was here")
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

-- | Type for wrapping the name and default value of a named parameter.
--   The first position is the overall position of all of it; the
--   second position is the position of just the name.
data ParamLabel = ParamLabel Pos Pos Text Expr

instance Positioned ParamLabel where
  getPos (ParamLabel allpos _xpos _x _e) = allpos

-- | As seen by the parser, a "function name" is an arbitrary pattern.
--   This is because we use the same syntax for function and value bindings:
--   in "let (a, b) = e" the "(a, b)" can and should be an arbitrary pattern.
--   For functions it doesn't make sense for it to be anything but a plain
--   name, as in "let f () = e". You can write "let (a, b) () = e" and the
--   parser will accept it, but it won't typecheck.
--
--   This function extracts the actual name for annotating
--   the lambda expressions we turn further arguments into. It will
--   return Nothing if the name is something other than an actual
--   name, which is fine for value bindings since the result won't be
--   used and also fine for nonsense like "let (a, b) () = e" that'll
--   be rejected by the typechecker. The annotations in question are
--   used only at eval time.
--
fixFunctionName :: Pattern -> Maybe Text
fixFunctionName = \case
  PWild {} -> Nothing
  PVar _allpos _namepos name _ty -> Just name
  PTuple {} -> Nothing

-- | Declare a whole function. This extracts positions, wraps any type
--   signature around the body, and calls `buildFunction`.
--
--   Runs in the Either monad for convenience.
declFunc :: Pattern -> [(Maybe ParamLabel, Pattern)] -> Maybe Type -> Expr ->
      Either ParseError Decl
declFunc fun params mbType e = do
  let fun' = fixFunctionName fun
      e' = case mbType of
        Nothing -> e
        Just ty -> TSig (maxSpan' ty e) e ty
  e' <- buildFunction fun' params e'
  Right $ Decl (maxSpan' fun e) fun Nothing e'

-- | Construct a function body from a parameter list and base body
--   expression. We store all functions as lambdas, so this takes the
--   parameters and pushes them onto the body function as a lambda node.
buildFunction :: Maybe Text -> [(Maybe ParamLabel, Pattern)] -> Expr ->
      Either ParseError Expr
buildFunction mname params e = case params of
  [] ->
      -- not actually a function, don't create a lambda node
      Right e
  _ -> do
      -- Run this in the Either monad for convenience

      -- Split off the named parameters so we can carry them
      -- around separately.
      let dosplit (mbName, param) (params', namedParams) =
            case mbName of
                Nothing -> (param : params', namedParams)
                Just info -> (params', (info, param) : namedParams)
          (params', namedParams) = foldr dosplit ([], []) params

      -- Convert the namedParams list to a map.
      let doadd namedParams' (ParamLabel allpos xpos x defval, param) =
            case Map.lookup x namedParams' of
                Nothing ->
                    Right $ Map.insert x (xpos, (allpos, defval, param)) namedParams'
                Just (prevxpos, _previnfo) ->
                    Left $ DuplicateNamedParam xpos x prevxpos
      namedParams' <- foldM doadd Map.empty namedParams

      -- Figure out the overall pos
      let pos = spanPos (maxSpan params) (getPos e)

      Right $ Lambda pos mname params' namedParams' e

buildApplication :: Expr -> [(Maybe (Pos, Text), Expr)] -> Expr
buildApplication fun args = case args of
    [] ->
        -- One expression: just an expression, not an application
        fun
    _ ->
        -- Function with args
        let argpos (Nothing, e) = getPos e
            argpos (Just (pos, _x), e) = maxSpan' pos e
            pos = maxSpan' fun $ maxSpan $ map argpos args
        in
        Application pos fun args

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

-- | Insert a type into a pattern, maybe.
--
--   Attaching more than one type annotation to the same pattern
--   element is prohibited, even if they're the same (it is not our
--   job here to know what "the same type" means) and if you want to
--   annotate the type of a tuple pattern you're supposed to do it on
--   the elements, not on the outside. Historically attempting the
--   latter just produced a parse error; now because the pieces can be
--   further apart it's accepted by the grammar in some cases and
--   fails here instead.
addTypeToPattern :: Pattern -> Maybe Type -> Either ParseError Pattern
addTypeToPattern pat mbType = case mbType of
  Nothing -> pure pat
  Just ty -> case pat of
      PWild pos Nothing ->
          pure $ PWild pos (Just ty)
      PVar allpos namepos name Nothing ->
          pure $ PVar allpos namepos name (Just ty)
      _ ->
          Left $ InvalidPatternAnnotation (getPos ty)

-- | Build a named parameter.
mkNamedParam ::
      (Pos, Text, Maybe Pattern, Expr) ->
      Maybe Type ->
      Either ParseError (Maybe ParamLabel, Pattern)
mkNamedParam (xpos, x, mbPat, e) mbType = do
  pat <- case mbPat of
        Nothing -> pure $ mkVarPattern xpos x mbType
        Just pat' -> addTypeToPattern pat' mbType

  let allpos = case mbType of
        Nothing -> spanPos xpos (getPos pat)
        Just ty -> spanPos xpos (getPos ty)

  if x == "_" then
      Left $ InvalidNamedParam xpos
  else
      Right (Just (ParamLabel allpos xpos x e), pat)

-- | Build a variable pattern, discarding the variable if it's _.
--
--   Note: it is probably more appropriate to discard all variables
--   that _begin_ with an underscore; however, the traditional usage
--   in ML, Haskell, and also Rust is to treat variables beginning
--   with underscore as placeholder variables that can still be used
--   behind your back. That's wrong; however, SAWScript is not the
--   place to fight this battle...
--
mkVarPattern :: Pos -> Text -> Maybe Type -> Pattern
mkVarPattern xpos x mbType =
  let allpos = case mbType of
        Nothing -> xpos
        Just ty -> maxSpan [xpos, getPos ty]
  in
  case x of
      "_" -> PWild allpos mbType
      _ -> PVar allpos xpos x mbType

-- | Build a tuple parameter. Takes the left and right parentheses
--   tokens as well as the pattern list, for position tracking.
--   Single parenthesized parameters are just parameters, not
--   monoples.
mkTupleParam :: Token Pos -> [Pattern] -> Token Pos -> Pattern
mkTupleParam lp pats rp = case pats of
  [pat] -> pat
  _ -> PTuple (spanPos (tokPos lp) (tokPos rp)) pats

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
    TSig _pos (Var xpos x) t ->
        pure $ mkVarPattern xpos x (Just t)
    Var xpos x ->
        pure $ mkVarPattern xpos x Nothing
    _ ->
        Left (InvalidPattern (getPos expr) expr)

-- | Generate a function type from a list. This amounts to
--   peeling off the return type from the end of the list,
--   then splitting off the named parameters.
mkFuncType :: [(Maybe (Token Pos), Type)] -> Either ParseError Type
mkFuncType tys = do
  let pos = maxSpan tys
      (params, ret) = case reverse tys of
          [] -> panic "mkFuncType" ["Empty type list"]
          r : ps -> (reverse ps, r)

  (numPositional, namedNames, posParams, namedParams) <- do
      let once (count, names, pps, nps) (mbName, param) = case mbName of
            Nothing ->
                Right (count + 1, names, param : pps, nps)
            Just tok -> do
                let pos = tokPos tok
                    name = tokStr tok
                if name == "_" then
                    Left $ InvalidNamedParam pos
                else
                    case Map.lookup name nps of
                        Nothing ->
                            Right (count, name : names, pps, Map.insert name param nps)
                        Just prev ->
                            Left $ DuplicateNamedParam pos name (getPos prev)
      (count, names, pps, nps) <- foldM once (0, [], [], Map.empty) params
      -- Because foldM is a foldl, we need to reverse names and pps
      Right (count, reverse names, reverse pps, nps)

  let nameinfo = NamedParamInfo numPositional namedNames

  let ret' = case ret of
        (Nothing, r) ->
              r
        (Just _, r) ->
              -- This is not allowed by the grammar
              panic "mkFuncType" ["Return value was named"]

  Right $ tFun pos nameinfo posParams namedParams ret'

}
