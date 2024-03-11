{
{-# Language ViewPatterns #-}
module Verifier.SAW.Heapster.Parser (

  -- * Parser entry points
  parseCtx,
  parseType,
  parseFunPerm,
  parseExpr,
  parseValuePerms,

  -- * Parser errors
  ParseError(..),

  ) where

import GHC.Natural

import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.Token
import Verifier.SAW.Heapster.UntypedAST

}

%expect 0 -- shift/reduce conflicts

%tokentype      { Located Token                         }
%token
'('             { Located $$ TOpenParen                 }
')'             { Located $$ TCloseParen                }
'['             { Located $$ TOpenBrack                 }
']'             { Located $$ TCloseBrack                }
'{'             { Located $$ TOpenBrace                 }
'}'             { Located $$ TCloseBrace                }
'<'             { Located $$ TOpenAngle                 }
'>'             { Located $$ TCloseAngle                }
':'             { Located $$ TColon                     }
';'             { Located $$ TSemicolon                 }
'.'             { Located $$ TDot                       }
','             { Located $$ TComma                     }
'+'             { Located $$ TPlus                      }
'-'             { Located $$ TMinus                     }
'*'             { Located $$ TStar                      }
'@'             { Located $$ TAt                        }
'-o'            { Located $$ TLoli                      }
'|->'           { Located $$ TMapsTo                    }
'=='            { Located $$ TEqual                     }
'/='            { Located $$ TNotEqual                  }
'<u'            { Located $$ TUnsignedLt                }
'<=u'           { Located $$ TUnsignedLe                }
'or'            { Located $$ TOr                        }
'true'          { Located $$ TTrue                      }
'false'         { Located $$ TFalse                     }
'any'           { Located $$ TAny                       }
'empty'         { Located $$ TEmpty                     }
'exists'        { Located $$ TExists                    }
'eq'            { Located $$ TEq                        }
'unit'          { Located $$ TUnit                      }
'bool'          { Located $$ TBool                      }
'nat'           { Located $$ TNat                       }
'bv'            { Located $$ TBV                        }
'array'         { Located $$ TArray                     }
'ptr'           { Located $$ TPtr                       }
'perm'          { Located $$ TPerm                      }
'llvmptr'       { Located $$ TLlvmPtr                   }
'llvmfunptr'    { Located $$ TLlvmFunPtr                }
'llvmframe'     { Located $$ TLlvmFrame                 }
'llvmshape'     { Located $$ TLlvmShape                 }
'llvmblock'     { Located $$ TLlvmBlock                 }
'llvmword'      { Located $$ TLlvmWord                  }
'lifetime'      { Located $$ TLifetime                  }
'lowned'        { Located $$ TLOwned                    }
'lcurrent'      { Located $$ TLCurrent                  }
'lfinished'     { Located $$ TLFinished                 }
'rwmodality'    { Located $$ TRWModality                }
'permlist'      { Located $$ TPermList                  }
'struct'        { Located $$ TStruct                    }
'shape'         { Located $$ TShape                     }
'emptysh'       { Located $$ TEmptySh                   }
'falsesh'       { Located $$ TFalseSh                   }
'eqsh'          { Located $$ TEqSh                      }
'ptrsh'         { Located $$ TPtrSh                     }
'fieldsh'       { Located $$ TFieldSh                   }
'arraysh'       { Located $$ TArraySh                   }
'tuplesh'       { Located $$ TTupleSh                   }
'exsh'          { Located $$ TExSh                      }
'orsh'          { Located $$ TOrSh                      }
'memblock'      { Located $$ TMemBlock                  }
'free'          { Located $$ TFree                      }
'always'        { Located $$ TAlways                    }
'R'             { Located $$ TR                         }
'W'             { Located $$ TW                         }
IDENT           { (traverse tokenIdent -> Just $$)      }
NAT             { (traverse tokenNat   -> Just $$)      }


%monad          { Either ParseError                     }
%error          { errorP                                }

%name parseCtx          ctx
%name parseType         type
%name parseFunPerm      funPerm
%name parseExpr         expr
%name parseValuePerms   funPermList

%right    '.'
%left     'orsh'
%right    ';'
%left     'or'
%nonassoc '==' '/=' '<u' '<=u'
%left     '+'
%left     '*'
%nonassoc '@'
%left NEGPREC

%%

ctx ::                                          {[(Located String, AstType)]}
  : list(varType)                               { $1 }

type ::                                         { AstType }
  : '(' type ')'                                { $2 }
  | 'unit'                                      { TyUnit (pos $1) }
  | 'bool'                                      { TyBool (pos $1) }
  | 'nat'                                       { TyNat (pos $1) }
  | 'lifetime'                                  { TyLifetime (pos $1) }
  | 'rwmodality'                                { TyRwModality (pos $1) }
  | 'permlist'                                  { TyPermList (pos $1) }
  | 'bv'        NAT                             { TyBV        (pos $1) (locThing $2) }
  | 'llvmptr'   NAT                             { TyLlvmPtr   (pos $1) (locThing $2) }
  | 'llvmframe' NAT                             { TyLlvmFrame (pos $1) (locThing $2) }
  | 'llvmblock' NAT                             { TyLlvmBlock (pos $1) (locThing $2) }
  | 'llvmshape' NAT                             { TyLlvmShape (pos $1) (locThing $2) }
  | 'struct' '(' list(type) ')'                 { TyStruct (pos $1) $3 }
  | 'perm'   '(' type      ')'                  { TyPerm (pos $1) $3 }

expr ::                                         { AstExpr }
  : '(' expr ')'                                { $2 }
  | IDENT identArgs permOffset                  { ExVar (pos $1) (locThing $1) $2 $3 }
  | NAT                                         { ExNat (pos $1) (locThing $1) }
  | 'unit'                                      { ExUnit (pos $1) }
  | expr '+' expr                               { ExAdd (pos $2) $1 $3 }
    -- NB: Give negation the highest possible precedence to avoid shift/reduce
    -- conflicts with other operators, such as + and *.
  | '-' expr %prec NEGPREC                      { ExNeg (pos $1) $2 }
  | expr '*' expr                               { ExMul (pos $2) $1 $3 }
  | 'struct' '(' list(expr) ')'                 { ExStruct (pos $1) $3 }
  | lifetime 'array' '(' expr ',' expr ',' '<' expr ',' '*' expr ',' expr ')'
                                                { ExArray (pos $2) $1 $4 $6 $9 $12 $14 }
  | 'llvmword' '(' expr ')'                     { ExLlvmWord (pos $1) $3 }
  | 'llvmfunptr' '{' expr ',' expr '}' '(' funPerm ')'
                                                { ExLlvmFunPtr (pos $1) $3 $5 $8 }
  | 'llvmframe' '[' list(frameEntry) ']'        { ExLlvmFrame (pos $1) $3 }

-- Lifetimes

  | 'always'                                    { ExAlways (pos $1) }

-- RW Modalities

  | 'R'                                         { ExRead (pos $1) }
  | 'W'                                         { ExWrite (pos $1) }

-- Shapes

  | 'emptysh'                                   { ExEmptySh (pos $1) }
  | 'falsesh'                                   { ExFalseSh (pos $1) }
  | expr 'orsh' expr                            { ExOrSh (pos $2) $1 $3 }
  | expr ';' expr                               { ExSeqSh (pos $2) $1 $3 }
  | 'eqsh' '(' expr ',' expr ')'                { ExEqSh (pos $1) $3 $5 }
  | lifetime 'ptrsh' '(' expr ',' expr ')'      { ExPtrSh (pos $2) $1 (Just $4) $6 }
  | lifetime 'ptrsh' '('          expr ')'      { ExPtrSh (pos $2) $1 Nothing $4 }
  | 'fieldsh' '(' expr ',' expr ')'             { ExFieldSh (pos $1) (Just $3) $5 }
  | 'fieldsh' '('          expr ')'             { ExFieldSh (pos $1) Nothing $3 }
  | 'arraysh' '(' '<' expr ',' '*' expr ',' expr ')'
                                                { ExArraySh (pos $1) $4 $7 $9 }
  | 'tuplesh' '(' expr ')'                      { ExTupleSh (pos $1) $3 }
  | 'exsh' IDENT ':' type '.' expr              { ExExSh (pos $1) (locThing $2) $4 $6 }

-- Value Permissions

  | 'true'                                      { ExTrue (pos $1) }
  | 'false'                                     { ExFalse (pos $1) }
  | 'any'                                       { ExAny (pos $1) }
  | expr 'or' expr                              { ExOr (pos $2) $1 $3 }
  | 'eq' '(' expr ')'                           { ExEq (pos $1) $3 }
  | 'exists' IDENT ':' type '.' expr            { ExExists (pos $1) (locThing $2) $4 $6 }

  | lifetime 'memblock' '(' expr ',' expr ',' expr ',' expr ')'
                                                { ExMemblock (pos $2) $1 $4 $6 $8 $10 }
  | 'free' '(' expr ')'                         { ExFree (pos $1) $3 }
  | lifetime 'ptr' '(' '(' expr ',' expr ',' expr ')' '|->' expr ')'
                                                { ExPtr (pos $2) $1 $5 $7 (Just $9) $12 }
  | lifetime 'ptr' '(' '(' expr ','          expr ')' '|->' expr ')'
                                                { ExPtr (pos $2) $1 $5 $7 Nothing $10 }

  | 'shape' '(' expr ')'                        { ExShape (pos $1) $3}
  | 'lowned' lifetimes '(' list(varExpr) '-o' list1(varExpr) ')'
                                                { ExLOwned (pos $1) $2 $4 $6}
  | lifetime 'lcurrent'                         { ExLCurrent (pos $2) $1 }
  | 'lfinished'                                 { ExLFinished (pos $1) }

-- BV Props (Value Permissions)

  | expr '=='  expr                             { ExEqual (pos $2) $1 $3}
  | expr '/='  expr                             { ExNotEqual (pos $2) $1 $3}
  | expr '<u'  expr                             { ExLessThan (pos $2) $1 $3}
  | expr '<=u' expr                             { ExLessEqual (pos $2) $1 $3}

frameEntry ::                                   { (AstExpr, Natural) }
  : expr ':' NAT                                { ($1, locThing $3) }

identArgs ::                                    { Maybe [AstExpr]       }
  :                                             { Nothing               }
  | '<' list(expr) '>'                          { Just $2               }

permOffset ::                                   { Maybe AstExpr         }
  :                                             { Nothing               }
  | '@' expr                                    { Just $2               }

funPerm ::                                      { AstFunPerm }
  : '(' ctx ')' '.' funPermList '-o' funPermList
                                                { AstFunPerm (pos $6) $2 $5 [] $7 }
  | '(' ctx ')' '.' funPermList '-o' '(' ctx ')' '.' funPermList
                                                { AstFunPerm (pos $6) $2 $5 $8 $11 }

funPermList ::                                  { [(Located String, AstExpr)] }
  : 'empty'                                     { []                    }
  | list1(varExpr)                              { $1                    }

varExpr ::                                      { (Located String, AstExpr) }
  : IDENT ':' expr                              { ($1, $3)              }

varType ::                                      { (Located String, AstType) }
  : IDENT ':' type                              { ($1, $3)              }

lifetime ::                                     { Maybe AstExpr         }
  :                                             { Nothing               }
  | '[' expr ']'                                { Just $2               }

lifetimes ::                                    { [AstExpr]             }
  :                                             { []                    }
  | '[' list(expr) ']'                          { $2                    }

llvmFieldPermArray ::                           { ArrayPerm             }
  : lifetime '(' expr ',' expr ',' expr ')' '|->' expr
                                                { ArrayPerm (pos $9) $1 $3 $5 (Just $7) $10 }
  | lifetime '(' expr ','          expr ')' '|->' expr
                                                { ArrayPerm (pos $7) $1 $3 $5 Nothing $8 }

list(p) ::                                      { [p]                   }
  :                                             { []                    }
  | list1(p)                                    { $1                    }

list1(p) ::                                     { [p]                   }
  : list1R(p)                                   { reverse $1            }

list1R(p) ::                                    { [p]                   }
  :               p                             { [$1]                  }
  | list1R(p) ',' p                             { $3 : $1               }

{

-- | Errors that can terminate parsing.
data ParseError
  = UnexpectedToken Pos Token   -- ^ Unexpected token
  | UnexpectedEnd               -- ^ Unexpected end of input
  deriving Show

-- | Generate an error message from the remaining token stream.
errorP :: [Located Token] -> Either ParseError a
errorP (Located p t:_) = Left (UnexpectedToken p t)
errorP []              = Left UnexpectedEnd
}
