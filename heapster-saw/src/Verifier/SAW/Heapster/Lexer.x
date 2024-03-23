{
module Verifier.SAW.Heapster.Lexer (lexer) where

import Verifier.SAW.Heapster.Located (Located(..), Pos(..))
import Verifier.SAW.Heapster.Token (Token(..))

}

%wrapper "posn"

$alpha = [a-z A-Z]
$digit = [0-9]

heapster :-

$white+                         ;
"("                             { token_ TOpenParen     }
")"                             { token_ TCloseParen    }
"["                             { token_ TOpenBrack     }
"]"                             { token_ TCloseBrack    }
"{"                             { token_ TOpenBrace     }
"}"                             { token_ TCloseBrace    }
"<"                             { token_ TOpenAngle     }
">"                             { token_ TCloseAngle    }
":"                             { token_ TColon         }
";"                             { token_ TSemicolon     }
"."                             { token_ TDot           }
","                             { token_ TComma         }
"+"                             { token_ TPlus          }
"-"                             { token_ TMinus         }
"*"                             { token_ TStar          }
"@"                             { token_ TAt            }
"-o"                            { token_ TLoli          }
"|->"                           { token_ TMapsTo        }
"=="                            { token_ TEqual         }
"/="                            { token_ TNotEqual      }
"<u"                            { token_ TUnsignedLt    }
"<=u"                           { token_ TUnsignedLe    }
"or"                            { token_ TOr            }
"true"                          { token_ TTrue          }
"false"                         { token_ TFalse         }
"any"                           { token_ TAny           }
"empty"                         { token_ TEmpty         }
"exists"                        { token_ TExists        }
"eq"                            { token_ TEq            }
"unit"                          { token_ TUnit          }
"bool"                          { token_ TBool          }
"nat"                           { token_ TNat           }
"bv"                            { token_ TBV            }
"array"                         { token_ TArray         }
"ptr"                           { token_ TPtr           }
"perm"                          { token_ TPerm          }
"llvmptr"                       { token_ TLlvmPtr       }
"llvmfunptr"                    { token_ TLlvmFunPtr    }
"llvmframe"                     { token_ TLlvmFrame     }
"llvmshape"                     { token_ TLlvmShape     }
"llvmblock"                     { token_ TLlvmBlock     }
"llvmword"                      { token_ TLlvmWord      }
"lifetime"                      { token_ TLifetime      }
"lowned"                        { token_ TLOwned        }
"lcurrent"                      { token_ TLCurrent      }
"rwmodality"                    { token_ TRWModality    }
"permlist"                      { token_ TPermList      }
"struct"                        { token_ TStruct        }
"shape"                         { token_ TShape         }
"emptysh"                       { token_ TEmptySh       }
"falsesh"                       { token_ TFalseSh       }
"eqsh"                          { token_ TEqSh          }
"ptrsh"                         { token_ TPtrSh         }
"fieldsh"                       { token_ TFieldSh       }
"arraysh"                       { token_ TArraySh       }
"tuplesh"                       { token_ TTupleSh       }
"exsh"                          { token_ TExSh          }
"orsh"                          { token_ TOrSh          }
"memblock"                      { token_ TMemBlock      }
"free"                          { token_ TFree          }
"always"                        { token_ TAlways        }
"R"                             { token_ TR             }
"W"                             { token_ TW             }
$alpha [$alpha $digit _ ']*     { token TIdent          }
$digit+                         { token (TNatLit . read)}
.                               { token TError          }

{

-- | Convert alex-specific position type to public interface.
mkPos :: AlexPosn -> Pos
mkPos (AlexPn x y z) = Pos x y z

-- | Helper for building a 'Located' 'Token'
token :: (String -> Token) -> AlexPosn -> String -> Located Token
token tok p str = Located (mkPos p) (tok str)

-- | Helper for building a 'Located' 'Token' with no argument
token_ :: Token -> AlexPosn -> String -> Located Token
token_ tok p _ = Located (mkPos p) tok

-- | Transform input text into a token stream. Errors are
-- reported inline with the 'TError' token.
lexer ::
  String                {- ^ input text                 -} ->
  [Located Token]       {- ^ token stream               -}
lexer = alexScanTokens
}
