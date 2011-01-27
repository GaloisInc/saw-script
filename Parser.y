{
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -fno-warn-unused-binds        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module SAWScript.Parser(parseSAW) where

import SAWScript.MethodAST
import SAWScript.Token
import SAWScript.Utils
import {-# SOURCE #-} SAWScript.ParserActions
}

%expect 0
%tokentype { Token Pos }
%monad { Parser }
%lexer { lexer } { TEOF _ }
%error { parseError }
%name parseSAW VerifierCommands

%token
   import { TImport _ }
   str    { TLit _ $$ }
   ';'    { TSemi _   }
%%

VerifierCommands :: { [VerifierCommand] }
VerifierCommands : {- empty -}                          { []      }
                 | VerifierCommands VerifierCommand ';' { $2 : $1 }

VerifierCommand :: { VerifierCommand }
VerifierCommand : import str { ImportCommand (getPos $1) $2 }
