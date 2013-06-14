
module TestRenamer where

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.RenameRefs
import qualified Data.Map as M

type Exp  = Expr UnresolvedName ResolvedT
type RExp = Expr ResolvedName TCheckT

testMod3 :: OutgoingModule
testMod3 = Module (ModuleName [] "Test")
  (M.fromList
    [ ( "foo" , Function "a" Nothing
                  (Function "b" Nothing (Var (LocalName "a") Nothing) Nothing ) Nothing)
    ])
  M.empty
  M.empty

testMod1 :: Exp -> IncomingModule
testMod1 e = Module (ModuleName [] "Test")
  (M.fromList
    [ ( "foo" , e )
    ])
  M.empty
  M.empty

testMod2 :: Exp -> RExp -> IncomingModule
testMod2 e1 e2 = Module (ModuleName [] "Test")
  (M.fromList
    [ ( "foo" , e1 )
    ])
  M.empty
  (M.fromList
    [ ( ModuleName [] "Foo"
      , Module (ModuleName [] "Foo")
          (M.fromList
            [ ( "foo" , e2 )
            ])
          M.empty
          M.empty
      )
    ])

-- locally bound in function
func1Example = lambda "a" (var "a")
func2Example = lambda "a" (lambda "b" (var "a"))
func3Example = lambda "a" (lambda "b" (var "b"))
-- demonstrates shadowing behavior
func4Example = lambda "a" (lambda "a" (var "a"))

-- locally bound in let
let1Example = testMod1 $ LetBlock [("a", int 1)] (var "a")
-- failuring on duplicate bindings
let2Example = testMod1 $ LetBlock [("a", int 1), ("a", int 2)] (var "a")

-- top level binding with unqualified name
var1Example = testMod1 $ var "foo"
-- demonstrates precedence of local binding over top level binding
func5Example = testMod1 $ lambda "foo" $ var "foo"
-- top level binding with qualified name
var2Example = testMod1 $ qvar ["Test"] "foo"
-- qualified names will not be caught by local bindings
func6Example = testMod1 $ lambda "foo" (qvar ["Test"] "foo")
-- failuring on unbound name
var3Example = testMod1 $ var "bar"

-- failuring on ambiguous reference
mod2Test1 = testMod2 (var "foo") (Z 1 z)
-- resolving to dependency module
mod2Test2 = testMod2 (qvar ["Foo"] "foo") (Z 1 z)
-- resolving to local module
mod2Test3 = testMod2 (qvar ["Test"] "foo") (Z 1 z)


-- Helpers {{{

lambda :: Name -> Exp -> Exp
lambda x body = Function x Nothing body Nothing

app :: Exp -> Exp -> Exp
app f v = Application f v Nothing

var :: Name -> Exp
var x = Var (UnresolvedName [] x) Nothing

int :: Integer -> Exp
int n = Z n Nothing

qvar :: [Name] -> Name -> Exp
qvar ns x = Var (UnresolvedName ns x) Nothing

runTest :: IncomingModule -> IO ()
runTest mod = runE m putStrLn print
  where
  m = renameRefs mod

-- }}}

