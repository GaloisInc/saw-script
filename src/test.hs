
import SAWScript.AST
import SAWScript.Unify

import SAWScript.LiftPoly
import SAWScript.TypeCheck
import SAWScript.GroundType

import Control.Monad
import Data.Foldable
import Data.Traversable

testAll m = case runComp m of
  Left e   -> error e
  Right m' -> m'

runComp = liftPoly >=> typeCheck >=> groundType

