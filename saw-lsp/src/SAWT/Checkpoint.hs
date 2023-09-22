module SAWT.Checkpoint where

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HMap
import Data.Hashable (Hashable (..))
import SAWScript.AST qualified as SAW
import SAWScript.Value qualified as SAW
import Util.Stack as Stack (Stack, emptyStack, fromList, push)

--------------------------------------------------------------------------------

newtype Script = Script (Stack SAW.Stmt)
  deriving (Eq)

instance Hashable Script where
  hashWithSalt salt (Script stmts) = hashWithSalt salt stmts

mkContext :: [SAW.Stmt] -> Script
mkContext = Script . Stack.fromList

emptyScript :: Script
emptyScript = Script emptyStack

addStmtToScript :: SAW.Stmt -> Script -> Script
addStmtToScript stmt (Script stmts) = Script (push stmt stmts)

--------------------------------------------------------------------------------

newtype Checkpoints = Checkpoints (HashMap Script Checkpoint)

instance Semigroup Checkpoints where
  Checkpoints c1 <> Checkpoints c2 = Checkpoints (c1 <> c2)

instance Monoid Checkpoints where
  mempty = Checkpoints mempty

-- | The results of executing a `Script`
data Checkpoint = Checkpoint
  { ckEnv :: SAW.TopLevelCheckpoint,
    ckVal :: SAW.Value,
    ckOutput :: [String]
  }

createCheckpoint :: SAW.TopLevelCheckpoint -> SAW.Value -> [String] -> Checkpoint
createCheckpoint ckEnv ckVal ckOutput = Checkpoint {..}

addCheckpoint :: Script -> Checkpoint -> Checkpoints -> Checkpoints
addCheckpoint script ck (Checkpoints cks) = Checkpoints (HMap.insert script ck cks)

findCheckpoint :: Checkpoints -> Script -> Maybe Checkpoint
findCheckpoint (Checkpoints cks) script = cks HMap.!? script
