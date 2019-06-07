-- | The CrucibleSetup monad
module SAWScript.Crucible.Common.CrucibleSetup where

import           Control.Lens

import           SAWScript.Crucible.Common
import qualified SAWScript.Crucible.Common.MethodSpec as MS
import           SAWScript.Crucible.LLVM.CrucibleLLVM (LLVM)
import           SAWScript.Value

currentState :: Lens' (MS.CrucibleSetupState ext) (MS.StateSpec ext)
currentState f x = case x^. MS.csPrePost of
  PreState  -> MS.csMethodSpec (MS.csPreState f) x
  PostState -> MS.csMethodSpec (MS.csPostState f) x

addPointsTo :: MS.PointsTo ext -> CrucibleSetup ext ()
addPointsTo pt = currentState . MS.csPointsTos %= (pt : )

addCondition :: MS.SetupCondition ext
             -> CrucibleSetup ext ()
addCondition cond = currentState . MS.csConditions %= (cond : )
