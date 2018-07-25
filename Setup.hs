import Control.Monad (unless)
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenPackageModulesDir)
import Distribution.PackageDescription (emptyHookedBuildInfo, allBuildInfo)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import System.Process (readProcess)

main = defaultMainWithHooks myHooks
  where myHooks = simpleUserHooks { buildHook = myBuild }

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  desc <- readProcess "git" ["describe", "--always", "--dirty"] ""

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "hash :: String"
    , "hash = " ++ show (init desc)
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags

