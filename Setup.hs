import Control.Exception
import Control.Monad (unless)
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenPackageModulesDir)
import Distribution.PackageDescription (emptyHookedBuildInfo, allBuildInfo)
import System.Directory (createDirectoryIfMissing, findExecutable)
import System.FilePath ((</>))
import System.Process (readProcess)
import System.Exit

main = defaultMainWithHooks myHooks
  where myHooks = simpleUserHooks { buildHook = myBuild }

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  hasGit <- findExecutable "git"

  let gitfailure :: SomeException -> IO String
      gitfailure _e = return "<non-dev-build> "

  desc <- case hasGit of
            Just git -> readProcess "git" ["describe", "--always", "--dirty"] ""
                        `catch` gitfailure
            Nothing -> return "<VCS-less build> "

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "hash :: String"
    , "hash = " ++ show (init desc)
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags

