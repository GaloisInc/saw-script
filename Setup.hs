import Control.Exception
import Control.Monad (unless)
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenPackageModulesDir)
import Distribution.PackageDescription (emptyHookedBuildInfo, allBuildInfo)
import System.Directory (createDirectoryIfMissing, findExecutable)
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)
import System.Exit

main = defaultMainWithHooks myHooks
  where myHooks = simpleUserHooks { buildHook = myBuild }

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  hasGit <- findExecutable "git"

  let gitfailure :: SomeException -> IO (ExitCode, String, String)
      gitfailure _e = return (ExitFailure 1, "<non-dev-build> ", "")
      middle (_,v,_) = v

  desc <- case hasGit of
            Just git -> middle <$> readProcessWithExitCode "git" ["describe", "--always", "--dirty"] ""
                                   `catch` gitfailure
            Nothing -> return "<VCS-less build> "

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "hash :: String"
    , "hash = " ++ show (init desc)
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags

