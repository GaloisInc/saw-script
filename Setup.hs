import Control.Exception
import Control.Monad (unless)
import Data.List (find)
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenPackageModulesDir)
import Distribution.PackageDescription (emptyHookedBuildInfo, allBuildInfo)
import System.Directory
import System.FilePath ((</>))
import System.Process (readProcess, callProcess)
import System.Exit

main = defaultMainWithHooks myHooks
  where myHooks = simpleUserHooks { buildHook = myBuild }

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  hasGit <- findExecutable "git"

  let gitfailure :: a -> SomeException -> IO a
      gitfailure a _e = return a

  let gitdescribe dir m on_no_exe on_fail = case hasGit of
        Just exe -> withCurrentDirectory dir (m <$>
                      readProcess "git" ["describe", "--always", "--dirty"] "")
                    `catch` gitfailure on_fail
        Nothing -> return on_no_exe

  let gitbranch dir m on_no_exe on_fail = case hasGit of
        Just exe -> withCurrentDirectory dir (m <$>
                      readProcess "git" ["branch", "--points-at", "HEAD"] "")
                    `catch` gitfailure on_fail
        Nothing -> return on_no_exe

  desc     <- gitdescribe "." init "<VCS-less build>" "<non-dev-build>"
  aig_desc <- gitdescribe "deps/aig" (Just . init) Nothing Nothing
  w4_desc  <- gitdescribe "deps/what4" (Just . init) Nothing Nothing

  branch <- gitbranch "." (drop 2 . init) "<VCS-less build>" "<non-dev-build>"

  rme_desc <- case hasGit of
    Just exe -> (Just <$> readProcess "git" ["log", "--max-count=1", "--pretty=format:%h", "--", "rme"] "")
                `catch` gitfailure Nothing
    Nothing -> return Nothing

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "-- | Strings describing the HEAD of saw-script at compile-time"
    , "hash :: String"
    , "hash = " ++ show desc
    , "branch :: String"
    , "branch = " ++ show branch
    , "-- | String describing the HEAD of the deps/aig submodule at compile-time"
    , "aigHash :: Maybe String"
    , "aigHash = " ++ show aig_desc
    , "-- | String describing the HEAD of the deps/what4 submodule at compile-time"
    , "what4Hash :: Maybe String"
    , "what4Hash = " ++ show w4_desc
    , "-- | String describing the most recent commit which modified the rme directory"
    , "-- at compile-time"
    , "rmeHash :: Maybe String"
    , "rmeHash = " ++ show rme_desc
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags
