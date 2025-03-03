import Control.Exception
import Control.Monad (unless)
import Data.Maybe (isJust)
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

  let gitdescribe m = case hasGit of
        Just exe -> ((Just . m) <$>
                      readProcess "git" ["describe", "--always", "--dirty"] "")
                    `catch` gitfailure Nothing
        Nothing -> return Nothing

  let gitbranch m = case hasGit of
        Just exe -> ((Just . m) <$>
                      readProcess "git" ["branch", "--points-at", "HEAD"] "")
                    `catch` gitfailure Nothing
        Nothing -> return Nothing

  desc     <- gitdescribe init
  aig_desc <- withCurrentDirectory "deps/aig" $ gitdescribe init
  w4_desc  <- withCurrentDirectory "deps/what4" $ gitdescribe init

  branch <- gitbranch (drop 2 . init)

  rme_desc <- case hasGit of
    Just exe -> (Just <$> readProcess "git" ["log", "--max-count=1", "--pretty=format:%h", "--", "rme"] "")
                `catch` gitfailure Nothing
    Nothing -> return Nothing

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "-- | Strings describing the HEAD of saw-script at compile-time"
    , "foundGit :: Bool"
    , "foundGit = " ++ show (isJust hasGit)
    , "hash :: Maybe String"
    , "hash = " ++ show desc
    , "branch :: Maybe String"
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
