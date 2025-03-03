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

  let runGit args = case hasGit of
        Nothing ->
            return Nothing
        Just exe -> do
            let gitfailure :: SomeException -> IO (Maybe a)
                gitfailure _e = return Nothing
            output <- do
                Just <$> readProcess "git" args ""
              `catch` gitfailure
            return output

  let gitdescribe = do
        output <- runGit ["describe", "--always", "--dirty"]
        return $ case output of
            Nothing -> Nothing
            Just txt ->
                -- remove the trailing newline
                Just $ init txt

  let gitbranch = do
        output <- runGit ["branch", "--points-at", "HEAD"]
        return $ case output of
            Nothing -> Nothing
            Just txt ->
                -- remove the trailing newline and leading "* "
                Just $ drop 2 $ init txt

  let gitlog args =
        runGit ("log" : args)

  desc     <- gitdescribe
  aig_desc <- withCurrentDirectory "deps/aig" $ gitdescribe
  w4_desc  <- withCurrentDirectory "deps/what4" $ gitdescribe

  branch <- gitbranch

  rme_desc <- gitlog ["--max-count=1", "--pretty=format:%h", "--", "rme"]

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
