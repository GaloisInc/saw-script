import Control.Exception
import Control.Monad (unless)
import Data.Maybe (isJust)
import Data.List (intercalate)
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
        return $ do -- in Maybe
            txt <- output
            -- remove the trailing newline
            return $ init txt

  let gitbranch = do
        output <- runGit ["branch", "--points-at", "HEAD"]
        return $ do -- in Maybe
            txt <- output
            -- We get one or more lines indented by either two spaces
            -- or "* ". Split the lines, drop the prefix, and concat
            -- with a space to separate.
            return $ intercalate " " $ map (drop 2) $ lines txt

  let gitlog args =
        -- This apparently doesn't produce a newline if the
        -- output isn't a tty.
        runGit ("log" : args)

  desc     <- gitdescribe
  aig_desc <- withCurrentDirectory "deps/aig" $ gitdescribe
  w4_desc  <- withCurrentDirectory "deps/what4" $ gitdescribe

  branch <- gitbranch

  rme_desc <- gitlog ["--max-count=1", "--pretty=format:%h", "--", "rme"]

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "-- | Whether git was found at compile time, which affects how we"
    , "--   interpret Nothing in the data below"
    , "foundGit :: Bool"
    , "foundGit = " ++ show (isJust hasGit)
    , "-- | The git commit hash for the HEAD of saw-script at compile-time"
    , "hash :: Maybe String"
    , "hash = " ++ show desc
    , "-- | The git branch string for the HEAD of saw-script at compile-time"
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
