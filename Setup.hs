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

onfailure :: a -> SomeException -> IO a
onfailure on_fail _e = return on_fail

withExe dir exe_str on_no_exe on_fail m = do
  mb <- findExecutable exe_str

  case mb of
    Just exe -> withCurrentDirectory dir (m exe)
                `catch` onfailure on_fail
    Nothing -> return on_no_exe

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  desc <- withExe "." "git" "<VCS-less build>" "<non-dev-build>" $ \git ->
    init <$> readProcess git ["describe", "--always", "--dirty"] ""

  aig_desc <- withExe "deps/aig" "git" Nothing Nothing $ \git -> do
    Just . init <$> readProcess git ["describe", "--always", "--dirty"] ""
                  
  w4_desc <- withExe "deps/what4" "git" Nothing Nothing $ \git -> do
    Just . init <$> readProcess git ["describe", "--always", "--dirty"] ""

  sbv_ver <- withExe "." "cabal" Nothing Nothing $ \cabal -> do
    ex <- doesFileExist "cabal.project.freeze"
    unless ex $ callProcess cabal ["freeze"]
    wss <- fmap words <$> lines <$> readFile "cabal.project.freeze"
    unless ex $ removeFile "cabal.project.freeze"
    case find (\ws -> (ws !! 0) == "any.sbv") wss of
      Just ws -> return . Just . init . drop 2 $ ws !! 1
      Nothing -> return Nothing

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "hash :: String"
    , "hash = " ++ show desc
    , "aigHash :: Maybe String"
    , "aigHash = " ++ show aig_desc
    , "what4Hash :: Maybe String"
    , "what4Hash = " ++ show w4_desc
    , "sbvVersion :: Maybe String"
    , "sbvVersion = " ++ show sbv_ver
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags

