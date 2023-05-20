import Control.Exception
import Control.Monad (unless)
import Data.List (find)
import Distribution.Simple
import Distribution.Simple.BuildPaths (autogenPackageModulesDir)
import Distribution.PackageDescription (emptyHookedBuildInfo, allBuildInfo)
import System.Directory (createDirectoryIfMissing, findExecutable, withCurrentDirectory)
import System.FilePath ((</>))
import System.Process (readProcess)
import System.Exit

main = defaultMainWithHooks myHooks
  where myHooks = simpleUserHooks { buildHook = myBuild }

withExe dir exe_str on_no_exe on_fail m = do
  mb <- findExecutable exe_str

  let onfailure :: SomeException -> IO String
      onfailure _e = return on_fail

  case mb of
    Just exe -> withCurrentDirectory dir (m exe)
                `catch` onfailure
    Nothing -> return on_no_exe

myBuild pd lbi uh flags = do
  let dir = autogenPackageModulesDir lbi
  createDirectoryIfMissing True dir

  desc <- withExe "." "git" "<VCS-less build>" "<non-dev-build>" $ \git ->
    init <$> readProcess git ["describe", "--always", "--dirty"] ""

  aig_desc <- withExe "deps/aig" "git" "unknown" "unknown" $ \git -> do
    init <$> readProcess git ["describe", "--always", "--dirty"] ""
                  
  w4_desc <- withExe "deps/what4" "git" "unknown" "unknown" $ \git -> do
    init <$> readProcess git ["describe", "--always", "--dirty"] ""

  sbv_ver <- withExe "." "cabal" "unknown" "unknown" $ \cabal -> do
    ls <- lines <$> readProcess cabal ["freeze"] ""
    wss <- fmap words <$> lines <$> readFile (ls !! 1)
    case find (\ws -> (ws !! 0) == "any.sbv") wss of
      Just ws -> return $ init $ drop 2 $ ws !! 1
      Nothing -> return "unknown"

  writeFile (dir </> "GitRev.hs") $ unlines
    [ "module GitRev where"
    , "hash :: String"
    , "hash = " ++ show desc
    , "aigHash :: String"
    , "aigHash = " ++ show aig_desc
    , "w4Hash :: String"
    , "w4Hash = " ++ show w4_desc
    , "sbvVer :: String"
    , "sbvVer = " ++ show sbv_ver
    ]

  unless (null $ allBuildInfo pd) $
    (buildHook simpleUserHooks) pd lbi uh flags

