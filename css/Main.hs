{-# LANGUAGE RankNTypes #-}

module Main where

import System.Environment( getArgs )
import System.Exit( exitFailure )

import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.ModuleSystem as CM
import qualified Cryptol.ModuleSystem.Env as CME
import qualified Cryptol.Parser as P
import           Cryptol.Utils.PP


import qualified Verifier.SAW.Cryptol as C
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedAST
import qualified Verifier.SAW.Cryptol.Prelude


import qualified Data.ABC as ABC
import qualified Verifier.SAW.Simulator.BitBlast as BBSim

main :: IO ()
main = getArgs >>= cssMain

cssMain :: [String] -> IO ()
cssMain [] = putStrLn "usage: css <cryptol input> <aig output> <function name>"
cssMain [f,o,funcName] = do
    (e,warn) <- CM.loadModuleByPath f
    mapM_ (print . pp) warn
    case e of
       Left msg -> print msg >> exitFailure
       Right (_,menv) -> processModule menv o funcName

processModule :: CM.ModuleEnv -> FilePath -> String -> IO ()
processModule menv fout funcName = do
   let m = Verifier.SAW.Cryptol.Prelude.cryptolModule
   sc <- mkSharedContext m
   tm <- extractCryptol sc menv funcName
   writeAIG sc fout tm

writeAIG :: SharedContext s -> FilePath -> SharedTerm s -> IO ()
writeAIG sc f t = withBE $ \be -> do
  ls <- BBSim.bitBlastTerm be sc t
  ABC.writeAiger f (ABC.Network be (ABC.bvToList ls))
  return ()

withBE :: (forall s . ABC.GIA s -> IO a) -> IO a
withBE f = do
  ABC.withNewGraph ABC.giaNetwork f

extractCryptol :: SharedContext s -> CM.ModuleEnv -> String -> IO (SharedTerm s)
extractCryptol sc modEnv input = do
  let declGroups = concatMap T.mDecls (CME.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  pexpr <-
    case P.parseExpr input of
      Left err -> fail (show (pp err))
      Right x -> return x
  (exprResult, exprWarnings) <- CM.checkExpr pexpr modEnv
  mapM_ (print . pp) exprWarnings
  ((expr, schema), _modEnv') <-
    case exprResult of
      Left err -> fail (show (pp err))
      Right x -> return x
  putStrLn $ "Extracting expression of type " ++ show (pp (schemaNoUser schema))
  C.importExpr sc env expr

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec [ (n, typeNoUser ty) | (n, ty) <- fields ]

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)
