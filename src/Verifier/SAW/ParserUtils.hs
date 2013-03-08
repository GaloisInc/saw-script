{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.ParserUtils
 ( module Verifier.SAW.TypedAST
   -- * Parser utilities.
 , readModuleFromFile
   -- * Template haskell utilities.
 , DecWriter
 , runDecWriter
 , DecExp(..)
 , importExp
 , mkDecModule
 , decSharedCtorApp
 , decSharedDefApp
 , decSharedModuleFns
 ) where

import Control.Applicative
import Control.Monad.State hiding (forM_)
import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Unsafe (unsafePackAddressLen)
import Data.Char
import Data.Foldable
import Language.Haskell.TH
import Prelude hiding (foldl)
import System.Directory
import System.FilePath
import System.IO.Unsafe (unsafePerformIO)

#if __GLASGOW_HASKELL__ >= 706
#else
import qualified Data.ByteString.Lazy.UTF8 as UTF8
#endif

import qualified Verifier.SAW.Grammar as Un
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Typechecker

camelCase :: String -> String
camelCase (h:l) = toUpper h : l
camelCase [] = []

-- | Read module from file with givne imports.
readModuleFromFile :: [Module] -> FilePath -> IO Module
readModuleFromFile imports path = do
  base <- getCurrentDirectory
  b <- BL.readFile path
  readModule imports base path b


-- | Returns a module containing the standard prelude for SAW.
readModule :: [Module] -> FilePath -> FilePath -> BL.ByteString -> IO Module
readModule imports base path b = do
  let (m,[]) = Un.runParser base path b Un.parseSAW
  case tcModule imports m of
    Left e -> fail $ "Errors while reading module:\n" ++ show e
    Right r -> return r

readByteStringExpr :: ExpQ -> FilePath -> Q Exp
readByteStringExpr modules path = do
  let nm = takeFileName path
  base <- runIO $ getCurrentDirectory
  compile_b <- runIO $ BL.readFile path
  case Un.runParser base nm compile_b Un.parseSAW of
    (_,[]) -> do
      let blen :: Int
          blen = fromIntegral (BL.length compile_b)
#if __GLASGOW_HASKELL__ >= 706
          primExpr = LitE $ StringPrimL $ BL.unpack compile_b
#else
          primExpr = LitE $ StringPrimL $ UTF8.toString compile_b
#endif
      packExpr <- [| do
           b <- unsafePackAddressLen blen $(return primExpr)
           readModule $(modules) base path (BL.fromChunks [b])
        |]
      return packExpr
    (_,errors) -> fail $ "Failed to parse prelude:\n" ++ show errors


data DecWriterState = DecWriterState { dwDecs :: [Dec]
                                     }

addDecs :: DecWriterState -> [Dec] -> DecWriterState
addDecs dw decs = dw { dwDecs = dwDecs dw ++ decs }

type DecWriter = StateT DecWriterState Q

runDecWriter :: DecWriter () -> Q [Dec]
runDecWriter m = dwDecs <$> execStateT m s
  where s = DecWriterState { dwDecs = [] }


-- | Contains a value and an expression that will evaluate to it at runtime.
data DecExp a = DecExp { decExp :: !Exp
                       , decVal :: !a
                       }

-- | Define a declared
importExp :: ExpQ -> a -> DecWriter (DecExp a)
importExp eq m = do
  e <- lift eq
  return DecExp { decExp = e, decVal = m }

mkDecModule :: [DecExp Module] -> String -> FilePath -> DecWriter (DecExp Module)
mkDecModule modules decNameStr path = do
  let nm = takeFileName path
  StateT $ \s -> do
    base <- runIO $ getCurrentDirectory
    compile_b <- runIO $ BL.readFile path
    case Un.runParser base nm compile_b Un.parseSAW of
      (_,[]) -> return ()
      (_,errors) -> fail $ "Failed to parse module:\n" ++ show errors
    m <- runIO $ readModule (decVal <$> modules) base path compile_b
    let decName = mkName decNameStr
    let blen :: Int
        blen = fromIntegral (BL.length compile_b)
#if __GLASGOW_HASKELL__ >= 706
        primExpr = LitE $ StringPrimL $ BL.unpack compile_b
        noinlinePragma = InlineP decName NoInline FunLike AllPhases
#else
        primExpr = LitE $ StringPrimL $ UTF8.toString compile_b
        noinlinePragma = InlineP decName (InlineSpec False False Nothing)
#endif
    moduleTp <- [t| Module |]
    packExpr <- [| unsafePerformIO $ do
        b <- unsafePackAddressLen blen $(return primExpr)
        readModule $(return (ListE (decExp <$> modules))) base path (BL.fromChunks [b])
      |]
    let decs =  [ PragmaD noinlinePragma
                , SigD decName moduleTp
                , FunD decName [ Clause [] (NormalB packExpr) [] ]
                ]
    let dm = DecExp { decExp = VarE decName
                    , decVal  = m
                    }
    let s' = s `addDecs` decs
    return (dm, s')

-- @sharedFnType n@ returns the type of a function for generating function
-- applications.
sharedFunctionType :: Int -> Q Type
sharedFunctionType 0 =
    [t| forall s . SharedContext s -> IO (SharedTerm s) |]
sharedFunctionType n = do
    s <- newName "s"
    forallT [PlainTV s] (return [])
       [t| SharedContext $(varT s) -> IO $(go [t|SharedTerm $(varT s)|] n) |]
  where go nm 0 = [t| IO $(nm) |]
        go nm i = [t| $(nm) -> $(go nm (i-1)) |]


-- Given a ctor with the type
--   c : T1 -> ... -> TN -> T
-- This hads a declaration of the function.
-- scApply(modulename)(upcase c)
--   :: SharedContext s
--   -> IO (SharedTerm s -> ... -> SharedTerm s -> IO (SharedTerm s)
decSharedCtorApp :: String
                 -> Int
                 -> TypedCtor
                 -> DecWriter ()
decSharedCtorApp nm n c = do
  StateT $ \s -> do
    let cName = identName (ctorName c)
    -- Get type of result.
    tp <- sharedFunctionType n
    -- Get value of result.
    decExpr <- [| \sc -> do
       m <- scModule sc
       case findExportedCtor m $(stringE cName) of
         Nothing -> fail $(stringE ("Could not find " ++ cName))
         Just cExpr ->
           $(case n of
               0 -> [|scApplyCtor sc cExpr []|]
               _ -> [|return $(retFn n [])|]
                 where retFn 0 rArgs =
                         [|scApplyCtor sc cExpr $(listE (reverse rArgs)) |]
                       retFn i rArgs = do
                         x <- newName "x"
                         LamE [VarP x] <$> retFn (i-1) (varE x:rArgs))
     |]
    -- Add declarations for ctor.
    let decName = mkName nm
    let decs = [ SigD decName tp
               , FunD decName [ Clause [] (NormalB decExpr) [] ]
               ]
    return ((), s `addDecs` decs)

-- Given a ctor with the type
--   c : T1 -> ... -> TN -> T
-- This hads a declaration of the function:
--   scApply(modulename)(upcase c)
--     :: SharedContext s
--     -> IO (SharedTerm s -> ... -> SharedTerm s -> IO (SharedTerm s)
decSharedDefApp :: String
                -> Int
                -> TypedDef
                -> DecWriter ()
decSharedDefApp nm n def = do
  StateT $ \st -> do
    let iName = identName (defIdent def)
    -- Get type of result.
    tp <- sharedFunctionType n
    -- Get value of result.
    decExpr <- [| \sc -> do
      m <- scModule sc
      case findExportedDef m $(stringE iName) of
        Nothing -> fail ($(stringE ("Could not find " ++ iName ++ " in "))
                              ++ show (moduleName m))
        Just typedDef -> do
          $(case n of
              0 -> [| scDefTerm sc typedDef |]
              _ -> [| do d <- scDefTerm sc typedDef
                         return
                           $(let procStmt :: Exp -> [ExpQ] -> [StmtQ] -> ExpQ
                                 procStmt r [h] rStmts = doE (reverse (stmt:rStmts))
                                   where stmt = noBindS [|scApply sc $(return r) $(h)|]
                                 procStmt r (h:l) rStmts = do
                                   r0 <- newName "r"
                                   let stmt = bindS (varP r0) [|scApply sc $(return r) $(h)|]
                                   procStmt (VarE r0) l (stmt:rStmts)
                                 procStmt _ [] _ = error "Unexpected empty list to procStmt"
                                 retFn :: Int -> [ExpQ] -> ExpQ
                                 retFn 0 rArgs = do
                                   de <- [|d|]
                                   procStmt de (reverse rArgs) []
                                 retFn i rArgs = do
                                   x <- newName "x"
                                   LamE [VarP x] <$> retFn (i-1) (varE x:rArgs)
                              in retFn n [])|])
     |]
    -- Add declarations for ctor.
    let decName = mkName nm
    let decs = [ SigD decName tp
               , FunD decName [ Clause [] (NormalB decExpr) [] ]
               ]
    return ((), st `addDecs` decs)

-- | Declare functions for creating shared terms for module.
decSharedModuleFns :: String -> Module -> DecWriter ()
decSharedModuleFns mnm m = do
  forM_ (moduleCtors m) $ \c -> do
    let nm = "scApply" ++ mnm ++ identName (ctorName c)
    let n = piArgCount (ctorType c)
    decSharedCtorApp nm n c
  forM_ (moduleDefs m) $ \d -> do
    let nm = "scApply" ++ mnm ++ camelCase (identName (defIdent d))
    decSharedDefApp nm (piArgCount (defType d)) d