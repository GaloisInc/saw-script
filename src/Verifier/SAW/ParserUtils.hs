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
decSharedDataTypeApp :: String
                     -> TypedDataType
                     -> DecWriter ()
decSharedDataTypeApp nm dt = do
  let sym = show (dtName dt)
  let n = piArgCount (dtType dt)
  -- Get type of result.
  tp <- lift $ sharedFunctionType n
  -- Get value of result.
  decExpr <- lift $ [| \sc -> do
    m <- scModule sc
    case findDataType m (parseIdent $(stringE sym)) of
      Nothing -> fail $(stringE ("Could not find " ++ sym))
      Just dt ->
        $(do let applyFn expr = [| scDataTypeApp sc (dtName dt) $(expr) |]
             case n of
               0 -> applyFn [|[]|]
               _ -> do
                 nms <- replicateM n (newName "x")
                 let expr = ListE (VarE <$> nms)
                 [|return $(LamE (VarP <$> nms) <$> applyFn (return expr))|])
    |]
    -- Add declarations for ctor.
  let decName = mkName nm
  let decs = [ SigD decName tp
             , FunD decName [ Clause [] (NormalB decExpr) [] ]
             ]
  modify $ \s -> addDecs s decs


-- Given a ctor with the type
--   c : T1 -> ... -> TN -> T
-- This hads a declaration of the function.
-- scApply(modulename)(upcase c)
--   :: SharedContext s
--   -> IO (SharedTerm s -> ... -> SharedTerm s -> IO (SharedTerm s)  
decSharedCtorApp :: String
                 -> TypedCtor
                 -> DecWriter ()
decSharedCtorApp nm c = do
  let cName = show(ctorName c)
  let n = piArgCount (ctorType c)
  -- Get type of result.
  tp <- lift $ sharedFunctionType n
  -- Get value of result.
  decExpr <- lift $ [| \sc -> do
    m <- scModule sc
    case findCtor m (parseIdent $(stringE cName)) of
      Nothing -> fail $(stringE ("Could not find " ++ cName))
      Just cExpr ->
        $(do let applyFn expr = [| scCtorApp sc (ctorName cExpr) $(expr) |]
             case n of
               0 -> applyFn [|[]|]
               _ -> do
                 nms <- replicateM n (newName "x")
                 let expr = ListE (VarE <$> nms)
                 [|return $(LamE (VarP <$> nms) <$> applyFn (return expr))|])
    |]
    -- Add declarations for ctor.
  let decName = mkName nm
  let decs = [ SigD decName tp
             , FunD decName [ Clause [] (NormalB decExpr) [] ]
             ]
  modify $ \s -> addDecs s decs

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
    let iName = show (defIdent def)
    -- Get type of result.
    tp <- sharedFunctionType n
    -- Get value of result.
    decExpr <- [| \sc -> do
      m <- scModule sc
      case findDef m (parseIdent $(stringE iName)) of
        Nothing -> fail ($(stringE ("Could not find " ++ iName ++ " in "))
                              ++ show (moduleName m))
        Just typedDef -> do
          $(case n of
              0 -> [| scDefTerm sc typedDef |]
              _ -> [| do d <- scDefTerm sc typedDef
                         return
                           $(do let procStmt :: Exp -> [ExpQ] -> Q [Stmt]
                                    procStmt r [h] = do
                                      return <$> noBindS [|scApply sc $(return r) $(h)|]
                                    procStmt r (h:l) = do
                                      r0 <- newName "r"
                                      stmt <- bindS (varP r0) [|scApply sc $(return r) $(h)|]
                                      (stmt:) <$> procStmt (VarE r0) l
                                    procStmt _ [] = error "Unexpected empty list to procStmt"
                                nms <- replicateM n $ newName "x"
                                de <- [|d|]
                                LamE (VarP <$> nms) . DoE <$> procStmt de (varE <$> nms))|])
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
  forM_ (moduleDataTypes m) $ \dt -> do
    let nm = "sc" ++ mnm ++ identName (dtName dt)
    decSharedDataTypeApp nm dt
  forM_ (moduleCtors m) $ \c -> do
    let nm = "scApply" ++ mnm ++ identName (ctorName c)
    decSharedCtorApp nm c
  forM_ (moduleDefs m) $ \d -> do
    let nm = "scApply" ++ mnm ++ camelCase (identName (defIdent d))
    decSharedDefApp nm (piArgCount (defType d)) d