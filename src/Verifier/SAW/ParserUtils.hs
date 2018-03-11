{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

{- |
Module      : Verifier.SAW.ParserUtils
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.ParserUtils
 ( module Verifier.SAW.TypedAST
   -- * Parser utilities.
 , readModuleFromFile
   -- * Template haskell utilities.
 , DecWriter
 , runDecWriter
 , DecExp(..)
 , defineImport
 , defineModuleFromFile
 , declareDefTermF
 , declareSharedDataTypeApp
 , declareSharedCtorApp
 , declareSharedDefApp
 , declareSharedModuleFns
 , readByteStringExpr
 ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Lens
import Control.Monad.State
import qualified Data.ByteString.Lazy as BL
#if !MIN_VERSION_template_haskell(2,8,0)
import qualified Data.ByteString.Lazy.UTF8 as UTF8
#endif
import Data.ByteString.Unsafe (unsafePackAddressLen)
import Data.Maybe
import Language.Haskell.TH
#if MIN_VERSION_template_haskell(2,7,0)
import Language.Haskell.TH.Syntax (qAddDependentFile)
#endif
import System.Directory
import System.FilePath
import System.IO.Unsafe (unsafePerformIO)

import Text.PrettyPrint.ANSI.Leijen (nest)

import qualified Verifier.SAW.Grammar as Un
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Typechecker

-- | Creates a string primitive expression from a lazy bytestring.
stringPrimFromBS :: BL.ByteString -> Exp
#if MIN_VERSION_template_haskell(2,8,0)
stringPrimFromBS b = LitE $ StringPrimL $ BL.unpack b
#else
stringPrimFromBS b = LitE $ StringPrimL $ UTF8.toString b
#endif

-- | Returns a module containing the standard prelude for SAW.
readModule :: [Module] -> FilePath -> FilePath -> BL.ByteString -> Module
readModule imports base path b = do
  let (m,[]) = Un.parseSAW base path b
  case tcModule imports m of
    Left e -> error $ "Errors while reading module:\n" ++ show e
    Right r -> r

-- | Read module from file with givne imports.
readModuleFromFile :: [Module] -> FilePath -> IO Module
readModuleFromFile imports path = do
  base <- getCurrentDirectory
  b <- BL.readFile path
  return $ readModule imports base path b

readByteStringExpr :: ExpQ -> FilePath -> Q Exp
readByteStringExpr modules path = do
  let nm = takeFileName path
  base <- runIO $ getCurrentDirectory
  compile_b <- runIO $ BL.readFile path
  case Un.parseSAW base nm compile_b of
    (_,[]) -> do
      let blen :: Int
          blen = fromIntegral (BL.length compile_b)
          primExpr = stringPrimFromBS compile_b
      packExpr <- [| do
           b <- unsafePackAddressLen blen $(return primExpr)
           return $ readModule $(modules) base path (BL.fromChunks [b])
        |]
      return packExpr
    (_,errors) -> fail $ "Failed to parse prelude:\n" ++ show errors

data DecWriterState = DecWriterState { _dwDecs :: [Dec]
                                     }

dwDecs :: Simple Lens DecWriterState [Dec]
dwDecs = lens _dwDecs (\s v -> s { _dwDecs = v })

-- | Monad for defining declarations.
type DecWriter = StateT DecWriterState Q

-- | Run declaration writer returning list of declarations.
runDecWriter :: DecWriter () -> Q [Dec]
runDecWriter m = _dwDecs <$> execStateT m s
  where s = DecWriterState { _dwDecs = [] }

addDecs :: [Dec] -> DecWriter ()
addDecs decs = dwDecs %= (++decs)

-- | Contains a value and an expression that will evaluate to it at runtime.
data DecExp a = DecExp { decExp :: !Exp
                       , decVal :: !a
                       }

-- | Import an existing definition into the writer.
defineImport :: ExpQ -> a -> DecWriter (DecExp a)
defineImport eq m = do
  e <- lift eq
  return DecExp { decExp = e, decVal = m }

defineModuleFromFile :: [DecExp Module] -> String -> FilePath -> DecWriter (DecExp Module)
defineModuleFromFile modules decNameStr path = do
  let nm = takeFileName path
#if MIN_VERSION_template_haskell(2,7,0)
    -- Record path as a dependency on this compilation.
  lift $ qAddDependentFile path
#endif
  -- Get base directory for pretty printing purposes.
  base <- lift $ runIO $ getCurrentDirectory
  -- Load file as lazy bytestring.
  compile_b <- lift $ runIO $ BL.readFile path
  -- Run parser.
  let imports = decVal <$> modules

  m <-
    case Un.parseSAW base nm compile_b of
      (m0,[]) -> do
        case tcModule imports m0 of
          Right r -> return r
          Left e -> fail $ "Module typechecking failed:\n" ++ show (nest 4 e)
      (_,errors) -> fail $ "Module Parsing failed:\n" ++ show errors
  let decName = mkName decNameStr
  let blen :: Int
      blen = fromIntegral (BL.length compile_b)
      primExpr = stringPrimFromBS compile_b
#if MIN_VERSION_template_haskell(2,8,0)
      noinlinePragma = InlineP decName NoInline FunLike AllPhases
#else
      noinlinePragma = InlineP decName (InlineSpec False False Nothing)
#endif
  moduleTp <- lift $ [t| Module |]
  packExpr <- lift $ [| unsafePerformIO $ do
        b <- unsafePackAddressLen blen $(return primExpr)
        return $ readModule $(return (ListE (decExp <$> modules))) base path (BL.fromChunks [b])
      |]
  addDecs [ PragmaD noinlinePragma
          , SigD decName moduleTp
          , FunD decName [ Clause [] (NormalB packExpr) [] ]
          ]
  return $ DecExp { decExp = VarE decName
                  , decVal = m
                  }

-- | Declare a termf definition referring to a constant with the given name
-- in the module.
declareDefTermF :: DecExp Module -> String -> DecWriter ()
declareDefTermF mexp nm = do
  let m = decVal mexp
  let i = mkIdent (moduleName m) nm
  when (isNothing (findDef m i)) $ do
    fail $ "Could not find definition for " ++ show nm ++ " in module."
  let decName = mkName $ nm ++ "TermF"
  decTp  <- lift [t| forall t . TermF t |]
  decExpr <- lift [| FTermF (GlobalDef (parseIdent $(stringE (show i)))) |]
  addDecs [ SigD decName decTp
          , FunD decName [ Clause [] (NormalB decExpr) []]
          ]

-- @sharedFnType n@ returns the type of a function for generating function
-- applications.
sharedFunctionType :: Int -> Q Type
sharedFunctionType 0 =
    [t| SharedContext -> IO Term |]
sharedFunctionType n =
    [t| SharedContext -> IO $(go n) |]
  where go 0 = [t| IO Term |]
        go i = [t| Term -> $(go (i-1)) |]

-- Given a datatype with the type
--   c : T1 -> ... -> TN -> T
-- This hads a declaration of the function.
-- scApply(modulename)(upcase c)
--   :: SharedContext
--   -> IO (Term -> ... -> Term -> IO Term)
declareSharedDataTypeApp :: String
                         -> DataType
                         -> DecWriter ()
declareSharedDataTypeApp nm tdt = do
  let sym = show (dtName tdt)
  let n = length (dtParams tdt) + piArgCount (dtRetType tdt)
  -- Get type of result.
  tp <- lift $ sharedFunctionType n
  -- Get value of result.
  decExpr <- lift $ [| \sc ->
    case findDataType (scModule sc) (parseIdent $(stringE sym)) of
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
  addDecs [ SigD decName tp
          , FunD decName [ Clause [] (NormalB decExpr) [] ]
          ]

-- Given a ctor with the type
--   c : T1 -> ... -> TN -> T
-- This hads a declaration of the function.
-- scApply(modulename)(upcase c)
--   :: SharedContext
--   -> IO (Term -> ... -> Term -> IO Term)
declareSharedCtorApp :: String
                 -> TypedCtor
                 -> DecWriter ()
declareSharedCtorApp nm c = do
  let cName = show (ctorName c)
  let n = piArgCount (ctorType c)
  -- Get type of result.
  tp <- lift $ sharedFunctionType n
  -- Get value of result.
  decExpr <- lift $ [| \sc ->
    case findCtor (scModule sc) (parseIdent $(stringE cName)) of
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
  addDecs [ SigD decName tp
          , FunD decName [ Clause [] (NormalB decExpr) [] ]
          ]

-- Given a ctor with the type
--   c : T1 -> ... -> TN -> T
-- This adds a declaration of the function:
--   scApply(modulename)(upcase c)
--     :: SharedContext
--     -> IO (Term -> ... -> Term -> IO Term)
declareSharedDefApp :: String -> Int -> Def -> DecWriter ()
declareSharedDefApp nm n def = do
  let iName = show (defIdent def)
  -- Get type of result.
  tp <- lift $ sharedFunctionType n

  -- Get value of result.
  decExpr <- lift $ [| \sc -> do
    let m = scModule sc
    let typedDef = parseIdent $(stringE iName)
    when (isNothing (findDef m typedDef)) $
      fail ($(stringE ("Could not find " ++ iName ++ " in ")) ++ show (moduleName m))
    $(case n of
        0 -> [| scGlobalDef sc typedDef |]
        _ -> [| do d <- scGlobalDef sc typedDef
                   return $(do let procStmt :: Exp -> [ExpQ] -> Q [Stmt]
                                   procStmt r [h] = do
                                     return <$> noBindS [|scApply sc $(return r) $(h)|]
                                   procStmt r (h:l) = do
#if MIN_VERSION_template_haskell(2,8,0)
                                     r0 <- newName "r"
#else
                                     -- Introduce extra number to name to work around bug in
                                     -- ghc 7.4.2 (GHC Trac ticket #7092).
                                     r0 <- newName ("r" ++ show (length l))
#endif
                                     stmt <- bindS (varP r0) [|scApply sc $(return r) $(h)|]
                                     (stmt:) <$> procStmt (VarE r0) l
                                   procStmt _ [] = error "Unexpected empty list to procStmt"
                               nms <- replicateM n $ newName "x"
                               de <- [|d|]
                               LamE (VarP <$> nms) . DoE <$> procStmt de (varE <$> nms))|])
   |]
  -- Add declarations for ctor.
  let decName = mkName nm
  addDecs [ SigD decName tp
          , FunD decName [ Clause [] (NormalB decExpr) [] ]
          ]

-- | Declare functions for creating shared terms for module.
declareSharedModuleFns :: String -> Module -> DecWriter ()
declareSharedModuleFns mnm m = do
  forM_ (moduleDataTypes m) $ \dt -> do
    let nm = "sc" ++ mnm ++ "_" ++ identName (dtName dt)
    declareSharedDataTypeApp nm dt
  forM_ (moduleCtors m) $ \c -> do
    let nm = "scApply" ++ mnm ++ "_" ++ identName (ctorName c)
    declareSharedCtorApp nm c
  forM_ (moduleDefs m) $ \d -> do
    let nm = "scApply" ++ mnm ++ "_" ++ identName (defIdent d)
    declareSharedDefApp nm (piArgCount (defType d)) d
