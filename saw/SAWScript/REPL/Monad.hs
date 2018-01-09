{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveDataTypeable #-}

{- |
Module      : $Header$
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
module SAWScript.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPL
  , io
  , raise
  , stop
  , catch
  , catchIO
  , catchFail
  , catchTypeErrors

    -- ** Errors
  , REPLException(..)
  , rethrowEvalError

    -- ** Environment
  , getCryptolEnv, modifyCryptolEnv, setCryptolEnv
  , getModuleEnv, setModuleEnv
  , getTSyns, getNewtypes, getVars
  , getExprNames
  , getTypeNames
  , getPropertyNames
  , getPrompt
  , shouldContinue
  , unlessBatch
  , setREPLTitle
  , getTermEnv, modifyTermEnv, setTermEnv
  , getExtraTypes, modifyExtraTypes, setExtraTypes
  , getExtraNames, modifyExtraNames, setExtraNames
  , getRW

    -- ** SAWScript stuff
  , getSharedContext
  , getTopLevelRO
  , getEnvironment, modifyEnvironment, putEnvironment
  , getSAWScriptNames
  ) where

import Cryptol.Eval (EvalError)
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import Cryptol.ModuleSystem.NamingEnv (NamingEnv)
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..), pure, (<*>))
#endif
import Control.Monad (unless, ap)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable (Typeable)
import System.Console.ANSI (setTitle)
import qualified Control.Exception as X
import System.IO.Error (isUserError, ioeGetErrorString)

import Verifier.SAW.SharedTerm (Term)

--------------------

import SAWScript.AST (Located(getVal))
import SAWScript.CryptolEnv
import SAWScript.Exceptions
import SAWScript.Interpreter (buildTopLevelEnv)
import SAWScript.Options (Options)
import SAWScript.TopLevel (TopLevelRO(..), TopLevelRW(..))
import Verifier.SAW (SharedContext)


-- REPL Environment ------------------------------------------------------------

-- REPL RW Environment.
data RW = RW
  { eContinue   :: Bool
  , eIsBatch    :: Bool
  , eTopLevelRO :: TopLevelRO
  , environment :: TopLevelRW
  }

-- | Initial, empty environment.
defaultRW :: Bool -> Options -> IO RW
defaultRW isBatch opts = do
  (_biContext, ro, rw) <- buildTopLevelEnv opts

  return RW
    { eContinue   = True
    , eIsBatch    = isBatch
    , eTopLevelRO = ro
    , environment = rw
    }

-- | Build up the prompt for the REPL.
mkPrompt :: RW -> String
mkPrompt rw
  | eIsBatch rw = ""
  | otherwise   = "sawscript> "

mkTitle :: RW -> String
mkTitle _rw = "sawscript"


-- REPL Monad ------------------------------------------------------------------

-- | REPL_ context with InputT handling.
newtype REPL a = REPL { unREPL :: IORef RW -> IO a }

-- | Run a REPL action with a fresh environment.
runREPL :: Bool -> Options -> REPL a -> IO a
runREPL isBatch opts m = do
  ref <- newIORef =<< defaultRW isBatch opts
  unREPL m ref

instance Functor REPL where
  {-# INLINE fmap #-}
  fmap f m = REPL (\ ref -> fmap f (unREPL m ref))

instance Monad REPL where
  {-# INLINE return #-}
  return x = REPL (\_ -> return x)

  {-# INLINE (>>=) #-}
  m >>= f = REPL $ \ref -> do
    x <- unREPL m ref
    unREPL (f x) ref

  {-# INLINE fail #-}
  fail msg = REPL (\_ -> fail msg)

instance Applicative REPL where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = ap

-- Exceptions ------------------------------------------------------------------

-- | REPL exceptions.
data REPLException
  = ParseError ParseError
  | FileNotFound FilePath
  | DirectoryNotFound FilePath
  | NoPatError [Error]
  | NoIncludeError [IncludeError]
  | EvalError EvalError
  | ModuleSystemError M.ModuleError
  | EvalPolyError T.Schema
  | TypeNotTestable T.Type
    deriving (Show,Typeable)

instance X.Exception REPLException

instance PP REPLException where
  ppPrec _ re = case re of
    ParseError e         -> ppError e
    FileNotFound path    -> sep [ text "File"
                                , text ("`" ++ path ++ "'")
                                , text"not found"
                                ]
    DirectoryNotFound path -> sep [ text "Directory"
                                  , text ("`" ++ path ++ "'")
                                  , text"not found or not a directory"
                                  ]
    NoPatError es        -> vcat (map pp es)
    NoIncludeError es    -> vcat (map ppIncludeError es)
    ModuleSystemError me -> pp me
    EvalError e          -> pp e
    EvalPolyError s      -> text "Cannot evaluate polymorphic value."
                         $$ text "Type:" <+> pp s
    TypeNotTestable t    -> text "The expression is not of a testable type."
                         $$ text "Type:" <+> pp t

-- | Raise an exception.
raise :: REPLException -> REPL a
raise exn = io (X.throwIO exn)

-- | Handle any exception type in 'REPL' actions.
catchEx :: X.Exception e => REPL a -> (e -> REPL a) -> REPL a
catchEx m k = REPL (\ ref -> unREPL m ref `X.catch` \ e -> unREPL (k e) ref)

-- | Handle 'IOError' exceptions in 'REPL' actions.
catchIO :: REPL a -> (IOError -> REPL a) -> REPL a
catchIO = catchEx

-- | Handle SAWScript type error exceptions in 'REPL' actions.
catchTypeErrors :: REPL a -> (TypeErrors -> REPL a) -> REPL a
catchTypeErrors = catchEx

-- | Handle 'REPLException' exceptions in 'REPL' actions.
catch :: REPL a -> (REPLException -> REPL a) -> REPL a
catch = catchEx

-- | Similar to 'catch' above, but catches generic IO exceptions from 'fail'.
catchFail :: REPL a -> (String -> REPL a) -> REPL a
catchFail m k = REPL (\ ref -> X.catchJust sel (unREPL m ref) (\s -> unREPL (k s) ref))
  where
    sel :: X.IOException -> Maybe String
    sel e | isUserError e = Just (ioeGetErrorString e)
          | otherwise     = Nothing

rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalError -> IO a
  rethrow exn = X.throwIO (EvalError exn)




-- Primitives ------------------------------------------------------------------

io :: IO a -> REPL a
io m = REPL (\ _ -> m)

getRW :: REPL RW
getRW  = REPL readIORef

modifyRW_ :: (RW -> RW) -> REPL ()
modifyRW_ f = REPL (\ ref -> modifyIORef ref f)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt  = mkPrompt `fmap` getRW

shouldContinue :: REPL Bool
shouldContinue  = eContinue `fmap` getRW

stop :: REPL ()
stop  = modifyRW_ (\ rw -> rw { eContinue = False })

unlessBatch :: REPL () -> REPL ()
unlessBatch body = do
  rw <- getRW
  unless (eIsBatch rw) body

setREPLTitle :: REPL ()
setREPLTitle  = unlessBatch $ do
  rw <- getRW
  io (setTitle (mkTitle rw))

getVars :: REPL (Map.Map T.Name M.IfaceDecl)
getVars  = do
  me <- getModuleEnv
  let decls = getAllIfaceDecls me
  let vars1 = M.ifDecls decls
  extras <- getExtraTypes
  let vars2 = Map.mapWithKey (\q s -> M.IfaceDecl q s [] False Nothing Nothing) extras
  return (Map.union vars1 vars2)

getTSyns :: REPL (Map.Map T.Name T.TySyn)
getTSyns  = do
  me <- getModuleEnv
  let decls = getAllIfaceDecls me
  return (M.ifTySyns decls)

getNewtypes :: REPL (Map.Map T.Name T.Newtype)
getNewtypes = do
  me <- getModuleEnv
  let decls = getAllIfaceDecls me
  return (M.ifNewtypes decls)

-- | Get visible variable names.
getExprNames :: REPL [String]
getExprNames =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.neExprs fNames)))

-- | Get visible type signature names.
getTypeNames :: REPL [String]
getTypeNames  =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.neTypes fNames)))

getPropertyNames :: REPL [String]
getPropertyNames =
  do xs <- getVars
     return [ getName x | (x,d) <- Map.toList xs,
                T.PragmaProperty `elem` M.ifDeclPragmas d ]

getName :: T.Name -> String
getName  = show . pp

getTermEnv :: REPL (Map T.Name Term)
getTermEnv = fmap eTermEnv getCryptolEnv

modifyTermEnv :: (Map T.Name Term -> Map T.Name Term) -> REPL ()
modifyTermEnv f = modifyCryptolEnv $ \ce -> ce { eTermEnv = f (eTermEnv ce) }

setTermEnv :: Map T.Name Term -> REPL ()
setTermEnv x = modifyTermEnv (const x)

getExtraTypes :: REPL (Map T.Name T.Schema)
getExtraTypes = fmap eExtraTypes getCryptolEnv

modifyExtraTypes :: (Map T.Name T.Schema -> Map T.Name T.Schema) -> REPL ()
modifyExtraTypes f = modifyCryptolEnv $ \ce -> ce { eExtraTypes = f (eExtraTypes ce) }

setExtraTypes :: Map T.Name T.Schema -> REPL ()
setExtraTypes x = modifyExtraTypes (const x)

getExtraNames :: REPL NamingEnv
getExtraNames = fmap eExtraNames getCryptolEnv

modifyExtraNames :: (NamingEnv -> NamingEnv) -> REPL ()
modifyExtraNames f = modifyCryptolEnv $ \ce -> ce { eExtraNames = f (eExtraNames ce) }

setExtraNames :: NamingEnv -> REPL ()
setExtraNames x = modifyExtraNames (const x)

getModuleEnv :: REPL M.ModuleEnv
getModuleEnv  = eModuleEnv `fmap` getCryptolEnv

setModuleEnv :: M.ModuleEnv -> REPL ()
setModuleEnv me = modifyCryptolEnv (\ce -> ce { eModuleEnv = me })

getCryptolEnv :: REPL CryptolEnv
getCryptolEnv = rwCryptol `fmap` getEnvironment

modifyCryptolEnv :: (CryptolEnv -> CryptolEnv) -> REPL ()
modifyCryptolEnv f = modifyEnvironment (\rw -> rw { rwCryptol = f (rwCryptol rw) })

setCryptolEnv :: CryptolEnv -> REPL ()
setCryptolEnv x = modifyCryptolEnv (const x)

getSharedContext :: REPL SharedContext
getSharedContext = fmap roSharedContext getTopLevelRO

getTopLevelRO :: REPL TopLevelRO
getTopLevelRO = fmap eTopLevelRO getRW

getEnvironment :: REPL TopLevelRW
getEnvironment = fmap environment getRW

putEnvironment :: TopLevelRW -> REPL ()
putEnvironment = modifyEnvironment . const

modifyEnvironment :: (TopLevelRW -> TopLevelRW) -> REPL ()
modifyEnvironment f = modifyRW_ $ \current ->
  current { environment = f (environment current) }

-- | Get visible variable names for Haskeline completion.
getSAWScriptNames :: REPL [String]
getSAWScriptNames = do
  env <- getEnvironment
  let rnames = Map.keys (rwValues env)
  return (map getVal rnames)

-- User Environment Interaction ------------------------------------------------

data EnvVal
  = EnvString String
  | EnvNum    !Int
  | EnvBool   Bool
    deriving (Show)

