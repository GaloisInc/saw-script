{- |
Module      : SAWScript.REPL.Monad
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}

module SAWScript.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPL
  , io
  , raise
  , stop
  , catch
  , catchFail
  , catchOther
  , subshell
  , Refs(..)

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

    -- ** SAWScript stuff
  , getSharedContext
  , getTopLevelRO
  , getValueEnvironment
  , getEnvironment, modifyEnvironment, putEnvironment
  , getEnvironmentRef
  , getSAWScriptNames
  ) where

import Cryptol.Eval (EvalError, EvalErrorEx(..))
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import Cryptol.ModuleSystem.NamingEnv (NamingEnv)
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.Ident (Namespace(..))
import Cryptol.Utils.PP

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..), pure, (<*>))
#endif
import Control.Monad (unless, ap)
import Control.Monad.Reader (ask)
import Control.Monad.State (put, get)
import Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.Fail as Fail
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable (Typeable)
import System.Console.ANSI (setTitle)
import qualified Control.Exception as X
import System.IO.Error (isUserError, ioeGetErrorString)

import Verifier.SAW.SharedTerm (Term)
import Verifier.SAW.CryptolEnv
import qualified Data.AIG as AIG
import qualified Data.AIG.CompactGraph as AIG

--------------------

import SAWScript.AST (Located(getVal))
import SAWScript.Interpreter (buildTopLevelEnv)
import SAWScript.Options (Options)
import SAWScript.TopLevel (TopLevelRO(..), TopLevelRW(..), TopLevel(..))
import SAWScript.Value (AIGProxy(..), mergeLocalEnv)
import Verifier.SAW (SharedContext)

deriving instance Typeable AIG.Proxy

-- REPL Environment ------------------------------------------------------------

-- REPL Environment.
data Refs = Refs
  { eContinue   :: IORef Bool
  , eIsBatch    :: Bool
  , eTopLevelRO :: TopLevelRO
  , environment :: IORef TopLevelRW
  }

-- | Initial, empty environment.
defaultRefs :: Bool -> Options -> IO Refs
defaultRefs isBatch opts =
  do (_biContext, ro, rw) <- buildTopLevelEnv (AIGProxy AIG.compactProxy) opts
     contRef <- newIORef True
     rwRef <- newIORef rw
     return Refs
       { eContinue   = contRef
       , eIsBatch    = isBatch
       , eTopLevelRO = ro
       , environment = rwRef
       }

-- | Build up the prompt for the REPL.
mkPrompt :: Bool {- ^ is batch -} -> String
mkPrompt batch
  | batch     = ""
  | otherwise = "sawscript> "

mkTitle :: Refs -> String
mkTitle _refs = "sawscript"


-- REPL Monad ------------------------------------------------------------------

-- | REPL_ context with InputT handling.
newtype REPL a = REPL { unREPL :: Refs -> IO a }

-- | Run a REPL action with a fresh environment.
runREPL :: Bool -> Options -> REPL a -> IO a
runREPL isBatch opts m =
  do refs <- defaultRefs isBatch opts
     unREPL m refs

subshell :: REPL () -> TopLevel ()
subshell (REPL m) = TopLevel_ $
  do ro <- ask
     rw <- get
     rw' <- liftIO $
       do contRef <- newIORef True
          rwRef <- newIORef rw
          let refs = Refs
                     { eContinue = contRef
                     , eIsBatch  = False
                     , eTopLevelRO = ro
                     , environment = rwRef
                     }
          m refs
          readIORef rwRef
     put rw'

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

#if !MIN_VERSION_base(4,13,0)
  fail = Fail.fail
#endif

instance Fail.MonadFail REPL where
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

-- | Handle any other exception
catchOther :: REPL a -> (X.SomeException -> REPL a) -> REPL a
catchOther = catchEx

rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalErrorEx -> IO a
  rethrow (EvalErrorEx _ exn) = X.throwIO (EvalError exn)




-- Primitives ------------------------------------------------------------------

io :: IO a -> REPL a
io m = REPL (\ _ -> m)

getRefs :: REPL Refs
getRefs = REPL pure

readRef :: (Refs -> IORef a) -> REPL a
readRef r = REPL (\refs -> readIORef (r refs))

modifyRef :: (Refs -> IORef a) -> (a -> a) -> REPL ()
modifyRef r f = REPL (\refs -> modifyIORef (r refs) f)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt = mkPrompt <$> (REPL (return . eIsBatch))

shouldContinue :: REPL Bool
shouldContinue = readRef eContinue

stop :: REPL ()
stop = modifyRef eContinue (const False)

unlessBatch :: REPL () -> REPL ()
unlessBatch body =
  do batch <- REPL (return . eIsBatch)
     unless batch body

setREPLTitle :: REPL ()
setREPLTitle =
  unlessBatch $
  do refs <- getRefs
     io (setTitle (mkTitle refs))

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
     return (map (show . pp) (Map.keys (MN.namespaceMap NSValue fNames)))

-- | Get visible type signature names.
getTypeNames :: REPL [String]
getTypeNames  =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.namespaceMap NSType fNames)))

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
getTopLevelRO = REPL (return . eTopLevelRO)

getEnvironmentRef :: REPL (IORef TopLevelRW)
getEnvironmentRef = environment <$> getRefs

getEnvironment :: REPL TopLevelRW
getEnvironment = readRef environment

getValueEnvironment :: REPL TopLevelRW
getValueEnvironment =
  do ro <- getTopLevelRO
     rw <- getEnvironment
     io (mergeLocalEnv (roSharedContext ro) (roLocalEnv ro) rw)

putEnvironment :: TopLevelRW -> REPL ()
putEnvironment = modifyEnvironment . const

modifyEnvironment :: (TopLevelRW -> TopLevelRW) -> REPL ()
modifyEnvironment = modifyRef environment

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

