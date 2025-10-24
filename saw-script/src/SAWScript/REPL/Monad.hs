{- |
Module      : SAWScript.REPL.Monad
Description :
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module SAWScript.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPLFresh
  , raise
  , stop
  , exceptionProtect
  , liftTopLevel
  , liftProofScript
  , subshell
  , proof_subshell
  , REPLState(..)

    -- ** Errors
  , REPLException(..)

    -- ** Environment
  , getCryptolExprNames
  , getCryptolTypeNames
  , getPrompt
  , shouldContinue

    -- ** SAWScript stuff
  , getTopLevelRW
  , getProofStateRef
  , getSAWScriptValueNames
  , getSAWScriptTypeNames
  ) where

import Cryptol.Eval (EvalError)
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.Ident (Namespace(..))
import Cryptol.Utils.PP

import Control.Monad (void)
import Control.Monad.Reader (ask)
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..), MonadMask(..), catchJust)
import Control.Monad.State (MonadState(..), StateT(..), get, gets, put)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Data.IORef (IORef, newIORef, readIORef, modifyIORef, writeIORef)
import qualified Data.Set as Set
--import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Typeable (Typeable)
import qualified Control.Exception as X
import System.IO.Error (isUserError, ioeGetErrorString)
import System.Exit (ExitCode)

import qualified SAWSupport.ScopedMap as ScopedMap

import CryptolSAWCore.CryptolEnv

--------------------

import SAWCentral.Options (Options)
import SAWCentral.Proof (ProofState, ProofResult(..), psGoals)
import SAWCentral.TopLevel (TopLevelRO(..), TopLevelRW(..), TopLevel(..), runTopLevel)
import SAWCentral.Value (ProofScript(..), showsProofResult, Environ(..),
                         rwGetCryptolEnv,
                         pushScope, popScope)

import SAWScript.Interpreter (buildTopLevelEnv)
import SAWScript.ValueOps (makeCheckpoint, restoreCheckpoint)


-- REPL Environment ------------------------------------------------------------

-- REPL Environment.
data REPLState = REPLState
  { rContinue   :: IORef Bool
  , rIsBatch    :: Bool
  , rTopLevelRO :: TopLevelRO
  , rTopLevelRW :: IORef TopLevelRW
  , rProofState :: Maybe (IORef ProofState)
  }

-- | Initial, empty environment.
startupState :: Bool -> Options -> IO REPLState
startupState isBatch opts =
  do (ro, rw) <- buildTopLevelEnv opts []
     contRef <- newIORef True
     rwRef <- newIORef rw
     return REPLState
       { rContinue   = contRef
       , rIsBatch    = isBatch
       , rTopLevelRO = ro
       , rTopLevelRW = rwRef
       , rProofState  = Nothing
       }


-- REPL Monad ------------------------------------------------------------------

-- | REPL monad context.
newtype REPL a = REPL { unREPL :: StateT REPLState IO a }
  deriving (Applicative, Functor, Monad, MonadThrow, MonadCatch, MonadMask, MonadFail)

deriving instance MonadState REPLState REPL

-- | Run a REPL action with a fresh environment.
runREPLFresh :: Bool -> Options -> REPL a -> IO a
runREPLFresh isBatch opts m =
  do st <- startupState isBatch opts
     (result, _st') <- runStateT (unREPL m) st
     return result

-- | Run a REPL action on a REPL state.
runREPLOn :: REPL a -> REPLState -> IO a
runREPLOn m st = do
    (result, _st') <- runStateT (unREPL m) st
    return result

subshell :: REPL () -> TopLevel ()
subshell m =
  do pushScope
     ro <- ask
     rw <- get
     rw' <- liftIO $
       do contRef <- newIORef True
          rwRef <- newIORef rw
          let st = REPLState
                     { rContinue = contRef
                     , rIsBatch  = False
                     , rTopLevelRO = ro
                     , rTopLevelRW = rwRef
                     , rProofState  = Nothing
                     }
          runREPLOn m st
          readIORef rwRef
     put rw'
     popScope

proof_subshell :: REPL () -> ProofScript ()
proof_subshell m =
  ProofScript $ ExceptT $ StateT $ \proofSt ->
  do pushScope
     ro <- ask
     rw <- get
     (rw', outProofSt) <- liftIO $
       do contRef <- newIORef True
          rwRef <- newIORef rw
          proofRef <- newIORef proofSt
          let st = REPLState
                     { rContinue = contRef
                     , rIsBatch  = False
                     , rTopLevelRO = ro
                     , rTopLevelRW = rwRef
                     , rProofState  = Just proofRef
                     }
          runREPLOn m st
          (,) <$> readIORef rwRef <*> readIORef proofRef
     put rw'
     popScope
     return (Right (), outProofSt)


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
raise exn = liftIO $ X.throwIO exn

-- | Handle any exception type in 'REPL' actions.
catchEx :: X.Exception e => REPL a -> (e -> REPL a) -> REPL a
catchEx m k = m `catch` k

-- | Handle 'REPLException' exceptions in 'REPL' actions.
catchREPL :: REPL a -> (REPLException -> REPL a) -> REPL a
catchREPL = catchEx

-- | Similar to 'catchREPL' above, but catches generic IO exceptions from 'fail'.
catchFail :: REPL a -> (String -> REPL a) -> REPL a
catchFail m k = catchJust sel m k
  where
    sel :: X.IOException -> Maybe String
    sel e | isUserError e = Just (ioeGetErrorString e)
          | otherwise     = Nothing

-- | Handle any other exception (except that we ignore async exceptions and exitWith)
catchOther :: REPL a -> (X.SomeException -> REPL a) -> REPL a
catchOther m k = catchJust flt m k
 where
  flt e
    | Just (_ :: X.AsyncException) <- X.fromException e = Nothing
    | Just (_ :: ExitCode)       <- X.fromException e = Nothing
    | otherwise = Just e

exceptionProtect :: REPL () -> REPL ()
exceptionProtect cmd =
      do chk <- liftIO . makeCheckpoint =<< getTopLevelRW
         cmd `catchREPL`  (handlerPP chk)
             `catchFail`  (handlerFail chk)
             `catchOther` (handlerPrint chk)

    where
    handlerPP chk re =
      do liftIO (putStrLn "" >> print (pp re))
         void $ liftTopLevel (restoreCheckpoint chk)
         return ()
    handlerPrint chk e =
      do liftIO (putStrLn "" >> putStrLn (X.displayException e))
         void $ liftTopLevel (restoreCheckpoint chk)

    handlerFail chk s =
      do liftIO (putStrLn "" >> putStrLn s)
         void $ liftTopLevel (restoreCheckpoint chk)

liftTopLevel :: TopLevel a -> REPL a
liftTopLevel m =
  do ro  <- getTopLevelRO
     ref <- getTopLevelRWRef
     liftIO $ do
             rw <- readIORef ref
             (a, rw') <- runTopLevel m ro rw
             writeIORef ref rw'
             return a

liftProofScript :: ProofScript a -> IORef ProofState -> REPL a
liftProofScript m ref =
  liftTopLevel $
  do st <- liftIO $ readIORef ref
     (res, st') <- runStateT (runExceptT (unProofScript m)) st
     liftIO $ writeIORef ref st'
     case res of
       Left (stats, cex) ->
         do ppOpts <- rwPPOpts <$> get
            fail (showsProofResult ppOpts (InvalidProof stats cex st') "")
       Right x -> return x

-- Primitives ------------------------------------------------------------------

instance MonadIO REPL where
  liftIO m = REPL (liftIO m)

readRef :: (REPLState -> IORef a) -> REPL a
readRef r = do
    ref <- gets r
    liftIO $ readIORef ref

modifyRef :: (REPLState -> IORef a) -> (a -> a) -> REPL ()
modifyRef r f = do
    ref <- gets r
    liftIO $ modifyIORef ref f

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt =
  do batch <- gets rIsBatch
     if batch then return ""
     else
       getProofStateRef >>= \case
         Nothing -> return "sawscript> "
         Just psr ->
           do ps <- liftIO (readIORef psr)
              return ("proof ("++show (length (psGoals ps))++")> ")

shouldContinue :: REPL Bool
shouldContinue = readRef rContinue

stop :: REPL ()
stop = modifyRef rContinue (const False)

-- | Get visible Cryptol variable names.
getCryptolExprNames :: REPL [String]
getCryptolExprNames =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.namespaceMap NSValue fNames)))

-- | Get visible Cryptol type names.
getCryptolTypeNames :: REPL [String]
getCryptolTypeNames =
  do fNames <- fmap getNamingEnv getCryptolEnv
     return (map (show . pp) (Map.keys (MN.namespaceMap NSType fNames)))

getCryptolEnv :: REPL CryptolEnv
getCryptolEnv = do
    rw <- getTopLevelRW
    return $ rwGetCryptolEnv rw

getTopLevelRO :: REPL TopLevelRO
getTopLevelRO = gets rTopLevelRO

getTopLevelRWRef :: REPL (IORef TopLevelRW)
getTopLevelRWRef = gets rTopLevelRW

getProofStateRef :: REPL (Maybe (IORef ProofState))
getProofStateRef = gets rProofState

getTopLevelRW :: REPL TopLevelRW
getTopLevelRW = readRef rTopLevelRW

-- | Get visible variable names for Haskeline completion.
getSAWScriptValueNames :: REPL [String]
getSAWScriptValueNames = do
  rw <- getTopLevelRW
  let avail = rwPrimsAvail rw
      visible (_, lc, _, _, _) = Set.member lc avail
      Environ valenv _tyenv _cryenv = rwEnviron rw
      rbenv = rwRebindables rw
  let rnames1 = ScopedMap.allKeys $ ScopedMap.filter visible valenv
      rnames2 = Map.keys rbenv
  return (map Text.unpack (rnames1 ++ rnames2))

-- | Get visible type names for Haskeline completion.
getSAWScriptTypeNames :: REPL [String]
getSAWScriptTypeNames = do
  rw <- getTopLevelRW
  let avail = rwPrimsAvail rw
      visible (lc, _) = Set.member lc avail
      Environ _valenv tyenv _cryenv = rwEnviron rw
  let rnames = ScopedMap.allKeys $ ScopedMap.filter visible tyenv
  return (map Text.unpack rnames)
