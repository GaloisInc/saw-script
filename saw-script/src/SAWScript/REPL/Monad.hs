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
{-# LANGUAGE OverloadedStrings #-}
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
  , getProofState
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
import Control.Monad.State (MonadState(..), StateT(..), get, gets, put, modify)
import Control.Monad.Except (ExceptT(..), runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
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

import SAWScript.Panic (panic)
import SAWScript.Interpreter (buildTopLevelEnv)
import SAWScript.ValueOps (makeCheckpoint, restoreCheckpoint)


-- REPL Environment ------------------------------------------------------------

-- REPL Environment.
data REPLState = REPLState
  { rContinue   :: Bool
  , rIsBatch    :: Bool
  , rTopLevelRO :: TopLevelRO
  , rTopLevelRW :: TopLevelRW
  , rProofState :: Maybe ProofState
  }

-- | Initial, empty environment.
startupState :: Bool -> Options -> IO REPLState
startupState isBatch opts =
  do (ro, rw) <- buildTopLevelEnv opts []
     return REPLState
       { rContinue   = True
       , rIsBatch    = isBatch
       , rTopLevelRO = ro
       , rTopLevelRW = rw
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
runREPLOn :: REPL a -> REPLState -> IO (a, REPLState)
runREPLOn m st = do
    runStateT (unREPL m) st

subshell :: REPL () -> TopLevel ()
subshell m =
  do pushScope
     ro <- ask
     rw <- get
     rw' <- liftIO $
       do let st = REPLState
                     { rContinue = True
                     , rIsBatch  = False
                     , rTopLevelRO = ro
                     , rTopLevelRW = rw
                     , rProofState  = Nothing
                     }
          (_result, st') <- runREPLOn m st
          return $ rTopLevelRW st'
     put rw'
     popScope

proof_subshell :: REPL () -> ProofScript ()
proof_subshell m =
  ProofScript $ ExceptT $ StateT $ \proofSt ->
  do pushScope
     ro <- ask
     rw <- get
     (rw', outProofSt) <- liftIO $
       do let st = REPLState
                     { rContinue = True
                     , rIsBatch  = False
                     , rTopLevelRO = ro
                     , rTopLevelRW = rw
                     , rProofState  = Just proofSt
                     }
          (_result, st') <- runREPLOn m st
          let proofSt' = case rProofState st' of
                Nothing -> panic "proof_subshell" ["Proof state disappeared!"]
                Just ps -> ps
          return (rTopLevelRW st', proofSt')
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
liftTopLevel m = do
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    (result, rw') <- liftIO $ runTopLevel m ro rw
    modify (\st -> st { rTopLevelRW = rw' })
    return result

liftProofScript :: ProofScript a -> REPL a
liftProofScript m = do
    mpst <- gets rProofState
    let pst = case mpst of
          Nothing -> panic "liftProofScript" ["Not in ProofScript mode"]
          Just ps -> ps
    (result, pst') <- liftTopLevel $ runStateT (runExceptT (unProofScript m)) pst
    modify (\st -> st { rProofState = Just pst' })
    liftTopLevel $ case result of
       Left (stats, cex) ->
         do ppOpts <- rwPPOpts <$> get
            fail (showsProofResult ppOpts (InvalidProof stats cex pst') "")
       Right x -> return x

-- Primitives ------------------------------------------------------------------

instance MonadIO REPL where
  liftIO m = REPL (liftIO m)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt =
  do batch <- gets rIsBatch
     if batch then return ""
     else do
       mpst <- gets rProofState
       case mpst of
         Nothing ->
             return "sawscript> "
         Just pst ->
             return ("proof ("++show (length (psGoals pst))++")> ")

shouldContinue :: REPL Bool
shouldContinue =
    gets rContinue

stop :: REPL ()
stop =
    modify (\st -> st { rContinue = False })

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

getTopLevelRW :: REPL TopLevelRW
getTopLevelRW = gets rTopLevelRW

getProofState :: REPL (Maybe ProofState)
getProofState = gets rProofState

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
