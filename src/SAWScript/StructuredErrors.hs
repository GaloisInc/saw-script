{-# language ConstraintKinds, MultiParamTypeClasses, RankNTypes, TypeFamilies,
  DataKinds, NamedFieldPuns, FlexibleInstances, FlexibleContexts,
  ScopedTypeVariables, TypeApplications, UndecidableInstances, TypeOperators #-}
{-# options_ghc -Wno-unticked-promoted-constructors #-}

module SAWScript.StructuredErrors
  ( Throws
  , throwChecked
  , catchChecked
  , formatCallStack

  , Unimplemented
  , Unfinished
  , unimplemented
  , unimplementedMessage

  , Impossible
  , AssertsInvariants
  , impossible
  , impossibleMessage
  ) where

import Control.Monad.Catch
import GHC.Stack
import GHC.Exts (IsList(..))
import GHC.TypeLits
import Unsafe.Coerce
import Data.Constraint
import Data.List

-- TODO: Toggle this on and off with a CPP flag
type Use_GHC_Stack_Traces = HasCallStack


-- * Checked exceptions that must be caught once thrown, and carry their stack
-- * traces with them if this feature is enabled.

-- NOTE: Not exported, so nobody can mention Throws_ This means that if anyone
-- wants to defer catching to an outer function, they have to put Throws in
-- their context, which carries with it Use_GHC_Stack_Traces, forcing the call
-- stack tracking to propagate along with the must-be-caught constraint.
class Throws_ e
instance TypeError
  ( Text "Checked exception of type ‘" :<>:
    ShowType e :<>:
    Text "’ may not have been caught." :$$:
    Text "Either catch it using ‘catchChecked’ " :<>:
    Text "or defer handling it by adding the constraint ‘Throws " :<>:
    ShowType e :<>:
    Text "’ to the context."
  ) => Throws_ e

type Throws e
  = ( Use_GHC_Stack_Traces
    , Throws_ e
    )

data TracedException e
  = TracedException { exception :: e, trace :: CallStack }

instance Show e => Show (TracedException e) where
  show TracedException{exception, trace} =
    "Uncaught checked exception!\n" ++
    show exception ++
    "\n\nNOTE: If you are seeing this message, it means this exception slipped " ++
    "through a static exception check and was not caught. The only way " ++
    "for this to happen is for ‘catchChecked’ to be called on a nested " ++
    "monadic action like ‘IO (IO a)’ where the inner action throws the " ++
    "exception in question. Please report this as a bug. Thank you!\n" ++
    "\nThis call stack may be useful:\n" ++
    unlines (map ("   " ++) (lines (formatCallStack trace)))

instance Exception e => Exception (TracedException e)

throwChecked
  :: (MonadThrow m, Exception e, Throws e)
  => e -> m a
throwChecked e =
  throwM $
    TracedException {
      exception = e,
      trace = fromList (drop 1 (toList callStack))
    }

catchChecked
  :: forall e m a. (MonadCatch m, Exception e, Use_GHC_Stack_Traces)
  => (Throws_ e => m a)
  -> (e -> Maybe CallStack -> m a)
  -> m a
catchChecked action handler =
  case unsafeCoerce (Dict :: Dict ()) :: Dict (Throws_ e) of
    Dict ->
      catch (catch action (\e -> handler e Nothing)) $
          \TracedException{exception, trace} -> handler exception (Just trace)


-- * Formatting call stack traces nicely

formatCallStack :: CallStack -> String
formatCallStack =
  intercalate "\n" . map perLine . toList
  where
    perLine :: (String, SrcLoc) -> String
    perLine (function, SrcLoc{srcLocFile, srcLocStartLine, srcLocStartCol}) =
      concat
        [ function
        , ", called at "
        , srcLocFile
        , ":"
        , show srcLocStartLine
        , ":"
        , show srcLocStartCol
        ]


-- * Internal exceptions

-- "Impossible" cases that might not be entirely impossible...

newtype Impossible
  = Impossible String

impossibleMessage :: Impossible -> String
impossibleMessage (Impossible text) = text

instance Show Impossible where
  show (Impossible text) =
    concat [ "Internal invariant violation: "
           , text
           ]

instance Exception Impossible

type AssertsInvariants
  = Throws Impossible

impossible :: (AssertsInvariants, MonadThrow m) => String -> m a
impossible text = throwChecked (Impossible text)

-- Unimplemented features...

newtype Unimplemented
  = Unimplemented String

unimplementedMessage :: Unimplemented -> String
unimplementedMessage (Unimplemented text) = text

instance Show Unimplemented where
  show (Unimplemented text) =
    concat [ "Unimplemented feature: "
           , text
           ]

instance Exception Unimplemented

type Unfinished =
  Throws Unimplemented

unimplemented :: (Unfinished, MonadThrow m) => String -> m a
unimplemented text = throwChecked (Unimplemented text)
