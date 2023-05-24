module Error where

import Data.Text (Text)
import Language.LSP.Types (ErrorCode (InternalError), ResponseError (ResponseError))

internalError :: Text -> ResponseError
internalError s = ResponseError InternalError s Nothing
