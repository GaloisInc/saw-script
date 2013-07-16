module SAWScript.FileQuote where

import Language.Haskell.TH
import Language.Haskell.TH.Quote

litFile :: QuasiQuoter
litFile = quoteFile $ QuasiQuoter { quoteExp = return . LitE . StringL }
