module SAWScript.Exceptions where

failure :: String -> Eval a
failure err = Eval $ \e -> Left err

newtype TypeError = TypeError String