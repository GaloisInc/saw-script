module SAWScript.TIMonad where

import Control.Monad
import Control.Monad.Trans
import SAWScript.Utils
import Text.PrettyPrint.HughesPJ

type WarnMsg = (Pos, Doc)
type ErrMsg  = (Pos, Doc, String)

newtype TI m s a = TI { unTI :: s -> m (Either ErrMsg (s, a, [WarnMsg])) }

instance Monad m => Functor (TI m s) where
  fmap f m = TI $ \s -> do ms <- unTI m s
                           case ms of
                             Left err         -> return $ Left err
                             Right (s', a, w) -> return $ Right (s', f a, w)

instance Monad m => Monad (TI m s) where
  return x   = TI (\s -> return (Right (s, x, [])))
  TI c >>= f = TI (\s -> do cs <- c s
                            case cs of
                              Left err -> return (Left err)
                              Right (s', x, w1) -> do cs' <- unTI (f x) s'
                                                      case cs' of
                                                        Right (s'', y, w2) -> return $ Right (s'', y, w1 ++ w2)
                                                        r                  -> return $ r)
  fail s = TI (\_ -> return (Left (PosInternal "type-checker", ftext s, "")))

gets :: Monad m => (s -> a) -> TI m s a
gets f = TI (\s -> return (Right (s, f s, [])))

liftTI :: Monad m => m a -> TI m s a
liftTI m = TI (\s -> m >>= \a -> return $ Right (s, a, []))

typeErrWithR :: Monad m => Pos -> Doc -> String -> TI m s a
typeErrWithR p msg resolution = TI (\_ -> return (Left (p, msg, resolution)))

mismatch :: Monad m => Pos -> String -> Doc -> Doc -> TI m s a
mismatch p w g i = TI (\_ -> return (Left (p, msg, "")))
  where msg =    text ("Type mismatch in " ++ w)
              $$ text "Given   : " <+> g
              $$ text "Inferred: " <+> i

typeErr :: Monad m => Pos -> Doc -> TI m s a
typeErr p msg = TI (\_ -> return (Left (p, msg, "")))

typeWarn :: Monad m => Pos -> Doc -> TI m s ()
typeWarn p msg = TI (\s -> return (Right (s, (), [(p, msg)])))

runTI :: MonadIO m => s -> TI m s a -> m a
runTI s (TI c) = do cs <- c s
                    case cs of
                      Right (_, result, w) -> do mapM_ (liftIO . printWarn) w
                                                 return result
                      Left (p, m, r)       -> throwIOExecException p m r

printWarn :: MonadIO m => WarnMsg -> m ()
printWarn (p, d) = liftIO $ putStrLn $ render $ (text (show p) <> text ":") $$ nest 2 d
