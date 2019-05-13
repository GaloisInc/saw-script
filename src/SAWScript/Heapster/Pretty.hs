{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Heapster.Pretty where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PPL ((<$>))
import Data.Proxy
import Data.Parameterized.Context
import Data.Parameterized.Ctx
import Data.Parameterized.TraversableFC
import Control.Monad.Reader
import Verifier.SAW.Term.Pretty

import SAWScript.Heapster.Permissions


-- | Typed string
newtype StringF a = StringF { unStringF :: String }

-- | Try to make a string unique by adding a prime to the end
primeStringF :: StringF a -> StringF a
primeStringF (StringF x) = StringF (x ++ "'")

-- | Environment for pretty-printing
data PrettyEnv ctx =
  PrettyEnv { envPPOpts :: PPOpts,
              envCtx :: Assignment StringF ctx }

extendEnv :: StringF tp -> PrettyEnv ctx -> PrettyEnv (ctx ::> tp)
extendEnv x (PrettyEnv {..}) =
  PrettyEnv { envCtx = extend envCtx x, .. }

-- | Monad for pretty-printing
type PrettyM ctx = Reader (PrettyEnv ctx)

-- | Pretty-print inside a bigger context
withVarM :: StringF tp -> PrettyM (ctx ::> tp) a -> PrettyM ctx a
withVarM x m =
  do names <- toListFC unStringF <$> envCtx <$> ask
     if elem (unStringF x) names then withVarM (primeStringF x) m else
       ReaderT $ \env ->
       runReaderT m (extendEnv x env)

parensIf :: Bool -> PrettyM ctx Doc -> PrettyM ctx Doc
parensIf True m = parens <$> align <$> m
parensIf False m = m

-- | Typeclass for pretty-printing objects relative to a context
class CtxPretty (f :: Ctx k -> *) where
  cpretty :: f ctx -> PrettyM ctx Doc

-- | Typeclass for pretty-printing objects relative to a context
class CtxPretty' (f :: Ctx k1 -> k2 -> *) where
  cpretty' :: f ctx a -> PrettyM ctx Doc

instance CtxPretty' Index where
  cpretty' ix =
    string <$> unStringF <$> (! ix) <$> envCtx <$> ask

instance CtxPretty' PermVar where
  cpretty' (PermVar _ ix) = cpretty' ix

splittingIsStar :: SplittingExpr ctx -> Bool
splittingIsStar (SplExpr_Star _ _) = True
splittingIsStar _ = False

binaryOpM :: String -> PrettyM ctx Doc -> PrettyM ctx Doc -> PrettyM ctx Doc
binaryOpM op m1 m2 =
  do pp1 <- m1
     pp2 <- m2
     return $ hang 2 $ group (pp1 PPL.<$> text "*" <+> pp2)

instance CtxPretty SplittingExpr where
  cpretty SplExpr_All = return $ string "W"
  cpretty (SplExpr_L spl) =
    (<>) <$> parensIf (splittingIsStar spl) (cpretty spl) <*>
    return (string "L")
  cpretty (SplExpr_R spl) =
    (<>) <$> parensIf (splittingIsStar spl) (cpretty spl) <*>
    return (string "R")
  cpretty (SplExpr_Star spl1 spl2) =
    binaryOpM "*" (parensIf (splittingIsStar spl1) (cpretty spl1))
    (cpretty spl2)
  cpretty (SplExpr_Var x) = cpretty' x

instance CtxPretty' PermExpr where
  cpretty' (PExpr_Var x) = cpretty' x
  cpretty' (PExpr_BV _w factors i) =
    foldM (\pp factor -> binaryOpM "+" (cpretty' factor) (return pp))
    (text $ show i)
    factors
  cpretty' (PExpr_Struct _ args) =
    do pps <- mapM id $ toListFC cpretty' args
       return (text "struct" <+> parens (align $ helper pps))
         where
           helper [] = text ""
           helper [p] = p
           helper (p:ps) = p <> text "," PPL.<$> helper ps
  cpretty' (PExpr_LLVMWord _w bv_expr) =
    do pp <- cpretty' bv_expr
       return $ hang 2 (text "llvmWord" <+> parens pp)
  cpretty' (PExpr_LLVMOffset _w x off_expr) =
    binaryOpM "+" (cpretty' x) (cpretty' off_expr)
  cpretty' (PExpr_Spl spl) = cpretty spl

instance CtxPretty' BVFactor where
  cpretty' (BVFactor _ i x) =
    binaryOpM "*" (return $ text $ show i) (cpretty' x)
