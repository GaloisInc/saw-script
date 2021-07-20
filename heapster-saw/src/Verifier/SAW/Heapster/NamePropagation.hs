{-# Language ScopedTypeVariables #-}
{-# Language GADTs #-}
module Verifier.SAW.Heapster.NamePropagation where

import Data.Parameterized.TraversableFC ( FoldableFC(toListFC), FunctorFC(fmapFC) )
import Lang.Crucible.Analysis.Fixpoint
import Lang.Crucible.CFG.Core ( Some(Some), CFG(cfgHandle) )
import Lang.Crucible.FunctionHandle ( FnHandle(handleArgTypes) )
import Lang.Crucible.LLVM.Extension ( LLVM, LLVMStmt(..), LLVM_Dbg(..) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as PM
import qualified Text.LLVM.AST as L

type NameDom = Pointed (Ignore String)

nameJoin :: Ignore String a -> Ignore String a -> NameDom a
nameJoin (Ignore x) (Ignore y) | x == y = Pointed (Ignore x)
nameJoin _ _ = Top

nameDomain :: Domain (Pointed (Ignore String))
nameDomain = pointed nameJoin (==) WTO

nameInterpretation :: Interpretation LLVM NameDom
nameInterpretation =  Interpretation
  { interpExpr        = \_ _ _     names -> (Just names, Bottom)
  , interpCall        = \_ _ _ _ _ names -> (Just names, Bottom)
  , interpReadGlobal  = \_         names -> (Just names, Bottom)
  , interpWriteGlobal = \_ _       names -> Just names
  , interpBr          = \_ _ _ _   names -> (Just names, Just names)
  , interpMaybe       = \_ _ _     names -> (Just names, Bottom, Just names)
  , interpExt         = \_ stmt    names ->
      let names' =
            case stmt of
              LLVM_Debug (LLVM_Dbg_Declare ptr di _) | Just n <- L.dilvName di ->
                modifyAbstractRegValue names ptr (\_ -> Pointed (Ignore ("&" ++ n)))
              LLVM_Debug (LLVM_Dbg_Addr ptr di _) | Just n <- L.dilvName di ->
                modifyAbstractRegValue names ptr (\_ -> Pointed (Ignore ("&" ++ n)))
              LLVM_Debug (LLVM_Dbg_Value _ val di _) | Just n <- L.dilvName di ->
                modifyAbstractRegValue names val (\_ -> Pointed (Ignore n))
              _ -> names
      in (Just names', Bottom)             
  }

computeNames ::
  forall blocks init ret.
  CFG LLVM blocks init ret ->
  Ctx.Assignment (Ignore [Maybe String]) blocks
computeNames cfg =
  case alg of
    (_, end, _) -> fmapFC (\(Ignore (Some p)) -> Ignore (toListFC flatten (_paRegisters p))) end
  where
  flatten :: NameDom a -> Maybe String
  flatten Top = Nothing
  flatten Bottom = Nothing
  flatten (Pointed (Ignore x)) = Just x

  sz = Ctx.size (handleArgTypes (cfgHandle cfg))
  alg =
      forwardFixpoint'
      nameDomain
      nameInterpretation
      cfg
      PM.empty
      (Ctx.replicate sz Bottom)
