{-# Language ScopedTypeVariables #-}
{-# Language GADTs #-}
module Heapster.NamePropagation where

import Data.Functor.Constant
import Data.Parameterized.TraversableFC ( FoldableFC(toListFC), FunctorFC(fmapFC) )
import Lang.Crucible.Analysis.Fixpoint
import Lang.Crucible.CFG.Core ( Some(Some), CFG(cfgHandle) )
import Lang.Crucible.FunctionHandle ( FnHandle(handleArgTypes) )
import Lang.Crucible.LLVM.Extension ( LLVM, LLVMStmt(..), LLVM_Dbg(..) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as PM
import qualified Text.LLVM.AST as L

type NameDom = Pointed (Constant String)

nameJoin :: Constant String a -> Constant String a -> NameDom a
nameJoin (Constant x) (Constant y) | x == y = Pointed (Constant x)
nameJoin _ _ = Top

nameDomain :: Domain (Pointed (Constant String))
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
                modifyAbstractRegValue names ptr (\_ -> Pointed (Constant ("&" ++ n)))
              LLVM_Debug (LLVM_Dbg_Addr ptr di _) | Just n <- L.dilvName di ->
                modifyAbstractRegValue names ptr (\_ -> Pointed (Constant ("&" ++ n)))
              LLVM_Debug (LLVM_Dbg_Value _ val di _) | Just n <- L.dilvName di ->
                modifyAbstractRegValue names val (\_ -> Pointed (Constant n))
              _ -> names
      in (Just names', Bottom)             
  }

computeNames ::
  forall blocks init ret.
  CFG LLVM blocks init ret ->
  Ctx.Assignment (Constant [Maybe String]) blocks
computeNames cfg =
  case alg of
    (_, end, _) -> fmapFC (\(Ignore (Some p)) -> Constant (toListFC flatten (_paRegisters p))) end
  where
  flatten :: NameDom a -> Maybe String
  flatten Top = Nothing
  flatten Bottom = Nothing
  flatten (Pointed (Constant x)) = Just x

  sz = Ctx.size (handleArgTypes (cfgHandle cfg))
  alg =
      forwardFixpoint'
      nameDomain
      nameInterpretation
      cfg
      PM.empty
      (Ctx.replicate sz Bottom)
