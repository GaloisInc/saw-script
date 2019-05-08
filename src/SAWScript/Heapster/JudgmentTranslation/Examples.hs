{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.Heapster.JudgmentTranslation.Examples (
  testJudgmentTranslation,
  ) where

import Data.Functor.Const

import Data.Parameterized.Classes
import Data.Parameterized.Context
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.Types
import SAWScript.Heapster.JudgmentTranslation
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.TypeTranslation
import SAWScript.TopLevel
import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Pretty

type ExampleContext = EmptyCtx ::> LLVMPointerType 64

permInLeft :: ValuePerm ExampleContext (LLVMPointerType 64)
permInLeft =
  ValPerm_LLVMPtr knownRepr
  [ (LLVMFieldShapePerm
     (LLVMFieldPerm { llvmFieldOffset    = 0
                    , llvmFieldSplitting = SplExpr_All
                    , llvmFieldPerm      = ValPerm_True
                    }
     )
    )
  ]
  Nothing

permInRight :: ValuePerm ExampleContext (LLVMPointerType 64)
permInRight = ValPerm_Eq (PExpr_LLVMWord knownRepr (PExpr_BV knownRepr [] 0))

permIn :: ValuePerm ExampleContext (LLVMPointerType 64)
permIn = ValPerm_Or permInLeft permInRight

permOutLeft :: ValuePerm ExampleContext (LLVMPointerType 64)
permOutLeft = ValPerm_LLVMPtr knownRepr [] Nothing

permOutRightInsideExists :: ValuePerm (ExampleContext ::> BVType 64) (LLVMPointerType 64)
permOutRightInsideExists = ValPerm_Eq (PExpr_LLVMWord knownRepr (PExpr_Var (nextPermVar (incSize zeroSize))))

permOutRight :: ValuePerm ExampleContext (LLVMPointerType 64)
permOutRight = ValPerm_Exists (BVRepr knownRepr) permOutRightInsideExists

permOut :: ValuePerm ExampleContext (LLVMPointerType 64)
permOut = ValPerm_Or permOutLeft permOutRight

-- | For debugging purposes, a simpler example proving the left side:
-- ValPerm_LLVMPtr shapes Nothing |- ValPerm_LLVMPtr [] Nothing
examplePermElimLeft :: PermElim AnnotIntro ExampleContext
examplePermElimLeft = Elim_Done leftAnnotIntro

  where

    permSetSpecOut :: PermSetSpec EmptyCtx ExampleContext
    permSetSpecOut =
      [ PermSpec zeroSize (PExpr_Var (nextPermVar zeroSize)) permOutLeft
      ]

    -- permInLeft |- permOutLeft
    leftAnnotIntro :: AnnotIntro ExampleContext
    leftAnnotIntro = AnnotIntro
      { introInPerms  = extendPermSet emptyPermSet knownRepr permInLeft
      , introOutPerms = permSetSpecOut
      , introProof    = leftIntro
      }

    -- permInLeft |- permOutLeft
    leftIntro :: PermIntro ExampleContext
    leftIntro =
      -- permInLeft |- permOutLeft
      Intro_LLVMPtr (nextPermVar zeroSize)
      -- permInLeft |- empty
      $ Intro_Done

examplePermElimRight :: PermElim AnnotIntro ExampleContext
examplePermElimRight = Elim_Done rightAnnotIntro

  where

    permSetSpecOut :: PermSetSpec EmptyCtx ExampleContext
    permSetSpecOut =
      [ PermSpec zeroSize (PExpr_Var (nextPermVar zeroSize)) permOutRight
      ]

    -- permInRight |- permOutRight
    rightAnnotIntro :: AnnotIntro ExampleContext
    rightAnnotIntro = AnnotIntro
      { introInPerms  = extendPermSet emptyPermSet knownRepr permInRight
      , introOutPerms = permSetSpecOut
      , introProof    = rightIntro
      }

    -- permInRight |- permOutRight
    rightIntro :: PermIntro ExampleContext
    rightIntro =
      -- permInRight |- permOutRight
      Intro_Exists (BVRepr (knownRepr :: NatRepr 64)) (PExpr_BV knownRepr [] 0) permOutRightInsideExists
      -- permInRight |- ValPerm_Eq (PExpr_LLVMWord knownRepr (PExpr_Var (nextPermVar (incSize zeroSize))))
      $ Intro_Eq (EqProof_Refl (PExpr_LLVMWord (knownRepr :: NatRepr 64) (PExpr_BV knownRepr [] 0)))
      -- permInLeft |- permOut
      $ Intro_Done

examplePermElim :: PermElim AnnotIntro ExampleContext
examplePermElim = Elim_Or (nextPermVar zeroSize) leftBranch rightBranch

  where

    permSetSpecOut :: PermSetSpec EmptyCtx ExampleContext
    permSetSpecOut =
      [ PermSpec zeroSize (PExpr_Var (nextPermVar zeroSize)) permOut
      ]

    -- permInLeft |- permOut
    leftBranch :: PermElim AnnotIntro ExampleContext
    leftBranch = Elim_Done leftAnnotIntro

    -- permInLeft |- permOut
    leftAnnotIntro :: AnnotIntro ExampleContext
    leftAnnotIntro = AnnotIntro
      { introInPerms  = extendPermSet emptyPermSet knownRepr permInLeft
      , introOutPerms = permSetSpecOut
      , introProof    = leftIntro
      }

    -- permInLeft |- permOut
    leftIntro :: PermIntro ExampleContext
    leftIntro =
      -- permInLeft |- permOut
      Intro_OrL permOutRight
      -- permInLeft |- permOutLeft
      $ Intro_LLVMPtr (nextPermVar zeroSize)
      -- permInLeft |- empty
      $ Intro_Done

    -- permInRight |- permOut
    rightBranch :: PermElim AnnotIntro ExampleContext
    rightBranch = Elim_Done rightAnnotIntro

    -- permInRight |- permOut
    rightAnnotIntro :: AnnotIntro ExampleContext
    rightAnnotIntro = AnnotIntro
      { introInPerms  = extendPermSet emptyPermSet knownRepr permInRight
      , introOutPerms = permSetSpecOut
      , introProof    = rightIntro
      }

    -- permInRight |- permOut
    rightIntro :: PermIntro ExampleContext
    rightIntro =
      -- permInRight |- permOut
      Intro_OrR permOutLeft
      -- permInRight |- permOutRight
      $ Intro_Exists (BVRepr (knownRepr :: NatRepr 64)) (PExpr_BV knownRepr [] 0) permOutRightInsideExists
      -- permInRight |- ValPerm_Eq (PExpr_LLVMWord knownRepr (PExpr_Var (nextPermVar (incSize zeroSize))))
      $ Intro_Eq (EqProof_Refl (PExpr_LLVMWord (knownRepr :: NatRepr 64) (PExpr_BV knownRepr [] 0)))
      -- permInRight |- permOut
      $ Intro_Done

emptyInfo :: BlocksInfo EmptyCtx
emptyInfo = BlocksInfo { entryPoints = [] }

llvmPointerType :: OpenTerm
llvmPointerType = typeTranslate'' (LLVMPointerRepr (knownRepr :: NatRepr 64))

permInTypeLeft :: OpenTermCtxt ExampleContext -> OpenTerm
permInTypeLeft typeEnvironment = typeTranslate typeEnvironment permInLeft

permInTypeRight :: OpenTermCtxt ExampleContext -> OpenTerm
permInTypeRight typeEnvironment = typeTranslate typeEnvironment permInRight

permInType :: OpenTermCtxt ExampleContext -> OpenTerm
permInType typeEnvironment = typeTranslate typeEnvironment permIn

permOutTypeLeft :: OpenTermCtxt ExampleContext -> OpenTerm
permOutTypeLeft typeEnvironment = typeTranslate typeEnvironment permOutLeft

permOutTypeRight :: OpenTermCtxt ExampleContext -> OpenTerm
permOutTypeRight typeEnvironment = typeTranslate typeEnvironment permOutRight

permOutType :: OpenTermCtxt ExampleContext -> OpenTerm
permOutType typeEnvironment = typeTranslate typeEnvironment permOut

scaffold ::
  ValuePerm ExampleContext (LLVMPointerType 64) ->
  ValuePerm ExampleContext (LLVMPointerType 64) ->
  PermElim AnnotIntro ExampleContext ->
  OpenTerm
scaffold pIn pOut permElim =
  lambdaOpenTerm "v" (typeTranslate'' (LLVMPointerRepr (knownRepr :: NatRepr 64))) $ \ v ->
  let typeEnvironment :: Assignment (Const OpenTerm) ExampleContext = extend empty (Const v) in
  lambdaOpenTerm "vp" (typeTranslate typeEnvironment permIn) $ \ vp ->
  let jctx = JudgmentContext { typeEnvironment
                             , permissionSet   = extendPermSet emptyPermSet knownRepr pIn
                             , permissionMap   = extend empty (Const vp)
                             , catchHandler    = Nothing
                             }
  in
  judgmentTranslate' emptyInfo jctx (typeTranslate typeEnvironment pOut) permElim

translateExamplePermElimLeft :: OpenTerm
translateExamplePermElimLeft = scaffold permInLeft permOutLeft examplePermElimLeft

translateExamplePermElimRight :: OpenTerm
translateExamplePermElimRight = scaffold permInRight permOutRight examplePermElimRight

translateExamplePermElim :: OpenTerm
translateExamplePermElim = scaffold permIn permOut examplePermElim

testJudgmentTranslation :: TopLevel ()
testJudgmentTranslation = do
  sc <- getSharedContext
  io $ do
    let test term = putStrLn . showTerm =<< completeOpenTerm sc term
    putStrLn "Testing llvmPointerType"
    test llvmPointerType
    putStrLn "Testing permInType"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permInType (extend empty (Const v))
    putStrLn "Testing permOutType"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permOutType (extend empty (Const v))
    putStrLn "Testing permInTypeLeft"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permInTypeLeft (extend empty (Const v))
    putStrLn "Testing permOutTypeLeft"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permOutTypeLeft (extend empty (Const v))
    putStrLn "Testing translating examplePermElimLeft"
    test $ translateExamplePermElimLeft
    putStrLn "Testing permInTypeRight"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permInTypeRight (extend empty (Const v))
    putStrLn "Testing permOutTypeRight"
    test $ lambdaOpenTerm "v" llvmPointerType $ \ v -> permOutTypeRight (extend empty (Const v))
    putStrLn "Testing translating examplePermElimRight"
    test $ translateExamplePermElimRight
    putStrLn "Testing translating examplePermElim"
    test $ translateExamplePermElim

-- EXAMPLE to write:
--
-- (ValPerm_LLVMPtr shapes ... \/ eq(PExpr_LLVMWord zero)) ->
-- (ValPerm_LLVMPtr [] Nothing) \/ (exists (x : ), PExpr_LLVMWord x)
--
-- PermElim AnnotIntro (EmptyCtx ::> LLVMPointerType 64)
