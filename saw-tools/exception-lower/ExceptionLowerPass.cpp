#include "ExceptionLowerPass.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <vector>

using namespace llvm;

namespace exclow {

/// Thread-local globals for the error state.
struct ErrorState {
  GlobalVariable *Flag;     // i1  — true when an exception is in flight
  GlobalVariable *TypeInfo; // i8* — pointer to std::type_info of thrown type
  GlobalVariable *Value;    // i8* — pointer to exception object
};

/// Create the thread-local error-state globals if they don't already exist.
static ErrorState getOrCreateErrorState(Module &M) {
  auto &Ctx = M.getContext();
  auto *I1Ty = Type::getInt1Ty(Ctx);
  auto *PtrTy = PointerType::getUnqual(Ctx);

  auto getOrInsert = [&](StringRef Name, Type *Ty) -> GlobalVariable * {
    if (auto *GV = M.getGlobalVariable(Name))
      return GV;
    auto *GV = new GlobalVariable(M, Ty, /*isConstant=*/false,
                                  GlobalValue::InternalLinkage,
                                  Constant::getNullValue(Ty), Name);
    GV->setThreadLocal(true);
    return GV;
  };

  return {getOrInsert("__exclow_error_flag", I1Ty),
          getOrInsert("__exclow_error_typeinfo", PtrTy),
          getOrInsert("__exclow_error_value", PtrTy)};
}

/// Get or declare a sentinel return value for a function type.
/// For pointer returns: null.  For integer returns: -1.  For void: nothing.
static Value *getSentinelReturn(IRBuilder<> &B, Function &F) {
  Type *RetTy = F.getReturnType();
  if (RetTy->isVoidTy())
    return nullptr;
  if (RetTy->isPointerTy())
    return ConstantPointerNull::get(cast<PointerType>(RetTy));
  if (RetTy->isIntegerTy())
    return ConstantInt::get(RetTy, -1);
  if (RetTy->isFloatingPointTy())
    return ConstantFP::getNaN(RetTy);
  // Struct/array: return zeroinitializer
  return Constant::getNullValue(RetTy);
}

PreservedAnalyses ExceptionLowerPass::run(Module &M,
                                          ModuleAnalysisManager &MAM) {
  bool Changed = false;
  auto &Ctx = M.getContext();
  ErrorState ES = getOrCreateErrorState(M);

  // Collect all functions to process (avoid iterator invalidation).
  std::vector<Function *> Functions;
  for (auto &F : M)
    Functions.push_back(&F);

  for (auto *F : Functions) {
    if (F->isDeclaration())
      continue;

    // =====================================================================
    // Step 1 & 2: Replace __cxa_allocate_exception + __cxa_throw
    // =====================================================================
    // Handled by replacing call sites below.

    // =====================================================================
    // Step 3: invoke → call + error-flag check + branch
    // =====================================================================
    std::vector<InvokeInst *> Invokes;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *II = dyn_cast<InvokeInst>(&I))
          Invokes.push_back(II);

    for (auto *II : Invokes) {
      BasicBlock *NormalBB = II->getNormalDest();
      BasicBlock *UnwindBB = II->getUnwindDest();
      BasicBlock *InvokeBB = II->getParent();

      // Create a new basic block for the error check.
      BasicBlock *CheckBB =
          BasicBlock::Create(Ctx, InvokeBB->getName() + ".ehcheck", F,
                             NormalBB);

      // Replace invoke with call.
      IRBuilder<> B(II);
      SmallVector<Value *, 8> Args(II->args());
      SmallVector<OperandBundleDef, 2> Bundles;
      II->getOperandBundlesAsDefs(Bundles);

      CallInst *CI = B.CreateCall(II->getFunctionType(),
                                  II->getCalledOperand(), Args, Bundles);
      CI->setCallingConv(II->getCallingConv());
      CI->setAttributes(II->getAttributes());
      if (!II->getType()->isVoidTy())
        II->replaceAllUsesWith(CI);

      // Branch to check block.
      B.CreateBr(CheckBB);

      // In the check block, load error flag and branch.
      IRBuilder<> CB(CheckBB);
      Value *ErrFlag = CB.CreateLoad(Type::getInt1Ty(Ctx), ES.Flag,
                                     "exclow.err");
      CB.CreateCondBr(ErrFlag, UnwindBB, NormalBB);

      // Remove the original invoke.
      II->eraseFromParent();

      // Remove landingpad from unwind BB if it's the first instruction.
      if (auto *LP = dyn_cast<LandingPadInst>(&UnwindBB->front())) {
        // Step 4: Replace landingpad with loads from error state.
        // Create { i8*, i32 } struct from thread-local error slots.
        IRBuilder<> LPB(LP);
        Value *TI = LPB.CreateLoad(PointerType::getUnqual(Ctx),
                                   ES.TypeInfo, "exclow.ti");
        // Build the { i8*, i32 } struct.
        Type *LPTy = LP->getType();
        Value *Result = UndefValue::get(LPTy);
        Result = LPB.CreateInsertValue(Result, TI, 0);
        // typeinfo selector — use 0 as default
        Result = LPB.CreateInsertValue(
            Result, ConstantInt::get(Type::getInt32Ty(Ctx), 0), 1);
        LP->replaceAllUsesWith(Result);
        LP->eraseFromParent();
      }

      Changed = true;
    }

    // =====================================================================
    // Step 5 & 6: __cxa_begin_catch → load value, __cxa_end_catch → remove
    // =====================================================================
    std::vector<CallInst *> ToRemove;
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = dyn_cast<CallInst>(&I);
        if (!CI || !CI->getCalledFunction())
          continue;

        StringRef Name = CI->getCalledFunction()->getName();

        if (Name == "__cxa_allocate_exception") {
          // Step 1: Replace with alloca of requested size.
          IRBuilder<> B(CI);
          Value *Size = CI->getArgOperand(0);
          Value *Alloc = B.CreateAlloca(Type::getInt8Ty(Ctx), Size,
                                        "exclow.exn");
          CI->replaceAllUsesWith(Alloc);
          ToRemove.push_back(CI);
          Changed = true;
        } else if (Name == "__cxa_throw") {
          // Step 2: Store error info and return sentinel.
          IRBuilder<> B(CI);
          B.CreateStore(ConstantInt::getTrue(Ctx), ES.Flag);
          B.CreateStore(CI->getArgOperand(1), ES.TypeInfo);
          B.CreateStore(CI->getArgOperand(0), ES.Value);
          Value *Sentinel = getSentinelReturn(B, *F);
          if (Sentinel)
            B.CreateRet(Sentinel);
          else
            B.CreateRetVoid();
          // Remove everything after the throw in this BB.
          ToRemove.push_back(CI);
          Changed = true;
        } else if (Name == "__cxa_begin_catch") {
          // Step 5: Load exception value and clear flag.
          IRBuilder<> B(CI);
          Value *ExnVal = B.CreateLoad(PointerType::getUnqual(Ctx),
                                       ES.Value, "exclow.caught");
          B.CreateStore(ConstantInt::getFalse(Ctx), ES.Flag);
          CI->replaceAllUsesWith(ExnVal);
          ToRemove.push_back(CI);
          Changed = true;
        } else if (Name == "__cxa_end_catch") {
          // Step 6: No-op — just remove.
          ToRemove.push_back(CI);
          Changed = true;
        }
      }
    }

    for (auto *CI : ToRemove)
      CI->eraseFromParent();

    // =====================================================================
    // Step 7: resume → re-set error flag and return sentinel
    // =====================================================================
    std::vector<ResumeInst *> Resumes;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *RI = dyn_cast<ResumeInst>(&I))
          Resumes.push_back(RI);

    for (auto *RI : Resumes) {
      IRBuilder<> B(RI);
      B.CreateStore(ConstantInt::getTrue(Ctx), ES.Flag);
      Value *Sentinel = getSentinelReturn(B, *F);
      if (Sentinel)
        B.CreateRet(Sentinel);
      else
        B.CreateRetVoid();
      RI->eraseFromParent();
      Changed = true;
    }
  }

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

} // namespace exclow
