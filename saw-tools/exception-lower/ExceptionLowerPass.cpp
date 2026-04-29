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

    // =====================================================================
    // Step 8-12: Windows SEH funclet transforms
    // =====================================================================
    // Windows EH uses catchswitch/catchpad/cleanuppad/catchret/cleanupret
    // instead of Itanium's landingpad/resume/__cxa_* model.  We lower them
    // to plain control-flow using the same thread-local error state.
    //
    // Processing order matters for use-def safety:
    //   rets first  → removes uses of pads
    //   pads second → removes uses of catchswitch
    //   catchswitch last

    // --- Collect all Windows EH instructions in this function. -----------
    std::vector<CatchReturnInst *>  CatchRets;
    std::vector<CleanupReturnInst *> CleanupRets;
    std::vector<CatchPadInst *>     CatchPads;
    std::vector<CleanupPadInst *>   CleanupPads;
    std::vector<CatchSwitchInst *>  CatchSwitches;

    for (auto &BB : *F) {
      for (auto &I : BB) {
        if (auto *CR = dyn_cast<CatchReturnInst>(&I))
          CatchRets.push_back(CR);
        else if (auto *CR = dyn_cast<CleanupReturnInst>(&I))
          CleanupRets.push_back(CR);
        else if (auto *CP = dyn_cast<CatchPadInst>(&I))
          CatchPads.push_back(CP);
        else if (auto *CP = dyn_cast<CleanupPadInst>(&I))
          CleanupPads.push_back(CP);
        else if (auto *CS = dyn_cast<CatchSwitchInst>(&I))
          CatchSwitches.push_back(CS);
      }
    }

    // =====================================================================
    // Step 8: catchret → clear error flag + unconditional branch to dest
    // =====================================================================
    for (auto *CR : CatchRets) {
      IRBuilder<> B(CR);
      B.CreateStore(ConstantInt::getFalse(Ctx), ES.Flag);
      B.CreateBr(CR->getSuccessor());
      CR->eraseFromParent();
      Changed = true;
    }

    // =====================================================================
    // Step 9: cleanupret → branch to unwind dest or return sentinel
    // =====================================================================
    for (auto *CR : CleanupRets) {
      IRBuilder<> B(CR);
      if (CR->hasUnwindDest()) {
        // Continue unwinding to the next handler.
        B.CreateBr(CR->getUnwindDest());
      } else {
        // "unwind to caller" — propagate exception out of function.
        Value *Sentinel = getSentinelReturn(B, *F);
        if (Sentinel)
          B.CreateRet(Sentinel);
        else
          B.CreateRetVoid();
      }
      CR->eraseFromParent();
      Changed = true;
    }

    // =====================================================================
    // Step 10: catchpad → load error value, clear flag, erase token
    // =====================================================================
    for (auto *CP : CatchPads) {
      IRBuilder<> B(CP);
      // Load the thrown object pointer (mirrors __cxa_begin_catch).
      B.CreateLoad(PointerType::getUnqual(Ctx), ES.Value,
                   "exclow.caught");
      B.CreateStore(ConstantInt::getFalse(Ctx), ES.Flag);
      // CatchPad yields a token consumed by catchret; those catchrets are
      // already gone, so any lingering uses get an undef token.
      if (!CP->use_empty())
        CP->replaceAllUsesWith(UndefValue::get(CP->getType()));
      CP->eraseFromParent();
      Changed = true;
    }

    // =====================================================================
    // Step 11: cleanuppad → no-op (cleanup body follows, error stays set)
    // =====================================================================
    for (auto *CP : CleanupPads) {
      if (!CP->use_empty())
        CP->replaceAllUsesWith(UndefValue::get(CP->getType()));
      CP->eraseFromParent();
      Changed = true;
    }

    // =====================================================================
    // Step 12: catchswitch → branch to first handler (or propagate)
    // =====================================================================
    for (auto *CS : CatchSwitches) {
      IRBuilder<> B(CS);
      if (CS->getNumHandlers() > 0) {
        // Dispatch to the first catch handler.
        BasicBlock *FirstHandler = *CS->handler_begin();
        B.CreateBr(FirstHandler);
      } else if (CS->hasUnwindDest()) {
        B.CreateBr(CS->getUnwindDest());
      } else {
        // "unwind to caller" — return error sentinel.
        Value *Sentinel = getSentinelReturn(B, *F);
        if (Sentinel)
          B.CreateRet(Sentinel);
        else
          B.CreateRetVoid();
      }
      CS->eraseFromParent();
      Changed = true;
    }
  }

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

} // namespace exclow
