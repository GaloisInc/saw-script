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

namespace {

// Names of the thread-local globals that hold the in-flight error state.
// Internalized so they cannot clash with user symbols.
constexpr StringRef kInFlightFlagGlobalName    = "__exclow_error_flag";
constexpr StringRef kThrownTypeInfoGlobalName  = "__exclow_error_typeinfo";
constexpr StringRef kThrownValuePtrGlobalName  = "__exclow_error_value";

// Thread-local globals representing "an exception is currently propagating".
// Together these stand in for the unwinder ABI in lowered bitcode.
struct ErrorState {
  GlobalVariable *InFlightFlag;       // i1:  true while an exception is live
  GlobalVariable *ThrownTypeInfo;     // ptr: std::type_info of thrown object
  GlobalVariable *ThrownValuePtr;     // ptr: address of the thrown object
};

GlobalVariable *getOrCreateThreadLocalGlobal(Module &Mod,
                                             StringRef GlobalName,
                                             Type *GlobalType) {
  if (auto *Existing = Mod.getGlobalVariable(GlobalName))
    return Existing;
  auto *Global = new GlobalVariable(Mod, GlobalType, /*isConstant=*/false,
                                    GlobalValue::InternalLinkage,
                                    Constant::getNullValue(GlobalType),
                                    GlobalName);
  Global->setThreadLocal(true);
  return Global;
}

ErrorState getOrCreateErrorState(Module &Mod) {
  auto &Context = Mod.getContext();
  auto *BoolType = Type::getInt1Ty(Context);
  auto *OpaquePtrType = PointerType::getUnqual(Context);
  return {
      getOrCreateThreadLocalGlobal(Mod, kInFlightFlagGlobalName, BoolType),
      getOrCreateThreadLocalGlobal(Mod, kThrownTypeInfoGlobalName,
                                   OpaquePtrType),
      getOrCreateThreadLocalGlobal(Mod, kThrownValuePtrGlobalName,
                                   OpaquePtrType),
  };
}

// A "sentinel" return value used to propagate an error out of any function
// that lacks a real unwind path after lowering.  The choice is per-type:
// integers use -1, pointers use null, floats use NaN, aggregates use zero.
Value *makeSentinelReturnValue(Function &Func) {
  Type *ReturnType = Func.getReturnType();
  if (ReturnType->isVoidTy())
    return nullptr;
  if (ReturnType->isPointerTy())
    return ConstantPointerNull::get(cast<PointerType>(ReturnType));
  if (ReturnType->isIntegerTy())
    return ConstantInt::get(ReturnType, -1);
  if (ReturnType->isFloatingPointTy())
    return ConstantFP::getNaN(ReturnType);
  return Constant::getNullValue(ReturnType);
}

// Emit "store true→InFlightFlag; ret <sentinel-or-void>" at Builder.
void emitErrorReturn(IRBuilder<> &Builder, Function &Func,
                     ErrorState &State) {
  Builder.CreateStore(ConstantInt::getTrue(Builder.getContext()),
                      State.InFlightFlag);
  if (Value *Sentinel = makeSentinelReturnValue(Func))
    Builder.CreateRet(Sentinel);
  else
    Builder.CreateRetVoid();
}

// Replace `landingpad` with a synthetic `{ ptr, i32 }` built from the
// thread-local typeinfo slot.  The selector is left as 0 since downstream
// catch dispatch is also lowered to plain control flow.
void lowerLandingPadInPlace(LandingPadInst *LandingPad, ErrorState &State) {
  auto &Context = LandingPad->getContext();
  IRBuilder<> Builder(LandingPad);
  Value *TypeInfo = Builder.CreateLoad(PointerType::getUnqual(Context),
                                       State.ThrownTypeInfo, "exclow.ti");
  Value *Result = UndefValue::get(LandingPad->getType());
  Result = Builder.CreateInsertValue(Result, TypeInfo, 0);
  Result = Builder.CreateInsertValue(
      Result, ConstantInt::get(Type::getInt32Ty(Context), 0), 1);
  LandingPad->replaceAllUsesWith(Result);
  LandingPad->eraseFromParent();
}

// invoke → call + ehcheck block that branches on InFlightFlag.
bool lowerInvokes(Function &Func, ErrorState &State) {
  bool Changed = false;
  auto &Context = Func.getContext();

  std::vector<InvokeInst *> Invokes;
  for (auto &BB : Func)
    for (auto &Inst : BB)
      if (auto *Invoke = dyn_cast<InvokeInst>(&Inst))
        Invokes.push_back(Invoke);

  for (auto *Invoke : Invokes) {
    BasicBlock *NormalDest = Invoke->getNormalDest();
    BasicBlock *UnwindDest = Invoke->getUnwindDest();
    BasicBlock *InvokeBlock = Invoke->getParent();

    BasicBlock *ErrorCheckBlock = BasicBlock::Create(
        Context, InvokeBlock->getName() + ".ehcheck", &Func, NormalDest);

    IRBuilder<> Builder(Invoke);
    SmallVector<Value *, 8> CallArgs(Invoke->args());
    SmallVector<OperandBundleDef, 2> CallBundles;
    Invoke->getOperandBundlesAsDefs(CallBundles);

    CallInst *DirectCall = Builder.CreateCall(Invoke->getFunctionType(),
                                              Invoke->getCalledOperand(),
                                              CallArgs, CallBundles);
    DirectCall->setCallingConv(Invoke->getCallingConv());
    DirectCall->setAttributes(Invoke->getAttributes());
    if (!Invoke->getType()->isVoidTy())
      Invoke->replaceAllUsesWith(DirectCall);
    Builder.CreateBr(ErrorCheckBlock);

    IRBuilder<> CheckBuilder(ErrorCheckBlock);
    Value *InFlight = CheckBuilder.CreateLoad(Type::getInt1Ty(Context),
                                              State.InFlightFlag,
                                              "exclow.err");
    CheckBuilder.CreateCondBr(InFlight, UnwindDest, NormalDest);

    Invoke->eraseFromParent();

    if (auto *LandingPad = dyn_cast<LandingPadInst>(&UnwindDest->front()))
      lowerLandingPadInPlace(LandingPad, State);

    Changed = true;
  }
  return Changed;
}

// Replace the Itanium C++ runtime calls with explicit moves in and out of
// the thread-local error state:
//   __cxa_allocate_exception(size) → alloca i8, size
//   __cxa_throw(obj, tinfo, ...)   → store flag/tinfo/obj; ret <sentinel>
//   __cxa_begin_catch(...)         → load ThrownValuePtr; store false→flag
//   __cxa_end_catch()              → erase
bool lowerItaniumRuntimeCalls(Function &Func, ErrorState &State) {
  bool Changed = false;
  auto &Context = Func.getContext();

  std::vector<CallInst *> CallsToErase;
  for (auto &BB : Func) {
    for (auto &Inst : BB) {
      auto *Call = dyn_cast<CallInst>(&Inst);
      if (!Call || !Call->getCalledFunction())
        continue;
      StringRef Callee = Call->getCalledFunction()->getName();

      if (Callee == "__cxa_allocate_exception") {
        IRBuilder<> Builder(Call);
        Value *RequestedSize = Call->getArgOperand(0);
        Value *Storage = Builder.CreateAlloca(Type::getInt8Ty(Context),
                                              RequestedSize, "exclow.exn");
        Call->replaceAllUsesWith(Storage);
        CallsToErase.push_back(Call);
        Changed = true;
      } else if (Callee == "__cxa_throw") {
        IRBuilder<> Builder(Call);
        Builder.CreateStore(Call->getArgOperand(1), State.ThrownTypeInfo);
        Builder.CreateStore(Call->getArgOperand(0), State.ThrownValuePtr);
        emitErrorReturn(Builder, Func, State);
        CallsToErase.push_back(Call);
        Changed = true;
      } else if (Callee == "__cxa_begin_catch") {
        IRBuilder<> Builder(Call);
        Value *Caught = Builder.CreateLoad(PointerType::getUnqual(Context),
                                           State.ThrownValuePtr,
                                           "exclow.caught");
        Builder.CreateStore(ConstantInt::getFalse(Context),
                            State.InFlightFlag);
        Call->replaceAllUsesWith(Caught);
        CallsToErase.push_back(Call);
        Changed = true;
      } else if (Callee == "__cxa_end_catch") {
        CallsToErase.push_back(Call);
        Changed = true;
      }
    }
  }
  for (auto *Call : CallsToErase)
    Call->eraseFromParent();
  return Changed;
}

// resume <slot> → store true→flag; ret <sentinel>
bool lowerResumes(Function &Func, ErrorState &State) {
  bool Changed = false;
  std::vector<ResumeInst *> Resumes;
  for (auto &BB : Func)
    for (auto &Inst : BB)
      if (auto *Resume = dyn_cast<ResumeInst>(&Inst))
        Resumes.push_back(Resume);

  for (auto *Resume : Resumes) {
    IRBuilder<> Builder(Resume);
    emitErrorReturn(Builder, Func, State);
    Resume->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

// Windows SEH funclets do not have an Itanium analogue; the unwinder is
// implicit in the catchswitch/pad/ret structure.  We collapse it to plain
// control flow using the same thread-local error state.  Ordering matters:
// catch/cleanup-ret first (removes uses of pads), pads next (removes uses
// of catchswitches), then the switches themselves.
struct SehFunclets {
  std::vector<CatchReturnInst *>   CatchReturns;
  std::vector<CleanupReturnInst *> CleanupReturns;
  std::vector<CatchPadInst *>      CatchPads;
  std::vector<CleanupPadInst *>    CleanupPads;
  std::vector<CatchSwitchInst *>   CatchSwitches;
};

SehFunclets collectSehFunclets(Function &Func) {
  SehFunclets Funclets;
  for (auto &BB : Func) {
    for (auto &Inst : BB) {
      if (auto *CatchRet = dyn_cast<CatchReturnInst>(&Inst))
        Funclets.CatchReturns.push_back(CatchRet);
      else if (auto *CleanupRet = dyn_cast<CleanupReturnInst>(&Inst))
        Funclets.CleanupReturns.push_back(CleanupRet);
      else if (auto *CatchPad = dyn_cast<CatchPadInst>(&Inst))
        Funclets.CatchPads.push_back(CatchPad);
      else if (auto *CleanupPad = dyn_cast<CleanupPadInst>(&Inst))
        Funclets.CleanupPads.push_back(CleanupPad);
      else if (auto *CatchSwitch = dyn_cast<CatchSwitchInst>(&Inst))
        Funclets.CatchSwitches.push_back(CatchSwitch);
    }
  }
  return Funclets;
}

bool lowerCatchReturns(ArrayRef<CatchReturnInst *> CatchReturns,
                       ErrorState &State) {
  bool Changed = false;
  for (auto *CatchRet : CatchReturns) {
    IRBuilder<> Builder(CatchRet);
    Builder.CreateStore(ConstantInt::getFalse(Builder.getContext()),
                        State.InFlightFlag);
    Builder.CreateBr(CatchRet->getSuccessor());
    CatchRet->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

bool lowerCleanupReturns(ArrayRef<CleanupReturnInst *> CleanupReturns,
                         Function &Func, ErrorState &State) {
  bool Changed = false;
  for (auto *CleanupRet : CleanupReturns) {
    IRBuilder<> Builder(CleanupRet);
    if (CleanupRet->hasUnwindDest()) {
      Builder.CreateBr(CleanupRet->getUnwindDest());
    } else {
      // "unwind to caller" — propagate the error out of this function.
      emitErrorReturn(Builder, Func, State);
    }
    CleanupRet->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

bool lowerCatchPads(ArrayRef<CatchPadInst *> CatchPads, ErrorState &State) {
  bool Changed = false;
  for (auto *CatchPad : CatchPads) {
    IRBuilder<> Builder(CatchPad);
    Builder.CreateLoad(PointerType::getUnqual(Builder.getContext()),
                       State.ThrownValuePtr, "exclow.caught");
    Builder.CreateStore(ConstantInt::getFalse(Builder.getContext()),
                        State.InFlightFlag);
    if (!CatchPad->use_empty())
      CatchPad->replaceAllUsesWith(UndefValue::get(CatchPad->getType()));
    CatchPad->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

bool lowerCleanupPads(ArrayRef<CleanupPadInst *> CleanupPads) {
  bool Changed = false;
  for (auto *CleanupPad : CleanupPads) {
    // Cleanup body follows in the same block; the error stays in flight.
    if (!CleanupPad->use_empty())
      CleanupPad->replaceAllUsesWith(UndefValue::get(CleanupPad->getType()));
    CleanupPad->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

bool lowerCatchSwitches(ArrayRef<CatchSwitchInst *> CatchSwitches,
                        Function &Func, ErrorState &State) {
  bool Changed = false;
  for (auto *CatchSwitch : CatchSwitches) {
    IRBuilder<> Builder(CatchSwitch);
    if (CatchSwitch->getNumHandlers() > 0) {
      // Dispatch to the first handler; type-matching is folded away.
      Builder.CreateBr(*CatchSwitch->handler_begin());
    } else if (CatchSwitch->hasUnwindDest()) {
      Builder.CreateBr(CatchSwitch->getUnwindDest());
    } else {
      emitErrorReturn(Builder, Func, State);
    }
    CatchSwitch->eraseFromParent();
    Changed = true;
  }
  return Changed;
}

bool lowerSehFunclets(Function &Func, ErrorState &State) {
  SehFunclets Funclets = collectSehFunclets(Func);
  bool Changed = false;
  Changed |= lowerCatchReturns(Funclets.CatchReturns, State);
  Changed |= lowerCleanupReturns(Funclets.CleanupReturns, Func, State);
  Changed |= lowerCatchPads(Funclets.CatchPads, State);
  Changed |= lowerCleanupPads(Funclets.CleanupPads);
  Changed |= lowerCatchSwitches(Funclets.CatchSwitches, Func, State);
  return Changed;
}

} // namespace

PreservedAnalyses ExceptionLowerPass::run(Module &Mod,
                                          ModuleAnalysisManager &) {
  ErrorState State = getOrCreateErrorState(Mod);
  bool Changed = false;

  // Snapshot the function list to avoid iterator invalidation when the
  // helpers below splice or erase blocks.
  std::vector<Function *> Functions;
  for (auto &Func : Mod)
    Functions.push_back(&Func);

  for (auto *Func : Functions) {
    if (Func->isDeclaration())
      continue;
    Changed |= lowerInvokes(*Func, State);
    Changed |= lowerItaniumRuntimeCalls(*Func, State);
    Changed |= lowerResumes(*Func, State);
    Changed |= lowerSehFunclets(*Func, State);
  }

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

} // namespace exclow
