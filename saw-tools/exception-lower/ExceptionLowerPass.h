#ifndef EXCEPTION_LOWER_PASS_H
#define EXCEPTION_LOWER_PASS_H

#include "llvm/IR/PassManager.h"

namespace exclow {

/// ExceptionLowerPass - Replaces C++ exception-handling constructs with
/// explicit error-flag control flow so that the resulting bitcode can be
/// analysed by tools (e.g. SAW) that do not model the Itanium EH ABI.
class ExceptionLowerPass
    : public llvm::PassInfoMixin<ExceptionLowerPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static bool isRequired() { return true; }
};

} // namespace exclow

#endif // EXCEPTION_LOWER_PASS_H
