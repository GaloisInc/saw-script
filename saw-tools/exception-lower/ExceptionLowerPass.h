#ifndef EXCEPTION_LOWER_PASS_H
#define EXCEPTION_LOWER_PASS_H

#include "llvm/IR/PassManager.h"

namespace exclow {

/// ExceptionLowerPass - Replaces C++ exception-handling constructs with
/// explicit error-flag control flow so that the resulting bitcode can be
/// analysed by tools (such as SAW) that do not model stack unwinding.
///
/// Handles both the Itanium exception-handling ABI
/// (`invoke` / `landingpad` / `resume` / `__cxa_*`) used on Linux and
/// macOS, and the Windows Structured Exception Handling (SEH) funclet
/// model (`catchswitch` / `catchpad` / `cleanuppad` / `catchret` /
/// `cleanupret`) used by MSVC and `clang-cl`.
class ExceptionLowerPass
    : public llvm::PassInfoMixin<ExceptionLowerPass> {
public:
  llvm::PreservedAnalyses run(llvm::Module &Mod,
                              llvm::ModuleAnalysisManager &);

  static bool isRequired() { return true; }
};

} // namespace exclow

#endif // EXCEPTION_LOWER_PASS_H
