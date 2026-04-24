#include "ExceptionLowerPass.h"

#include "llvm/IR/Module.h"

using namespace llvm;

namespace exclow {

PreservedAnalyses ExceptionLowerPass::run(Module &M,
                                          ModuleAnalysisManager &MAM) {
  // TODO [bvk step 1]: __cxa_allocate_exception → allocate an error struct
  //   Replace calls to __cxa_allocate_exception(size) with an alloca (or
  //   global) that holds the exception object.

  // TODO [bvk step 2]: __cxa_throw → store error type/value in thread-local,
  //                     return error sentinel
  //   Replace calls to __cxa_throw(ptr, typeinfo, dtor) with:
  //     1. Store the typeinfo pointer into a thread-local error-type slot.
  //     2. Store the exception pointer into a thread-local error-value slot.
  //     3. Set thread-local error flag to true.
  //     4. Return an error sentinel value from the enclosing function.

  // TODO [bvk step 3]: invoke → call + check thread-local error flag + branch
  //   Replace each `invoke @fn(...) to label %normal unwind label %unwind`
  //   with:
  //     1. A regular `call @fn(...)`.
  //     2. A load of the thread-local error flag.
  //     3. A conditional branch: if error, goto %unwind; else goto %normal.

  // TODO [bvk step 4]: landingpad → read error type from thread-local
  //   Replace `landingpad` instructions with loads from the thread-local
  //   error-type and error-value slots, packed into the expected
  //   { i8*, i32 } struct.

  // TODO [bvk step 5]: __cxa_begin_catch → read and clear active exception
  //   Replace calls to __cxa_begin_catch(ptr) with:
  //     1. Load the error-value pointer from thread-local.
  //     2. Clear the error flag.

  // TODO [bvk step 6]: __cxa_end_catch → no-op
  //   Remove (or replace with nothing) calls to __cxa_end_catch.

  // TODO [bvk step 7]: resume → re-set error flag and return error sentinel
  //   Replace `resume` instructions with:
  //     1. Re-set the thread-local error flag to true.
  //     2. Return the error sentinel from the enclosing function.

  // No transformations yet — pass through unchanged.
  return PreservedAnalyses::all();
}

} // namespace exclow
