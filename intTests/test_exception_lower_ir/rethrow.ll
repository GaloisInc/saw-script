; rethrow.ll -- `throw;` inside a catch handler lowers to a
; `__cxa_rethrow` call.  The pass must turn this into "re-set the
; in-flight flag and return a sentinel" and erase the trailing
; `unreachable`.
;
; Expected after lowering:
;   * No `__cxa_rethrow` call remains.
;   * No `unreachable` remains.
;   * The block ends in `ret void`.
;   * `opt -passes=verify` accepts the output.

target triple = "x86_64-pc-linux-gnu"

declare void @__cxa_rethrow()

define void @rethrower() {
entry:
  call void @__cxa_rethrow()
  unreachable
}
