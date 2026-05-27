; throw_then_unreachable.ll -- the canonical Itanium throw shape:
;   %exn = call @__cxa_allocate_exception(size)
;   store payload into %exn
;   call void @__cxa_throw(%exn, typeinfo, dtor)
;   unreachable
;
; The pass must:
;   * replace allocate_exception with an alloca,
;   * replace __cxa_throw with stores into the thread-local error
;     state plus a sentinel return,
;   * erase the trailing `unreachable` (and anything else after the
;     synthesized return) so the block ends in exactly one terminator.
;
; Expected after lowering:
;   * No `__cxa_*` calls remain.
;   * No `unreachable` remains in this function.
;   * The block ends in `ret i32 ...`.
;   * `opt -passes=verify` accepts the output.

target triple = "x86_64-pc-linux-gnu"

@_ZTIi = external constant ptr

declare ptr @__cxa_allocate_exception(i64)
declare void @__cxa_throw(ptr, ptr, ptr)

define i32 @throws() {
entry:
  %exn = call ptr @__cxa_allocate_exception(i64 4)
  store i32 -1, ptr %exn, align 4
  call void @__cxa_throw(ptr %exn, ptr @_ZTIi, ptr null)
  unreachable
}
