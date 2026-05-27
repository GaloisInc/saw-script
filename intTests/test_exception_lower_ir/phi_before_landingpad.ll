; phi_before_landingpad.ll -- reproduces the case that was miscompiled
; before the landingpad-detection fix: two invokes share the same
; unwind block, and that block carries a PHI *above* the landingpad.
;
; Per the LLVM language reference, "A landingpad instruction must be
; the first non-PHI instruction in the block".  The previous version
; of the pass inspected `UnwindDest->front()` directly, found a PHI,
; and skipped landingpad lowering -- leaving structurally invalid EH
; control flow (call + br to an unwind block that still contained a
; landingpad whose predecessor edges no longer existed).
;
; Expected after the fix:
;   * No `invoke` or `landingpad` instructions remain.
;   * The PHI in the (formerly unwind) block references the synthetic
;     `.ehcheck` predecessors, not the original invoke blocks.
;   * `opt -passes=verify` accepts the output.

target triple = "x86_64-pc-linux-gnu"

@_ZTIi = external constant ptr

declare i32 @__gxx_personality_v0(...)
declare void @callee()
declare ptr @__cxa_begin_catch(ptr)
declare void @__cxa_end_catch()

define i32 @two_invokes_one_lpad(i32 %x) personality ptr @__gxx_personality_v0 {
entry:
  %cmp = icmp slt i32 %x, 0
  br i1 %cmp, label %first, label %second

first:
  invoke void @callee() to label %ok unwind label %lpad

second:
  invoke void @callee() to label %ok unwind label %lpad

ok:
  ret i32 0

lpad:
  ; PHI sits *above* the landingpad -- this is what the previous
  ; pass missed.
  %tag = phi i32 [ 1, %first ], [ 2, %second ]
  %lp = landingpad { ptr, i32 }
          catch ptr @_ZTIi
  %ex = extractvalue { ptr, i32 } %lp, 0
  %caught = call ptr @__cxa_begin_catch(ptr %ex)
  call void @__cxa_end_catch()
  ret i32 %tag
}
