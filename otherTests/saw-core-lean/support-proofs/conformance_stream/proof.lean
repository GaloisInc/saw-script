import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
standalone library-proof row (its former driver twin drivers/conformance_stream was retired in the 2026-07-15 restructure; coverage lives in differential/).

The SAW driver proves concrete `Stream#rec`, `MkStream`, and `streamScanl`
facts with SAW's `w4` backend. This file pins the corresponding Lean
support-library realizations directly.
-/

def identityStream : Stream Nat :=
  Stream.MkStream (fun i => i)

def onesStream : Stream Nat :=
  Stream.MkStream (fun _ => 1)

theorem stream_rec_mkStream_semantics :
    @Stream.rec Nat (fun _ => Nat) (fun xs => xs 5) identityStream = 5 := by
  rfl

theorem stream_idx_mkStream_semantics :
    streamIdx Nat identityStream 5 = 5 := by
  rfl

theorem streamScanl_zero_semantics :
    streamIdx Nat (streamScanl Nat Nat addNat 0 onesStream) 0 = 0 := by
  rfl

theorem streamScanl_three_semantics :
    streamIdx Nat (streamScanl Nat Nat addNat 0 onesStream) 3 = 3 := by
  rfl

end
