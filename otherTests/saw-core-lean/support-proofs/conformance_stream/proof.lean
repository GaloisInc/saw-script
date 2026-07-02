import CryptolToLean

open CryptolToLean.SAWCorePrimitives
open CryptolToLean.SAWCorePreludeExtra

noncomputable section

/-!
Lean half of `drivers/conformance_stream`.

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
