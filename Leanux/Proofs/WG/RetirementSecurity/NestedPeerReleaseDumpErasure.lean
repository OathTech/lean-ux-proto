import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseErasure

/-! Exact dump cursor callback contracts, including stopped suffixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem dumpDone_erases (h : Ops.Erases g) (ctx : DumpCtx) :
    ErasesStatePrefix (dumpDoneWith g ctx) (dumpDoneWith native ctx) := by
  unfold dumpDoneWith
  repeat' first
    | nested_release_erase h

theorem dumpReplace_erases (h : Ops.Erases g) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    ErasesStatePrefix (dumpReplaceWith g ctx nextCursor done) (dumpReplaceWith native ctx nextCursor done) := by
  unfold dumpReplaceWith
  repeat' first
    | nested_release_erase h

theorem dumpFinish_erases (h : Ops.Erases g) (seq : Nat) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    ErasesStatePrefix (dumpFinishWith g seq ctx nextCursor skb flags attrs done peers) (dumpFinishWith native seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  repeat' first
    | with_reducible exact dumpReplace_erases h _ _ _
    | nested_release_erase h

theorem dumpTail_erases (h : Ops.Erases g) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    ErasesStatePrefix (dumpTailWith g d ctx skb flags attrs) (dumpTailWith native d ctx skb flags attrs) := by
  unfold dumpTailWith
  repeat' first
    | with_reducible exact dumpFinish_erases h _ _ _ _ _ _ _ _
    | nested_release_erase h

theorem dumpChunk_erases (h : Ops.Erases g) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    ErasesStatePrefix (dumpChunkWith g ctx prevSeq skb) (dumpChunkWith native ctx prevSeq skb) := by
  unfold dumpChunkWith
  repeat' first
    | with_reducible exact dumpTail_erases h _ _ _ _ _
    | nested_release_erase h

theorem dumpSocket_erases (h : Ops.Erases g) (fd : Nat) :
    ErasesStatePrefix (dumpSocketWith g fd) (dumpSocketWith native fd) := by
  unfold dumpSocketWith
  repeat' first
    | with_reducible exact dumpChunk_erases h _ _ _
    | with_reducible exact dumpDone_erases h _
    | nested_release_erase h

theorem dumpStart_erases (h : Ops.Erases g) (fd : Nat) (ref : DeviceRef) :
    ErasesStatePrefix (dumpStartWith g fd ref) (dumpStartWith native fd ref) := by
  unfold dumpStartWith
  repeat' first
    | with_reducible exact dumpSocket_erases h _
    | nested_release_erase h

theorem dumpReceive_erases (h : Ops.Erases g) (fd : Nat) :
    ErasesStatePrefix (dumpReceiveWith g fd) (dumpReceiveWith native fd) := by
  unfold dumpReceiveWith
  repeat' first
    | with_reducible exact dumpSocket_erases h _
    | nested_release_erase h

theorem dumpDevice_erases (h : Ops.Erases g) (ref : DeviceRef) :
    ErasesStatePrefix (dumpDeviceWith g ref) (dumpDeviceWith native ref) := by
  unfold dumpDeviceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact dumpStart_erases h _ _
    | with_reducible exact dumpReceive_erases h _
    | nested_release_erase h

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
