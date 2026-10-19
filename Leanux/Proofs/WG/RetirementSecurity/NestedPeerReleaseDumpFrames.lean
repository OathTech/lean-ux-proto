import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseFrames

/-! Exact dump cursor callback contracts, including stopped suffixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem dumpDone_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (ctx : DumpCtx) :
    StateHistoryFrame ρ (dumpDoneWith g ctx) := by
  unfold dumpDoneWith
  repeat' first
    | nested_release_frame h ρ

theorem dumpReplace_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    StateHistoryFrame ρ (dumpReplaceWith g ctx nextCursor done) := by
  unfold dumpReplaceWith
  repeat' first
    | nested_release_frame h ρ

theorem dumpFinish_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (seq : Nat) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    StateHistoryFrame ρ (dumpFinishWith g seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  repeat' first
    | with_reducible exact dumpReplace_frame ρ h _ _ _
    | nested_release_frame h ρ

theorem dumpTail_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    StateHistoryFrame ρ (dumpTailWith g d ctx skb flags attrs) := by
  unfold dumpTailWith
  repeat' first
    | with_reducible exact dumpFinish_frame ρ h _ _ _ _ _ _ _ _
    | nested_release_frame h ρ

theorem dumpChunk_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    StateHistoryFrame ρ (dumpChunkWith g ctx prevSeq skb) := by
  unfold dumpChunkWith
  repeat' first
    | with_reducible exact dumpTail_frame ρ h _ _ _ _ _
    | nested_release_frame h ρ

theorem dumpSocket_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (fd : Nat) :
    StateHistoryFrame ρ (dumpSocketWith g fd) := by
  unfold dumpSocketWith
  repeat' first
    | with_reducible exact dumpChunk_frame ρ h _ _ _
    | with_reducible exact dumpDone_frame ρ h _
    | nested_release_frame h ρ

theorem dumpStart_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (fd : Nat) (ref : DeviceRef) :
    StateHistoryFrame ρ (dumpStartWith g fd ref) := by
  unfold dumpStartWith
  repeat' first
    | with_reducible exact dumpSocket_frame ρ h _
    | nested_release_frame h ρ

theorem dumpReceive_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (fd : Nat) :
    StateHistoryFrame ρ (dumpReceiveWith g fd) := by
  unfold dumpReceiveWith
  repeat' first
    | with_reducible exact dumpSocket_frame ρ h _
    | nested_release_frame h ρ

theorem dumpDevice_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (ref : DeviceRef) :
    StateHistoryFrame ρ (dumpDeviceWith g ref) := by
  unfold dumpDeviceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact dumpStart_frame ρ h _ _
    | with_reducible exact dumpReceive_frame ρ h _
    | nested_release_frame h ρ

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
