import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseProjection

/-! Exact dump cursor callback contracts, including stopped suffixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

private theorem dump_forIn (ρ : E → Option F) (xs : List α) (b : β)
    (g : α → β → WGPrefix E (ForInStep β)) (t : α → β → WGPrefix F (ForInStep β))
    (same : ∀ x b, StateProjectsPrefix ρ id (g x b) (t x b)) :
    StateProjectsPrefix ρ id (forIn xs b g) (forIn xs b t) := by
  induction xs generalizing b with
  | nil => intro w a h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons,List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (same x b)
    intro step
    cases step with
    | done value => intro w a h; rfl
    | yield value => exact ih value

theorem dumpDone_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (ctx : DumpCtx) :
    StateProjectsPrefix ρ id (dumpDoneWith g ctx) (dumpDoneWith t ctx) := by
  unfold dumpDoneWith
  repeat' first
    | nested_release_project h ρ

theorem dumpReplace_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (ctx : DumpCtx) (nextCursor : Option PeerId) (done : Bool) :
    StateProjectsPrefix ρ id (dumpReplaceWith g ctx nextCursor done) (dumpReplaceWith t ctx nextCursor done) := by
  unfold dumpReplaceWith
  repeat' first
    | nested_release_project h ρ

theorem dumpFinish_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (seq : Nat) (ctx : DumpCtx) (nextCursor : Option PeerId) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool) (peers : Option (Array PeerDumpAttrs)) :
    StateProjectsPrefix ρ id (dumpFinishWith g seq ctx nextCursor skb flags attrs done peers) (dumpFinishWith t seq ctx nextCursor skb flags attrs done peers) := by
  unfold dumpFinishWith
  repeat' first
    | with_reducible exact dumpReplace_projects ρ h _ _ _
    | nested_release_project h ρ

theorem dumpTail_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (d : Device) (ctx : DumpCtx) (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    StateProjectsPrefix ρ id (dumpTailWith g d ctx skb flags attrs) (dumpTailWith t d ctx skb flags attrs) := by
  unfold dumpTailWith
  repeat' first
    | with_reducible exact dumpFinish_projects ρ h _ _ _ _ _ _ _ _
    | nested_release_project h ρ

theorem dumpChunk_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    StateProjectsPrefix ρ id (dumpChunkWith g ctx prevSeq skb) (dumpChunkWith t ctx prevSeq skb) := by
  unfold dumpChunkWith
  repeat' first
    | with_reducible exact dumpTail_projects ρ h _ _ _ _ _
    | nested_release_project h ρ

theorem dumpSocket_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (fd : Nat) :
    StateProjectsPrefix ρ id (dumpSocketWith g fd) (dumpSocketWith t fd) := by
  unfold dumpSocketWith
  repeat' first
    | with_reducible exact dumpChunk_projects ρ h _ _ _
    | with_reducible exact dumpDone_projects ρ h _
    | nested_release_project h ρ

theorem dumpStart_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (fd : Nat) (ref : DeviceRef) :
    StateProjectsPrefix ρ id (dumpStartWith g fd ref) (dumpStartWith t fd ref) := by
  unfold dumpStartWith
  repeat' first
    | with_reducible exact dumpSocket_projects ρ h _
    | nested_release_project h ρ

theorem dumpReceive_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (fd : Nat) :
    StateProjectsPrefix ρ id (dumpReceiveWith g fd) (dumpReceiveWith t fd) := by
  unfold dumpReceiveWith
  repeat' first
    | with_reducible exact dumpSocket_projects ρ h _
    | nested_release_project h ρ

theorem dumpDevice_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (ref : DeviceRef) :
    StateProjectsPrefix ρ id (dumpDeviceWith g ref) (dumpDeviceWith t ref) := by
  unfold dumpDeviceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact dumpStart_projects ρ h _ _
    | with_reducible exact dumpReceive_projects ρ h _
    | with_reducible apply dump_forIn ρ
    | nested_release_project h ρ

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
