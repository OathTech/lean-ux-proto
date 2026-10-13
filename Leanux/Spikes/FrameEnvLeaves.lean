import Leanux.Spikes.FrameWGDevice
import Leanux.Env
import Leanux.Spikes.SnapshotRules

/-! Framing the inner IP delivery cut and scheduler/environment leaves. -/
namespace Leanux.Spikes.Lifetimes.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Spikes.Lifetimes
open KernelFrames WGFrames WGTransitions WGMore WGConfig WGDevice

set_option maxHeartbeats 400000

theorem excluded_sameSnapshot (row : String) : SameSnapshot (Leanux.Env.Stack.excluded row) := by
  frame_same [Leanux.Env.Stack.excluded] using []

theorem excluded_spec (P : Snapshot → Prop) (row : String) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.Stack.excluded row)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (excluded_sameSnapshot row).wp P

theorem reply4_ordinary (dst : Nat) (bytes : List UInt8) : OrdinaryAction (Leanux.Env.Stack.reply4 dst bytes) := by
  frame_ordinary [Leanux.Env.Stack.reply4] using [skipCut_spec, getDev_spec] ordinary [wgXmit_spec]

theorem reply4_spec (P : Snapshot → Prop) (hp : Stable P) (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.Stack.reply4 dst bytes)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (reply4_ordinary dst bytes).wp P hp

theorem receive4_ordinary (pkt : List UInt8) : OrdinaryAction (Leanux.Env.Stack.receive4 pkt) := by
  frame_ordinary [Leanux.Env.Stack.receive4, Leanux.Env.Stack.excluded] using [] ordinary [reply4_spec]

theorem receive4_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.Stack.receive4 pkt)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receive4_ordinary pkt).wp P hp

theorem receive6_sameSnapshot (pkt : List UInt8) : SameSnapshot (Leanux.Env.Stack.receive6 pkt) := by
  frame_same [Leanux.Env.Stack.receive6, Leanux.Env.Stack.excluded] using []

theorem receive6_spec (P : Snapshot → Prop) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.Stack.receive6 pkt)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receive6_sameSnapshot pkt).wp P

theorem receive_ordinary (pkt : List UInt8) : OrdinaryAction (Leanux.Env.Stack.receive pkt) := by
  frame_ordinary [Leanux.Env.Stack.receive] using [receive6_spec] ordinary [receive4_spec]

theorem receive_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.Stack.receive pkt)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receive_ordinary pkt).wp P hp

theorem deliverInner_ordinary (pkt : List UInt8) : OrdinaryAction (Leanux.Env.deliverInner pkt) := by
  frame_ordinary [Leanux.Env.deliverInner] using [] ordinary [receive_spec]

theorem deliverInner_spec (P : Snapshot → Prop) (hp : Stable P) (pkt : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.deliverInner pkt)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (deliverInner_ordinary pkt).wp P hp

theorem checksumHelp_sameSnapshot (pkt : Packet) : SameSnapshot (Leanux.Env.checksumHelp pkt) := by
  frame_same [Leanux.Env.checksumHelp] using []

theorem checksumHelp_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Leanux.Env.checksumHelp pkt)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (checksumHelp_sameSnapshot pkt).wp P

theorem deliverSent_sameSnapshot  : SameSnapshot Leanux.Env.deliverSent := by
  frame_same [Leanux.Env.deliverSent] using []

theorem deliverSent_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.Env.deliverSent
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (deliverSent_sameSnapshot ).wp P

theorem peekNextSite_sameSnapshot  : SameSnapshot Leanux.Env.peekNextSite := by
  frame_same [Leanux.Env.peekNextSite] using []

theorem peekNextSite_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.Env.peekNextSite
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (peekNextSite_sameSnapshot ).wp P

theorem senderSource_sameSnapshot (family dest tos : Nat) (ll : Bool) :
    SameSnapshot (Leanux.Env.senderSource family dest tos ll) := by
  frame_same [Leanux.Env.senderSource] using []

theorem senderSource_spec (P : Snapshot → Prop) (family dest tos : Nat) (ll : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.Env.senderSource family dest tos ll
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (senderSource_sameSnapshot family dest tos ll).wp P

theorem fixtureSend_sameSnapshot : SameSnapshot Leanux.Env.fixtureSend := by
  frame_same [Leanux.Env.fixtureSend] using [skipCut_spec]

theorem fixtureSend_spec (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.Env.fixtureSend
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := fixtureSend_sameSnapshot.wp P

theorem condResched_sameSnapshot (self : Worker) : SameSnapshot (Env.condResched self) := by
  frame_same [Env.condResched] using [peekHiddenSite_spec, hidden_snapshot_spec]

theorem condResched_spec (P : Snapshot → Prop) (self : Worker) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.condResched self
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (condResched_sameSnapshot self).wp P

theorem activationHasWork_sameSnapshot (a : Activation) : SameSnapshot (Env.Activation.hasWork a) := by
  frame_same [Env.Activation.hasWork] using [getDev_spec, getPeer_spec, getTxSkb_spec]

theorem activationHasWork_spec (P : Snapshot → Prop) (a : Activation) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.Activation.hasWork a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (activationHasWork_sameSnapshot a).wp P

/-- The trial executes on a copy; its returned World is discarded. -/
theorem activationConsistent_sameSnapshot (a : Activation) : SameSnapshot (Env.Activation.consistent a) := by
  intro w b w' hr
  unfold Env.Activation.consistent at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  cases he : (Env.Activation.run a).run w with
  | ok out =>
    simp only [he, StateT.run_pure] at hr
    cases hr
    rfl
  | error e =>
    simp only [he, StateT.run_pure] at hr
    cases e <;> cases hr <;> rfl

theorem activationConsistent_spec (P : Snapshot → Prop) (a : Activation) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.Activation.consistent a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (activationConsistent_sameSnapshot a).wp P

theorem filterAuxM_sameSnapshot (f : α → M Bool) (hf : ∀ a, SameSnapshot (f a))
    (xs acc : List α) : SameSnapshot (List.filterAuxM f xs acc) := by
  induction xs generalizing acc with
  | nil => exact snapshot_pure _
  | cons a xs ih =>
    exact snapshot_bind (hf a) (fun b => ih (cond b (a :: acc) acc))

theorem filterM_sameSnapshot (f : α → M Bool) (hf : ∀ a, SameSnapshot (f a))
    (xs : List α) : SameSnapshot (xs.filterM f) := by
  exact snapshot_bind (filterAuxM_sameSnapshot f hf xs []) (fun ys => snapshot_pure ys.reverse)

end Leanux.Spikes.Lifetimes.EnvFrames
