import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! Actual admission/publication history frames retain the reached accesses,
queue events and nested releases independently of native endpoint erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem actual_appends_ops : TxSource.Ops.Appends actualOps where
  step := fun _ => Appends.focus _ _ _
  access := fun _ => Appends.focus _ _ _
  event := fun _ => Appends.focus _ _ _
  enqueue := fun _ _ => Appends.focus _ _ _
  release := fun peer =>
    (CausalJournal.CallbackQuiet.release (fun _ => (none : Option Unit))
      (fun _ => rfl) (fun _ => rfl) peer).1

theorem publication_appends (items : List SkbId) (state : PacketState) :
    Appends (TxSource.publish actualOps items state) := by
  unfold TxSource.publish
  repeat' first
    | with_reducible exact actual_appends_ops.step _
    | with_reducible exact actual_appends_ops.access _
    | with_reducible exact actual_appends_ops.event _
    | with_reducible exact actual_appends_ops.release _
    | exact Appends.pure _
    | apply Appends.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

/-- Append preservation follows the original accesses and nested release;
it applies equally when a later source operation stops. -/
theorem actual_appends (pid : PeerId) (items : List SkbId) : Appends (actual pid items) := by
  unfold actual front
  repeat' first
    | with_reducible exact actual_appends_ops.step _
    | with_reducible exact actual_appends_ops.access _
    | with_reducible exact actual_appends_ops.enqueue _ _
    | with_reducible exact publication_appends _ _
    | exact Appends.pure _
    | apply Appends.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split


end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
