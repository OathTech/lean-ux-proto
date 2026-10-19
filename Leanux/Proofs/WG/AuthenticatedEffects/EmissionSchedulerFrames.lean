import Leanux.Proofs.WG.AuthenticatedEffects.EmissionEncryptionFrames

/-! Scheduler selection leaves and copied consistency trials preserve the
actual sent buffer. Trial output is discarded by the original source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity

theorem consistent (a : Activation) : SameView EmissionOuter.Sent (Env.Activation.consistent a) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w b v run
  unfold Env.Activation.consistent at run
  simp only [StateT.run_bind,StateT.run_get,pure_bind] at run
  cases trial : (Env.Activation.run a).run w with
  | ok out =>
    simp only [trial,StateT.run_pure] at run
    cases run
    rfl
  | error stop =>
    simp only [trial] at run
    cases stop <;> cases run <;> rfl

theorem occupancy (a : Activation) : SameView EmissionOuter.Sent (Env.Activation.occupancy a) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    EmissionOuter.wg _ (by sent_frame [] using []) initial
  have peer (pid : PeerId) : Preserves P (monadLift (getPeer pid) : Leanux.M Peer) :=
    EmissionOuter.wg _ (fun sent => getPeer_sent_spec (· = sent) pid) initial
  have ambient {α : Type} (m : AmbientM α) : Preserves P (monadLift m : Leanux.M α) := EmissionOuter.ambient m initial
  routing_tx_source [Env.Activation.occupancy,invariant] using [dev,peer,ambient]

theorem refills : SameView EmissionOuter.Sent Env.Activation.refills := by
  unfold Env.Activation.refills
  apply (EmissionOuter.wg getDev (by sent_frame [] using [])).bind
  intro device
  exact (EmissionOuter.ambient AmbientM.recordsLeft).bind (fun _ => SameView.pure _ _)

theorem pending_device (worker : Worker) (queued : Bool) :
    SameView EmissionOuter.Sent (Env.pendingDevice worker queued) := by
  unfold Env.pendingDevice
  exact (EmissionOuter.ambient (get : AmbientM Ambient)).bind (fun _ => SameView.pure _ _)

theorem has_work (a : Activation) : SameView EmissionOuter.Sent (Env.Activation.hasWork a) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    EmissionOuter.wg _ (by sent_frame [] using []) initial
  have peer (pid : PeerId) : Preserves P (monadLift (getPeer pid) : Leanux.M Peer) :=
    EmissionOuter.wg _ (fun sent => getPeer_sent_spec (· = sent) pid) initial
  have packet (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    EmissionOuter.wg _ (fun sent => skb_sent_spec (· = sent) _) initial
  have ambient {α : Type} (m : AmbientM α) : Preserves P (monadLift m : Leanux.M α) := EmissionOuter.ambient m initial
  routing_tx_source [Env.Activation.hasWork,invariant] using [dev,peer,packet,ambient]

theorem pending_napi (next : Option Nat) : SameView EmissionOuter.Sent (Lifetimes.pendingNapi next) := by
  unfold Lifetimes.pendingNapi
  exact (EmissionOuter.wg getDev (by sent_frame [] using [])).bind (fun _ => SameView.pure _ _)

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
