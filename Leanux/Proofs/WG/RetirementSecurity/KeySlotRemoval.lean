import Leanux.Proofs.WG.RetirementSecurity.KeySlotWorkers

/-! Actual removal exposes its make-dead exception until the original clear
executes. Both work drains and the final peer payment follow that clear; no
base reference is assumed during this internal interval. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem weaken (before : InvExcept pending w) (more : ∀pid,pid∈pending → pid∈next) : InvExcept next w := by
  intro pid p found outside slots
  exact before pid p found (fun member=>outside (more pid member)) slots

theorem remove_routes (pid : PeerId) : Preserves (InvExcept pending) (removeByPeer pid) :=
  combined_frame (ConfiguredIdentity.removeByPeer_view pid) (removeByPeer_ownership pid)

theorem make_dead_pending (pid : PeerId) (selected : pid∈pending) :
    Preserves (InvExcept pending) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact remove_routes _)
    | (rx_retention_head setPeer
       apply set_saved
       intro outside
       exact False.elim (outside selected))
    | key_slot_work_step

theorem make_dead (pid : PeerId) : Hoare (peerMakeDead pid) (InvExcept pending)
    (fun _=>InvExcept (pid::pending)) := by
  apply hoare_consequence (make_dead_pending pid (pending:=pid::pending) (by simp))
  · intro w before
    exact weaken before (fun _ h=>by simp [h])
  · exact fun _ _ h=>h

theorem prepare_after_dead (pid : PeerId) : Hoare (HolderRemoval.preparation pid)
    (InvExcept (pid::pending)) (fun _=>InvExcept pending) := by
  unfold HolderRemoval.preparation
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment
  apply hoare_bind _ _ (getPeer_preserves pid _)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRemoveNotDead (!p.isDead)) _)
  intro notDead
  apply hoare_bind _ _
    (show Preserves (InvExcept (pid::pending)) (if notDead then unsupported _ else pure ()) from by
      split
      · exact hoare_liftAmbient (AmbientM.unsupported _) _
      · exact preserves_pure ())
  intro _
  apply hoare_bind _ _ (clear_discharge pid)
  intro _
  change Preserves (InvExcept pending) _
  repeat' first
    | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
    | (rx_retention_head timersStop; exact timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | key_slot_work_step

theorem after_dead (pid : PeerId) : Hoare (peerRemoveAfterDead pid)
    (InvExcept (pid::pending)) (fun _=>InvExcept pending) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.afterDead_factor)]
  exact hoare_bind _ _ (prepare_after_dead pid) (fun _=>peer_put (some pid))

theorem remove_peer (word : Option PeerId) : Preserves (InvExcept pending) (peerRemove word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases word with
  | none =>
    change Except.ok (((),w),CounterWindow.record a .peerRemoveNull true)=.ok (((),v),b) at run
    cases run
    exact before
  | some pid =>
    change ((peerMakeDead pid >>= fun _=>peerRemoveAfterDead pid).run w).run
      (CounterWindow.record a .peerRemoveNull false)=.ok (((),v),b) at run
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_bind _ _ (make_dead pid) (fun _=>after_dead pid)) w _ () v b before run

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
