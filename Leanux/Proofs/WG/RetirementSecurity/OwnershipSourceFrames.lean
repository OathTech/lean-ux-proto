import Leanux.Proofs.WG.RetirementSecurity.OwnershipFrames
import Leanux.Proofs.WG.Queues.SendWork

/-! Native timer and socket bookkeeping frames on actual key holders. Saved
peer reads retain the ownership fields needed by later source setters; no
whole-world invariant is smuggled through these bookkeeping paths. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private theorem timer_ownership (p : Peer) (timer : PeerTimer) (value : Option UInt64) :
    peerOwnership (p.setTimer timer value) = peerOwnership p := by cases timer <;> rfl
private theorem wheel_ownership (p : Peer) (timer : PeerTimer) (value : Option WheelEntry) :
    peerOwnership (p.setWheel timer value) = peerOwnership p := by cases timer <;> rfl

private theorem ownership_read_bind (initial) {α : Type} (pid : PeerId) (f : Peer → WG.M α)
    (next : ∀ p, initial.2.2.1 pid = some (peerOwnership p) →
      Preserves (fun w => ownershipPointView w = initial) (f p)) :
    Preserves (fun w => ownershipPointView w = initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (ownership_getPeer (fun s => s = initial) pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have saved := before.2
  change (ownershipPointView w).2.2.1 pid = some (peerOwnership p) at saved
  rw [before.1] at saved
  exact (hoare_iff_run_ambient _ _ _).mp (next p saved) w a result v b before.1 run

private theorem ownership_set_saved (initial) (pid : PeerId) (p : Peer)
    (saved : initial.2.2.1 pid = some (peerOwnership p)) :
    Preserves (fun w => ownershipPointView w = initial) (setPeer pid p) := by
  apply hoare_consequence (ownership_setPeer (fun s => s = initial) pid p)
  · intro w before
    refine ⟨before,?_⟩
    change (ownershipPointView w).2.2.1 pid = some (peerOwnership p)
    rw [before]
    exact saved
  · exact fun _ _ h => h

private theorem ownership_modify_spec (initial) (f : Device → Device)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (peers : ∀ d, (f d).peers = d.peers)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    Preserves (fun w => ownershipPointView w = initial) (modifyDev f) :=
  (ownership_modifyDev f keys peers tx rx).wp (fun s => s = initial)

macro "ownership_source_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (env_bind_head getPeer; apply ownership_read_bind $initial; intro p saved)
  | (rx_retention_head setPeer; apply ownership_set_saved $initial
     first | assumption | (simp only [timer_ownership,wheel_ownership]; assumption))
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev
     exact (ownershipPoints_kernel _ getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (KeyTimes.getKeypair_return _ w v k a b run).1 ▸ before)
  | (rx_retention_head getTxSkb
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (Packets.getTxSkb_current _ w v k a b run).1 ▸ before)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head liftRouting; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head getRouting
     exact hoare_liftRouting ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
       _ (fun _ _ h => h))
  | (rx_retention_head get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply ownership_modify_spec $initial
     all_goals intro d; rfl)
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head modify; apply hoare_modify; intro w before; exact before)
  | rx_retention_step)

theorem placeOnWheel_ownership (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView ownershipPointView (placeOnWheel pid timer expires clk unit) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [peekHiddenSite,hidden,invariant]
  repeat' ownership_source_step initial

theorem armTimer_ownership (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView ownershipPointView (armTimer pid timer delay jc) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | (rx_retention_head placeOnWheel
       exact (placeOnWheel_ownership _ _ _ _ _).wp (fun s => s = initial))
    | ownership_source_step initial

theorem delTimer_ownership (pid : PeerId) (timer : PeerTimer) :
    SameView ownershipPointView (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold delTimer
  repeat' ownership_source_step initial

theorem modPeerTimerGuard_ownership (pid : PeerId) :
    SameView ownershipPointView (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp only [branch]
  repeat' ownership_source_step initial

theorem modPeerTimer_ownership (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView ownershipPointView (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor
    ownershipPointView ownershipPointView (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_ownership pid)
  intro ready
  split
  · exact (armTimer_ownership pid timer delay jc).bind (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersTraversal_ownership (pid : PeerId) :
    SameView ownershipPointView (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersTraversal
  simp only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer
       exact (modPeerTimer_ownership _ _ _ _).wp (fun s => s = initial))
    | ownership_source_step initial
  all_goals exact ((modPeerTimer_ownership _ _ _ _).map (fun _ => ())).wp (fun s => s = initial)

theorem timersDataSent_ownership (pid : PeerId) :
    SameView ownershipPointView (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersDataSent
  simp only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => ownershipPointView w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => ownershipPointView w = initial))
    | (rx_retention_head modPeerTimerGuard
       exact (modPeerTimerGuard_ownership _).wp (fun s => s = initial))
    | (rx_retention_head armTimer
       exact (armTimer_ownership _ _ _ _).wp (fun s => s = initial))
    | ownership_source_step initial

end Leanux.Proofs.WG.RetirementSecurity
