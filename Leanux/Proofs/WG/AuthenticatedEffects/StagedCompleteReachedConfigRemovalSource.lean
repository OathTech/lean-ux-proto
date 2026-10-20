import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteSource

/-! Individual peer removal follows its original guard, make-dead operation
and after-dead continuation. The latter already exposes drains and repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver

def removeNonNull (peer : Option PeerId) : PrefixM Event Unit := match peer with
  | none=>liftPrefix (liftWG (invariant "unreachable"))
  | some pid=>do
      liftPrefix (liftWG (peerMakeDead pid))
      liftWGObserver (StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix
        (sendDrainObserved hooks) hooks.peerRelease pid)

def removeBody (peer : Option PeerId) : PrefixM Event Unit := do
  if ← liftPrefix (liftWG (branch .peerRemoveNull peer.isNone)) then pure () else removeNonNull peer

theorem remove_factor (peer : Option PeerId) :
    liftWGObserver (removeObserved hooks peer)=removeBody peer := by
  unfold removeObserved StagedDisposal.Lifecycle.removeWith Configuration.peerRemoveWith removeBody removeNonNull
  simp only [liftWGObserver_bind,liftWGObserver_lift]
  congr 1
  funext absent
  cases absent with
  | false=>
      cases peer with
      | none=>rfl
      | some pid=>exact liftWGObserver_bind _ _
  | true=>exact liftWGObserver_pure ()

noncomputable def removeNonNullShape (peer : Option PeerId) : Lifecycle.Points.Shape (removeNonNull peer) := by
  cases peer with
  | none=>exact .native (.quiet _ (Lifecycle.Points.wg_frame _ (by entry_lifecycle_native)))
  | some pid=>
      exact .bind (.native (.quiet _ (Lifecycle.Points.wg_frame _ (RoutingFrames.make_dead pid))))
        (fun _=>Lifecycle.Points.afterDeadShape pid)

noncomputable def removeBodyShape (peer : Option PeerId) : Lifecycle.Points.Shape (removeBody peer) := by
  apply Lifecycle.Points.Shape.bind
    (.native (.quiet _ (Lifecycle.Points.wg_frame _ (TimerFrames.branch_frame _ _))))
  intro absent
  cases absent with
  | false=>exact removeNonNullShape peer
  | true=>exact .pure ()

noncomputable def removeShape (peer : Option PeerId) :
    Lifecycle.Points.Shape (liftWGObserver (removeObserved hooks peer)) :=
  (congrArg Lifecycle.Points.Shape (remove_factor peer)).mpr (removeBodyShape peer)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
