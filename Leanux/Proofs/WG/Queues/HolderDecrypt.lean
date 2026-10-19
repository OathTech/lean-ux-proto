import Leanux.Proofs.WG.Queues.HolderNapi
import Leanux.Proofs.WG.Queues.DecryptConcrete

/-! Native decrypt preparation retains durable holder fields while acquiring
its explicit publication loan; the following source put pays precisely it. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDecrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders
open DecryptIteration (Physical Journal)

macro "holder_prepare_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head invariant; unfold invariant)
  | (rx_retention_head unsupported; unfold unsupported)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Frame $initial))
  | (rx_retention_head getRxSkb; unfold getRxSkb)
  | (rx_retention_head setRxSkb; unfold setRxSkb)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     exact hi.trans (by constructor <;> first | (simp [passiveView,sendView,hd]) |
       (intro q xs h; simpa [handoffTxView,hd] using h)))
  | holder_work_step $initial)

theorem peerGet_frame (pid : PeerId) (initial) : Preserves (Frame initial) (peerGet pid) := by
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' holder_prepare_step initial

theorem decryptPacket_frame (pkt : RxPacket) (initial) :
    Preserves (Frame initial) (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' holder_prepare_step initial

theorem publish_frame (id : SkbId) (state : PacketState) (initial) :
    Preserves (Frame initial) (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  repeat' first
    | (rx_retention_head peerGet; exact peerGet_frame _ initial)
    | holder_prepare_step initial

theorem prepare_frame (initial) : Preserves (Frame initial) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_frame _ initial)
    | (rx_retention_head RxWorkers.publishSource; exact publish_frame _ _ initial)
    | holder_prepare_step initial

/-- The publication loan is an additional charged occurrence, which may name
an owner already held elsewhere. It is kept across the real IRQ callback. -/
theorem prepare_normal (hi : Boundary cs loans w.wg) (physical : Physical w)
    (hr : runPrefix Origins.HistoryAdapters.prepare w h = (.ok (result,v),k)) :
    match result with
    | none => Boundary cs loans v.wg
    | some pid => ∃ o : Owner, o.slot = pid ∧ Boundary cs (o :: loans) v.wg := by
  obtain ⟨holders,funded,stable⟩ := hi
  have native := DecryptIteration.native_normal Origins.HistoryAdapters.prepare_erases hr
  have frame := (hoare_iff_run_ambient _ _ _).mp (prepare_frame w.wg)
    w.wg w.ambient result v.wg v.ambient (Frame.refl w.wg) native
  have post := DecryptIteration.prepare_normal ⟨funded.carriers,stable⟩ physical hr
  cases result with
  | none => exact ⟨holders,⟨funded.aligned.frame frame,post.1⟩,post.2⟩
  | some pid =>
    obtain ⟨o,slot,carriers⟩ := post.1
    exact ⟨o,slot,holders,⟨funded.aligned.frame frame,
      WorkReservations.carrier_loans_perm carriers List.perm_middle.symm⟩,post.2⟩

theorem payment_normal (hi : Boundary cs (o :: loans) w.wg)
    (hr : runPrefix (RxHistory.mixed (liftWGObserver (peerPutMixed (some o.slot)))) w h = (.ok ((),v),k)) :
    Boundary cs loans v.wg := by
  obtain ⟨holders,funded,stable⟩ := hi
  have native := DecryptIteration.native_normal
    (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _))) hr
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.peerPut_frame (some o.slot) w.wg)
    w.wg w.ambient () v.wg v.ambient (Frame.refl w.wg) native
  have paid := reservation_payment_stable
    (WorkReservations.carrier_loans_perm funded.carriers List.perm_middle) stable w.ambient v.ambient native
  exact ⟨holders,⟨funded.aligned.frame frame,paid.1⟩,paid.2⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderDecrypt
