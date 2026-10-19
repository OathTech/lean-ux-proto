import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRemoval
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeFrames
import Leanux.Proofs.WG.Queues.HolderDeviceDelete

/-! Native shutdown preserves one exact reference account. Actual work drains
may repay selected holders; no incoming empty-work or staged-empty premise is
introduced, and the mirror's pending-work Stops remain in place. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

private theorem read : Preserves (ExactBoundary cs loans) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b account run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ account

theorem modify_fields (f : Device → Device)
    (same : ∀w : WGWorld, HolderEncrypt.fields {w with dev:=w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (ExactBoundary cs loans) (modifyDev f) := by
  apply hoare_modify
  intro w account
  exact account.fields (same w)

theorem from_work (action : WG.M α)
    (keeps : ∀original, Preserves (RetiredPeer.DuringWork original cs loans) action) :
    Preserves (ExactBoundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨out,_,post⟩ := (hoare_iff_run_ambient _ _ _).mp (keeps holders)
    w a x v b (RetiredPeer.duringWork_initial account) run
  exact ⟨out,post⟩

theorem handshake (pid : PeerId) : Preserves (ExactBoundary cs loans) (handshakeClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  cases x
  obtain ⟨holders,account⟩ := before
  exact ⟨holders,account.handshake_clear run⟩

theorem reset (pid : PeerId) : Preserves (ExactBoundary cs loans) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) (ExactBoundary cs loans))
  intro now
  exact TimerFrames.modify_boundary pid
    (fun p => {p with lastSentHandshake:=now-(REKEY_TIMEOUT+1 : Nat).toInt64*NSEC_PER_SEC64})
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _ _ h=>h) (fun _=>rfl)

theorem socket (new4 new6 : Option Nat) : Preserves (ExactBoundary cs loans) (socketReinit new4 new6) :=
  ExactBoundary.native_fields (NativeFrames.socket (socketReinit_sameSocket new4 new6))

theorem stop : Preserves (ExactBoundary cs loans) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head getDev; exact read)
    | (rx_retention_head purgeStagedPackets; exact TimerCallbacks.purge_boundary _)
    | (rx_retention_head timersStop; exact from_work _ (fun _ => RetiredPeer.timersStop_preserves _))
    | (rx_retention_head handshakeClear; exact handshake _)
    | (rx_retention_head keypairsClear; exact from_work _ (fun _ => RetiredPeer.keypairsClear_preserves _))
    | (rx_retention_head resetLastSentHandshake; exact reset _)
    | (rx_retention_head socketReinit; exact socket _ _)
    | (rx_retention_head modifyDev
       apply modify_fields
       intro w
       unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
       unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
       cases hd : w.dev <;> simp [hd,rxView])
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (ExactBoundary cs loans)
       intro x u
       change Preserves (ExactBoundary cs loans) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (ExactBoundary cs loans))
    | rx_retention_step

theorem down : Preserves (ExactBoundary cs loans) wgDown := by
  unfold wgDown
  apply preserves_bind
  · apply modify_fields
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  · intro _; exact stop

/-- Cursor inactivity is an actual source property alongside the exact
account, not a replacement lower-only holder witness. -/
def Clear (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ExactBoundary cs loans w ∧ activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none

theorem down_clear : Preserves (Clear cs loans) wgDown := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  have post := (hoare_iff_run_ambient _ _ _).mp down w a x v b before.1 run
  have cursors := (hoare_iff_run_ambient _ _ _).mp HolderDeviceDelete.down_clear
    w a x v b ⟨before.1.lower,before.2⟩ run
  exact ⟨post,cursors.2⟩

theorem clear_modify (f : Device → Device)
    (same : ∀w : WGWorld, HolderEncrypt.fields {w with dev:=w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (Clear cs loans) (modifyDev f) := by
  apply hoare_modify
  intro w account
  exact ⟨account.1.fields (same w),account.2⟩

theorem clear_read : Preserves (Clear cs loans) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b account run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ account

theorem clear_socket (new4 new6 : Option Nat) : Preserves (Clear cs loans) (socketReinit new4 new6) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (socketReinit_sameSocket new4 new6) w a x v b run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (socket new4 new6) w a x v b before.1 run,
    (congrArg (fun s : WGOwnedView => activeCursor s.nlSock7) fields).trans before.2.1,
    (congrArg (fun s : WGOwnedView => activeCursor s.nlSock8) fields).trans before.2.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
