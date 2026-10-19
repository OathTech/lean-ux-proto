import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleCuts
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceRemoval

/-! Positivity is transported independently of the exact reference budget,
then joined at the same actual native preparation cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders HolderDeviceCreate
open HandshakeSecurity
set_option maxHeartbeats 600000

private theorem positive_stop : Preserves PeerReference.Inv wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact PeerReference.purge _)
    | (rx_retention_head timersStop; exact PeerReference.stop_timers _)
    | (rx_retention_head handshakeClear; exact PeerReference.clear _)
    | (rx_retention_head keypairsClear; exact PeerReference.clear_keys _)
    | (rx_retention_head resetLastSentHandshake; exact PeerReference.reset_sent _)
    | (rx_retention_head socketReinit; exact PeerReference.socket (socketReinit_sameSocket _ _))
    | peer_reference_traffic_step

theorem positive_down : Preserves PeerReference.Inv wgDown := by
  unfold wgDown
  apply preserves_bind
  · apply PeerReference.modify_device
    intro d
    rfl
  intro _
  exact positive_stop

theorem positive_prepare : Preserves PeerReference.Inv RetirementSecurity.TxWork.Destruct.prepare := by
  unfold RetirementSecurity.TxWork.Destruct.prepare
  apply preserves_bind
  · apply PeerReference.modify_device
    intro d
    rfl
  intro _
  exact preserves_bind (PeerReference.socket (socketReinit_sameSocket none none))
    (fun _=>PeerReference.remove_all)

private theorem positive_lift {action : WG.M α} (rule : Preserves PeerReference.Inv action) :
    Preserves (fun w : World=>PeerReference.Inv w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  exact (hoare_iff_run_ambient _ _ _).mp rule w.wg w.ambient x v.wg v.ambient before
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v x run)

private theorem positive_product (action : Leanux.M α) (frame : SameProductStore action) :
    Preserves (fun w : World=>PeerReference.Inv w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  have same := congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v run)
  have counts := congrArg (fun s : WGStoreView=>fun pid : PeerId=>(s.dev.bind fun d=>d.peers[pid]?).map Peer.refcount) same
  change PeerReference.Positive (PeerReference.view v.wg)
  rw [show PeerReference.view v.wg=PeerReference.view w.wg from counts]
  exact before

private theorem positive_routing (action : Net.M α) :
    Preserves (fun w : World=>PeerReference.Inv w.wg)
      (MonadLift.monadLift (MonadLift.monadLift action : WG.M α) : Leanux.M α) :=
  positive_product _ (liftWG_sameProductStore _ (liftRouting_sameWGStore action))

private abbrev positiveNotifyDown : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
private abbrev positiveNotifyUnregister : Leanux.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister

private theorem positive_notify_down : Preserves (fun w : World=>PeerReference.Inv w.wg) positiveNotifyDown := by
  unfold positiveNotifyDown
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
  unfold modifyRouting
  repeat' first
    | (allocation_release_lift_from WG.M; exact positive_routing _)
    | (allocation_release_lift_from Net.M; exact positive_routing _)
    | rx_retention_step

private theorem positive_notify_unregister : Preserves (fun w : World=>PeerReference.Inv w.wg) positiveNotifyUnregister := by
  unfold positiveNotifyUnregister
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister
  unfold modifyRouting
  apply preserves_bind (positive_product _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store))
  intro _
  repeat' first
    | (allocation_release_lift_from WG.M; exact positive_routing _)
    | (allocation_release_lift_from Net.M; exact positive_routing _)
    | rx_retention_step

theorem positive_delete_prefix : Preserves (fun w : World=>PeerReference.Inv w.wg) deletePrefix := by
  let P := fun w : World=>PeerReference.Inv w.wg
  unfold deletePrefix
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | exact positive_notify_down
    | exact positive_notify_unregister
    | (allocation_release_lift_from WG.M; first
        | exact positive_lift positive_down
        | exact positive_lift (PeerReference.store getDev_sameWGStore)
        | exact positive_lift (PeerReference.store mayHaveSlept_sameWGStore))
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ P (fun _ _ h=>h))
    | rx_retention_step

/-- One actual deletion execution supplies both exact budget and positive
resident counts at its prepared destructor guard. Neither property is
obtained by choosing a different history or native entry state. -/
theorem delete_positive_cut (before : ExactBoundary cs [] w.wg)
    (physical : OptionalPhysical w.wg) (positive : PeerReference.Inv w.wg)
    (live : w.wg.dev.isSome=true) (run : Env.wgDelete.run w=.ok (result,v)) :
    cs=[] ∧ result=0 ∧ HolderDeviceDelete.guards.run w=.ok ((),w) ∧
    ∃u g c,deletePrefix.run w=.ok ((),u) ∧ Clear [] [] u.wg ∧
      (RetirementSecurity.TxWork.Destruct.prepare.run u.wg).run u.ambient=.ok (((),g),c) ∧
      EmptyBase [] [] g ∧ PeerReference.Inv g ∧
      (checkedTail.run g).run c=.ok (((),v.wg),v.ambient) := by
  obtain ⟨empty,result,guard,u,g,c,frontRun,atDrop,prepared,account,tail⟩ :=
    delete_live_cut before physical live run
  have atDropPositive := (hoare_iff_run _ _ _).mp positive_delete_prefix w () u positive frontRun
  exact ⟨empty,result,guard,u,g,c,frontRun,atDrop,prepared,account,
    (hoare_iff_run_ambient _ _ _).mp positive_prepare u.wg u.ambient () g c atDropPositive prepared,tail⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
