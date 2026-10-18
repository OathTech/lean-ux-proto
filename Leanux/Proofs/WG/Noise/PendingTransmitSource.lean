import Leanux.Proofs.WG.Noise.PendingTransmitFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTransmit
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues
open PendingReception PendingSession

theorem send4_native (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (send4 e (some pid) bytes ds exactRx) :=
  native_view _ (ConfiguredHandshake.send4_view _ _ _ _ _)
    (CurrentSlots.TxSource.send4_preserves _ _ _ _ _)
    (PendingTickets.send4_cached_frame pid e bytes ds exactRx) seen

theorem send6_native (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (send6 e (some pid) bytes ds exactRx) :=
  native_view _ (ConfiguredHandshake.send6_view _ _ _ _ _)
    (CurrentSlots.TxSource.send6_preserves _ _ _ _ _)
    (PendingTickets.send6_cached_frame pid e bytes ds exactRx) seen

theorem sendSkb_native (pid : PeerId) (bytes : List UInt8) (ds : Nat) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (sendSkbToPeer pid bytes ds) := by
  have count (ret : Bool) : Preserves (fun w => NativeInv w seen) (do
      let p ← getPeer pid
      setPeer pid {p with txBytes := p.txBytes + bytes.length}
      pure ret) := by
    simpa only [bind_assoc] using
      preserves_bind (native_update pid (fun p => {p with txBytes := p.txBytes + bytes.length})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) seen)
        (fun _ => (preserves_pure ret : Preserves (fun w => NativeInv w seen) (pure ret : WG.M Bool)))
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | env_operation_fact count
    | (rx_retention_head send4; exact send4_native _ _ _ _ _ seen)
    | (rx_retention_head send6; exact send6_native _ _ _ _ _ seen)
    | pending_native_step seen

theorem dataSent_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (timersDataSent pid) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.dataSent_view) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTransmit.«0».Leanux.Proofs.WG.CurrentSlots.TxSource.dataSent_preserves) pid)
    (PendingTickets.timersDataSent_frame pid) seen

theorem fresh_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact PendingTimers.queued_native _ _ seen)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _).wp (fun w => NativeInv w seen))
    | (rx_retention_head getKeypair
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient k v after hi run
       exact (KeyTimes.getKeypair_return _ w v k ambient after run).1 ▸ hi)
    | pending_native_step seen

theorem completion_native (pid : PeerId) (item : List SkbId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (createDataDone pid item) := by
  rw [← TimerDiscipline.dataDoneSource_eq]
  unfold TimerDiscipline.dataDoneSource TimerDiscipline.dataDoneStep TimerDiscipline.dataDoneFinish WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact traversal _ seen)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _ seen)
    | (rx_retention_head sendSkbToPeer; exact sendSkb_native _ _ _ seen)
    | (rx_retention_head timersDataSent; exact dataSent_native _ seen)
    | (rx_retention_head keepKeyFresh; exact fresh_native _ seen)
    | (allocation_release_lift_from SkbM; exact keeps_packet _ seen)
    | (rx_retention_head getTxSkb; exact keeps_packet (SkbStore.getTx _) seen)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => NativeInv w seen)
       intro x acc
       change Preserves (fun w => NativeInv w seen) _)
    | pending_native_step seen

end Leanux.Proofs.WG.Noise.PendingTransmit

namespace Leanux.Proofs.WG.Noise.PendingTransmit
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Queues
open PendingReception PendingSession

theorem step_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  unfold TxDisposition.stepSource TxDisposition.bodySource TxDisposition.disposeSource WG.andM
  simp (config := {zeta := false}) only [getPeer_twice,branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact completion_native _ _ seen)
    | (rx_retention_head keypairPut; exact keypair_keeps _ _ seen)
    | (rx_retention_head peerPut; exact peer_keeps _ seen)
    | (rx_retention_head PrevQueue.peek
       exact PendingReception.native_store _ (prevQueuePeek_sameWGStore _) seen)
    | (allocation_release_lift_from SkbM; exact keeps_packet _ seen)
    | (rx_retention_head getTxSkb; exact keeps_packet (SkbStore.getTx _) seen)
    | (rx_retention_head freeTxSkb; exact keeps_packet (SkbStore.freeTx _) seen)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => NativeInv w seen)
       intro x acc
       change Preserves (fun w => NativeInv w seen) _)
    | pending_native_step seen

theorem iteration_native (pid : PeerId) (need : Leanux.M Bool) (seen : List Nat)
    (next : Preserves (fun w : World => NativeInv w.wg seen) need) :
    Preserves (fun w : World => NativeInv w.wg seen) (txIter pid need) := by
  let P := fun w : World => NativeInv w.wg seen
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    native_product (txStep pid) (step_native pid) seen
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,next,ambient]

theorem observed (pid : PeerId) :
    PrefixPreserves StateInv HistorySafe
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) := by
  apply mixed_observed _ _ (txIterPrefix_erases pid (erasesPrefix_lift _))
  intro seen
  apply iteration_native pid _ seen
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact PendingSession.native_store w.wg v.wg seen
    (congrArg (fun s : ProductStore43 => s.2.2.2)
      ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel .txWorker) w result v run)) hi

end Leanux.Proofs.WG.Noise.PendingTransmit
