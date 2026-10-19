import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedStaging
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks
import Leanux.Proofs.WG.Queues.RxConsumeProtection

/-! Actual receive completion preserves the same live delayed-effect carrier.
The balanced source lookup/repayment uses its proved peer projection; no
timer or work provenance is inferred from an unrelated completed receive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem endpoint (pid : PeerId) (ep : Endpoint) : StateSafe (liftWGPrefix (setPeerEndpoint pid ep)) := by
  apply state_framed
  · intro initial
    unfold setPeerEndpoint endpointEq
    simp only [WG.andM,branch,requireNotPending]
    repeat' first
      | (rx_retention_head dstCacheReset; exact dstCacheReset_retained _ initial)
      | timer_socket_step initial
  · change SameView SendWorkCauses.queue _
    intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold setPeerEndpoint endpointEq dstCacheReset
    simp only [WG.andM,branch,requireNotPending,hiddenJiffies,getAmbient]
    repeat' first
      | (rx_retention_head modifyDev
         apply (SendWorkCauses.of_workQueueFrame (Queues.WorkQueueFrames.update _ ?_ ?_ ?_)).wp (fun q => q = initial)
         all_goals intro d; rfl)
      | queue_callback_step initial

private theorem lookup_repay (protocol : Nat) (bytes : List UInt8) :
    StateSafe (liftWGPrefix (Queues.RxBorrow.source protocol bytes)) := by
  apply state_framed
  · intro initial
    apply retained_exact
    exact (Queues.RxBorrow.source_frame protocol bytes).of_factor
      (fun obs pid timer => (obs.2 pid).map (fun p => (p.internalId,p.timer timer,p.wheel timer)))
      TimerSlots.view (fun _ => rfl)
  · exact (Queues.RxBorrow.source_frame protocol bytes).of_factor
      (fun obs => (obs.1.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue
      (fun w => by
        simp only [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,QueuedOccurrences.queue,
          Option.map_map,Function.comp_def])

theorem receive_finish (pid : PeerId) (ready : Packets.RxReady) :
    StateSafe (liftWGPrefix (Packets.rxFinish pid ready)) := by
  apply state_native
  intro h
  rw [← Queues.RxCredits.rxFinishSource_eq]
  unfold Queues.RxCredits.rxFinishSource
  apply preserves_bind (native_contract _ (lookup_repay ready.protocol ready.bytes) h)
  intro routed
  apply native_contract
  apply state_framed
  · intro initial
    unfold dishonest updateRxStats
    simp only [branch]
    repeat' timer_socket_step initial
  · change SameView SendWorkCauses.queue _
    intro initial
    change Preserves (fun w => SendWorkCauses.queue w = initial) _
    unfold dishonest updateRxStats
    simp only [branch]
    repeat' first
      | (rx_retention_head modifyDev
         apply (SendWorkCauses.of_workQueueFrame (Queues.WorkQueueFrames.update _ ?_ ?_ ?_)).wp (fun q => q = initial)
         all_goals intro d; rfl)
      | queue_callback_step initial


theorem receive_finish_observed (pid : PeerId) (ready : Packets.RxReady) :
    StateSafe (RetirementSecurity.NestedPeerRelease.rxFinishWith (Driver.nestedOps hooks) pid ready) :=
  observed_native _ _ (CallbackFrames.rx_finish_erases pid ready)
    (CallbackFrames.rx_finish_quiet (fun _ : Event => (none : Option Empty)) (fun _ => rfl) pid ready).1
    (receive_finish pid ready)

theorem receive_tail (pid : PeerId) (packet : RxPacket) (confirmed : Bool) :
    StateSafe (Driver.receiveTailObserved hooks pid packet confirmed) := by
  unfold Driver.receiveTailObserved
  repeat' first
    | (causal_delayed_head Driver.stagingObserved; exact staging _)
    | (causal_delayed_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact prepare_disposal _ _)
    | (causal_delayed_native_head timersHandshakeComplete; exact handshake_complete _ _)
    | (causal_delayed_head RetirementSecurity.NestedPeerRelease.rxFinishWith; exact receive_finish_observed _ _)
    | (causal_delayed_head liftWGPrefix; solve | causal_delayed_native)
    | causal_delayed_step

theorem consume (pid : PeerId) (packet : RxPacket) (ep : Endpoint) :
    StateSafe (Driver.consumeObserved hooks pid packet ep) := by
  unfold Driver.consumeObserved
  exact state_bind (endpoint pid ep) (fun _ => state_bind (confirmation pid packet.keypair)
    (receive_tail pid packet))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
