import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedLifecycle

/-! Native UDP admission allocates and queues receive packets without inventing
timer arms or handshake-send work. Authentication and later response effects
remain in the separately observed workers and poll. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem lookup_index (kinds : List IndexKind) (index : Nat) :
    StateSafe (liftWGPrefix (indexLookup kinds index)) := by
  apply state_framed _ (indexLookup_retained kinds index)
  exact (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.SendQueueReceiverFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses.holder_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.lookup_frame) kinds index)

private theorem enqueue_device_rx (skb : SkbId) : StateSafe (liftWGPrefix (enqueuePerDeviceAndPeerRx skb)) := by
  apply state_framed
  · intro initial
    unfold enqueuePerDeviceAndPeerRx getRxSkb setRxSkb
    simp only [branch,queueDeviceWork]
    repeat' first
      | (rx_retention_head cpumaskNextOnlineFrom; exact retained_store (cpumaskNextOnlineFrom_sameStore _) initial)
      | timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold enqueuePerDeviceAndPeerRx getRxSkb setRxSkb
    simp only [branch,queueDeviceWork]
    repeat' first
      | (rx_retention_head cpumaskNextOnlineFrom; exact (WorkQueueFrames.store (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
      | send_work_frame_step initial

private theorem enqueue_peer_rx (skb : SkbId) (state : PacketState) :
    StateSafe (liftWGPrefix (enqueuePerPeerRx (pure ()) skb state : WG.M Unit)) := by
  apply state_framed
  · intro initial
    unfold enqueuePerPeerRx getRxSkb setRxSkb
    simp only [invariant,monadLift_self]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold enqueuePerPeerRx getRxSkb setRxSkb
    simp only [invariant,monadLift_self]
    repeat' send_work_frame_step initial

theorem consume_data (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StateSafe (liftWGPrefix (consumeData msg src ds)) := by
  apply state_native
  intro h
  unfold consumeData WG.orM
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact native_contract _ (lookup_index _ _) h)
    | (rx_retention_head keypairGet; exact native_contract _
        (state_framed _ (keypairGet_retained _) (SendWorkCauses.key_get_frame _)) h)
    | (rx_retention_head keypairGetNull; exact native_contract _ (native_store _ keypairGetNull_sameStore) h)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact native_contract _ (enqueue_device_rx _) h)
    | (rx_retention_head enqueuePerPeerRx; exact native_contract _ (enqueue_peer_rx _ _) h)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact native_contract _ (state_framed _ (skb_retained _) (SendWorkCauses.skb_frame _)) h)
    | (rx_retention_head freeRxSkb; unfold freeRxSkb; exact native_contract _ (state_framed _ (skb_retained _) (SendWorkCauses.skb_frame _)) h)
    | (rx_retention_head getPeer; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head peerPut; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head keypairPut; exact native_contract _ (by causal_delayed_native) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

private theorem next_cpu : StateSafe (liftWGPrefix cpumaskNextOnline) := by
  unfold cpumaskNextOnline
  causal_delayed_native

theorem packet_receive (msg : List UInt8) (src : SkbSource) : StateSafe (liftWGPrefix (WG.packetReceive msg src)) := by
  apply state_native
  intro h
  unfold WG.packetReceive
  simp only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Inv h))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Inv h))
    | (rx_retention_head consumeData; exact native_contract _ (consume_data _ _ _) h)
    | (rx_retention_head cpumaskNextOnline; exact native_contract _ next_cpu h)
    | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem udp_receive (msg : List UInt8) (src : SkbSource) : StateSafe (liftWGPrefix (wgReceive msg src)) := by
  apply state_native
  intro h
  unfold wgReceive
  simp only [branch,unsupported]
  repeat' first
    | (rx_retention_head WG.packetReceive; exact native_contract _ (packet_receive _ _) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
