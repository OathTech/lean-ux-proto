import Leanux.Proofs.WG.AuthenticatedEffects.TimerSocketFrames
import Leanux.Proofs.WG.Lifetimes.TxStaging

/-! Keepalive staging and data submission do not arm timers directly. These
native frames retain timer provenance through nonce/key writes, queueing,
allocation and reference repayment; observed timer arms remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem skb_retained (action : SkbM α) (initial) : Preserves (Retained initial) (liftSkb action) := by
  apply hoare_liftSkb
  intro w d store hi hd
  intro pid t token found
  exact hi pid t token (by simpa only [view,Option.bind_some,hd] using found)

macro "timer_data_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head liftSkb; exact skb_retained _ $initial)
  | (rx_retention_head ForIn.forIn; rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | timer_handshake_step $initial)

theorem keypairGet_retained (id : Option KeypairId) (initial) :
    Preserves (Retained initial) (keypairGet id) := by
  unfold keypairGet refcountIncNotZero
  simp only [branch,branchCmp,invariant,unsupported]
  repeat' timer_data_step initial

private theorem cpu_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp only [branch]
  repeat' timer_data_step initial

private theorem enqueue_device_retained (pid : PeerId) (items : List SkbId) (initial) :
    Preserves (Retained initial) (enqueuePerDeviceAndPeer pid items) := by
  unfold enqueuePerDeviceAndPeer
  simp only [branch,queueDeviceWork,invariant,getDev]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact retained_store (cpumaskNextOnlineFrom_sameStore _) initial)
    | timer_data_step initial

private theorem enqueue_peer_retained (items : List SkbId) (state : PacketState) (initial) :
    Preserves (Retained initial) (enqueuePerPeerTx items state) := by
  unfold enqueuePerPeerTx
  simp only [peekQueuedUnit,recordQueued,invariant,getTxSkb,setTxSkb]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline; exact cpu_retained _ initial)
    | timer_data_step initial

theorem createData_retained (pid : PeerId) (items : List SkbId) (initial) :
    Preserves (Retained initial) (createData pid items) := by
  unfold createData
  simp only [branch,invariant,getTxSkb,freeTxSkb]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue_device_retained _ _ initial)
    | (rx_retention_head enqueuePerPeerTx; exact enqueue_peer_retained _ _ initial)
    | timer_data_step initial

theorem queued_retained (pid : PeerId) (retry : Bool) (initial) :
    Preserves (Retained initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp only [branch,peekQueuedUnit,recordQueued]
  repeat' timer_data_step initial

theorem noKey_retained (pid : PeerId) (packets : List Packet) (kp : Option KeypairId)
    (invalid : Bool) (initial) : Preserves (Retained initial) (stagedOutNokey pid packets kp invalid) := by
  unfold stagedOutNokey
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_retained _ _ initial)
    | timer_data_step initial

private theorem allocate_retained (packets : List DataPacket) (initial) :
    Preserves (Retained initial) (packets.mapM newTxSkb) := by
  apply mapM_view_spec id (Retained initial)
  intro packet
  exact skb_retained (SkbStore.newTx packet) initial

theorem staging_retained (pid : PeerId) (initial) : Preserves (Retained initial) (sendStagedPackets pid) := by
  unfold sendStagedPackets
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head keypairGet; exact keypairGet_retained _ initial)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp (Retained initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_retained _ _ initial)
    | (rx_retention_head List.mapM; exact allocate_retained _ initial)
    | (rx_retention_head createData; exact createData_retained _ _ initial)
    | timer_data_step initial

theorem keepalive_retained (pid : PeerId) (initial) : Preserves (Retained initial) (sendKeepalive pid) := by
  unfold sendKeepalive
  simp only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact staging_retained _ initial)
    | timer_data_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
