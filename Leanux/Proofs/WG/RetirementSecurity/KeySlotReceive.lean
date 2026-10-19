import Leanux.Proofs.WG.RetirementSecurity.KeySlotHandshake

/-! Native receive admission retains live published slots through actual
index/key/peer acquisition and refusal cleanup. RX packet storage and device
ring aliases are separate from the peer liveness projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

macro "key_slot_rx_step" : tactic => `(tactic| first
  | (rx_retention_head getRxSkb; unfold getRxSkb)
  | (rx_retention_head setRxSkb; unfold setRxSkb)
  | (rx_retention_head newRxSkb; unfold newRxSkb)
  | (rx_retention_head freeRxSkb; unfold freeRxSkb)
  | key_slot_tx_step)

theorem enqueue_rx (id : SkbId) : Preserves (InvExcept pending) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta:=false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom; exact store (cpumaskNextOnlineFrom_sameStore _))
    | key_slot_rx_step

theorem publication_middle (pid : PeerId) (id : SkbId) (state : PacketState) :
    Preserves (InvExcept pending) (publicationMiddle pid id state) := by
  unfold publicationMiddle
  simp only [invariant]
  repeat' key_slot_rx_step

theorem publish_rx (id : SkbId) (state : PacketState) :
    Preserves (InvExcept pending) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [publication_factor]
  apply preserves_bind (ReceiveOccurrences.get_rx id _)
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair packet.keypair) _)
  intro pid
  apply preserves_bind (peer_get pid)
  intro _
  apply preserves_bind (publication_middle pid id state)
  intro _
  exact peer_put (some pid)

theorem consume_data (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (InvExcept pending) (consumeData msg src ds) := by
  unfold consumeData WG.orM keypairGetNull
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup _ _)
    | (rx_retention_head keypairGet; exact key_get _)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueue_rx _)
    | (rx_retention_head enqueuePerPeerRx; exact publish_rx _ _)
    | key_slot_rx_step

theorem cpu_next : Preserves (InvExcept pending) cpumaskNextOnline := by
  unfold cpumaskNextOnline
  simp only [branch]
  repeat' key_slot_rx_step

theorem packet_receive (msg : List UInt8) (src : SkbSource) :
    Preserves (InvExcept pending) (packetReceive msg src) := by
  unfold packetReceive queueDeviceWork
  simp (config := {zeta:=false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (InvExcept pending))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (InvExcept pending))
    | (rx_retention_head consumeData; exact consume_data _ _ _)
    | (rx_retention_head cpumaskNextOnline; exact cpu_next)
    | key_slot_rx_step

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (InvExcept pending) (wgReceive msg src) := by
  unfold wgReceive
  simp only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact packet_receive _ _)
    | key_slot_rx_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
