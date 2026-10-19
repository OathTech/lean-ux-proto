import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastIngressFrames

/-! The full original ingress consumes the RX allocation frame and preserves
historical TX exclusion through admission, refusal and reference payments. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Ingress
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

macro "encryption_past_ingress_step" : tactic => `(tactic| first
  | (allocation_release_head getRxSkb; exact ready_get_rx _)
  | (allocation_release_head freeRxSkb; exact ready_free_rx _)
  | (allocation_release_head queueDeviceWork; unfold queueDeviceWork)
  | (allocation_release_head setRxSkb; exact ready_set_rx _ _)
  | (allocation_release_head indexLookup; exact ready_index_lookup _ _)
  | (allocation_release_head newRxSkb; exact ready_allocator (.rx _))
  | (allocation_release_head peerGet; exact ready_frame (LiveFrontier.peer_get _) (peer_get _))
  | (allocation_release_head peerPut; exact ready_frame (LiveFrontier.peer_put _) (peer_put _))
  | (allocation_release_head keypairGet; exact ready_get_key _)
  | (allocation_release_head keypairPut; exact ready_frame (LiveFrontier.key_put _ _) (key_put _ _))
  | (allocation_release_head keypairGetNull; unfold keypairGetNull)
  | (allocation_release_head branch; unfold branch)
  | (allocation_release_head cpumaskNextOnlineFrom
     exact ready_store (cpumaskNextOnlineFrom_sameStore _))
  | encryption_past_receive_step)

theorem enqueue (id : SkbId) : Preserves (Ready past active) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_ingress_step

/-- The source's admission fallback has a literal pure IRQ callback. -/
theorem publish (id : SkbId) (state : PacketState) :
    Preserves (Ready past active) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [liftM,monadLift_self,pure_bind,invariant]
  repeat' encryption_past_ingress_step

theorem consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Ready past active) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head enqueuePerDeviceAndPeerRx; exact enqueue _)
    | (allocation_release_head enqueuePerPeerRx; exact publish _ _)
    | encryption_past_ingress_step

theorem packet (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready past active) (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Ready past active))
    | (allocation_release_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Ready past active))
    | (allocation_release_head consumeData; exact consume _ _ _)
    | encryption_past_ingress_step

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves (Ready past active) (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head packetReceive; exact packet _ _)
    | encryption_past_ingress_step

/-- The same existing lifetime observer carries Ready on normal return. -/
theorem receive_observed (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  Napi.observed
    _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases (wgReceivePrefix_erases msg src)))
    (PublicationPoll.native_product (Ready past active) _ (receive msg src))

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Ingress
