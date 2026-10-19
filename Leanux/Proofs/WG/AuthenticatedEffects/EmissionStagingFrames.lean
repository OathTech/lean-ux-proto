import Leanux.Proofs.WG.AuthenticatedEffects.EmissionSessionFrames
import Leanux.Proofs.WG.TransmitSecurity.KeepalivePreparation
import Leanux.Proofs.WG.TransmitSecurity.NonceSource

/-! Staging and queued packet creation do not append socket datagrams. These
native sent frames are distinct from packet provenance and send authorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem reserve (slot : KeypairId) : SameView WGWorld.sent (TransmitSecurity.Nonce.reserveNative slot) := by
  sent_frame [TransmitSecurity.Nonce.reserveNative] using [getKeypair_sent_spec,setKeypair_sent_spec]

theorem allocate (packets : List DataPacket) : SameView WGWorld.sent (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec WGWorld.sent (fun sent => sent = initial)
  intro packet
  exact skb_sent_spec (fun sent => sent = initial) _

private theorem cpu (pid : PeerId) : SameView WGWorld.sent (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range',
    show (Std.Legacy.Range.mk 0 0 1 (by decide)).size = 0 from rfl,List.range'_zero,
    List.forIn_nil,pure_bind]
  sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec]

private theorem enqueue_peer (items : List SkbId) (state : PacketState) :
    SameView WGWorld.sent (enqueuePerPeerTx items state) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold enqueuePerPeerTx
  simp only [IndexOwner.peerDeref,IndexOwner.peerWord,peekQueuedUnit,recordQueued,unsupported]
  repeat' first
    | (cookie_source_head cpumaskChooseOnline; exact (cpu _).wp (fun sent => sent = initial))
    | (cookie_source_head peerGet; exact peerGet_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head peerPut; exact peerPut_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head getTxSkb; exact skb_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head setTxSkb; exact skb_sent_spec (fun sent => sent = initial) _)
    | consumer_sent_step initial

private theorem enqueue_both (pid : PeerId) (items : List SkbId) :
    SameView WGWorld.sent (enqueuePerDeviceAndPeer pid items) := by
  sent_frame [enqueuePerDeviceAndPeer,cpumaskNextOnlineFrom,queueDeviceWork]
    using [getPeer_sent_spec,setPeer_sent_spec]
  dsimp only [setTxSkb]
  apply hoare_liftSkb
  intro w d skbs hi hd
  exact hi

theorem create (pid : PeerId) (items : List SkbId) : SameView WGWorld.sent (createData pid items) := by
  intro initial
  change Preserves (fun w : WGWorld => w.sent = initial) _
  unfold createData
  simp only [branch]
  repeat' first
    | (cookie_source_head enqueuePerDeviceAndPeer; exact (enqueue_both _ _).wp (fun sent => sent = initial))
    | (cookie_source_head enqueuePerPeerTx; exact (enqueue_peer _ _).wp (fun sent => sent = initial))
    | (cookie_source_head keypairPut; exact keypair_put_spec (fun sent => sent = initial) _ _)
    | (cookie_source_head peerPut; exact peerPut_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head getTxSkb; exact skb_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head freeTxSkb; exact skb_sent_spec (fun sent => sent = initial) _)
    | (cookie_source_head ForIn.forIn
       apply list_view_spec id (fun w : WGWorld => w.sent = initial)
       intro id state
       exact preserves_bind (skb_sent_spec (fun sent => sent = initial) _) (fun _ => preserves_pure _))
    | consumer_sent_step initial

theorem keepalive (pid : PeerId) :
    SameView WGWorld.sent (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid) := by
  sent_frame [RetirementSecurity.OccurrenceHandshake.keepalivePrepare,hiddenAlloc]
    using [getPeer_sent_spec,setPeer_sent_spec]

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
