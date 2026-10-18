import Leanux.Proofs.WG.AuthenticatedEffects.DecryptEffects
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! The native decrypt worker's own preparation and release cannot transmit.
Its two softirq cuts and IRQ callback remain explicit: they may process other
previously authenticated packets, so a whole-driver proof must trace them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Queues
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem skb_sent_spec (P : List SentDatagram → Prop) {α : Type} (action : WG.SkbM α) :
    Preserves (fun w => P w.sent) (WG.liftSkb action) := by
  apply hoare_liftSkb
  intro w d store hi hd
  exact hi

theorem getRxSkb_sent_spec (P : List SentDatagram → Prop) (id : SkbId) :
    Preserves (fun w => P w.sent) (getRxSkb id) := skb_sent_spec P _
theorem setRxSkb_sent_spec (P : List SentDatagram → Prop) (id : SkbId) (f : RxPacket → RxPacket) :
    Preserves (fun w => P w.sent) (setRxSkb id f) := skb_sent_spec P _

theorem peerGet_sent (pid : PeerId) : SameView WGWorld.sent (peerGet pid) := by
  sent_frame [peerGet,requireNotPending,refcountInc] using [getPeer_sent_spec,setPeer_sent_spec]
theorem peerGet_sent_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (peerGet pid) := (peerGet_sent pid).wp P

theorem decryptPacket_sent (pkt : RxPacket) : SameView WGWorld.sent (decryptPacket pkt) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact (decryptPacket_peer_and_sent pkt result w v a b run).2
theorem decryptPacket_sent_spec (P : List SentDatagram → Prop) (pkt : RxPacket) :
    Preserves (fun w => P w.sent) (decryptPacket pkt) := (decryptPacket_sent pkt).wp P

theorem publishSource_sent (id : SkbId) (state : PacketState) :
    SameView WGWorld.sent (RxWorkers.publishSource id state) := by
  sent_frame [RxWorkers.publishSource,IndexOwner.peerDeref,IndexOwner.peerWord]
    using [getRxSkb_sent_spec,setRxSkb_sent_spec,getPeer_sent_spec,setPeer_sent_spec,
      getKeypair_sent_spec,peerGet_sent_spec]
theorem publishSource_sent_spec (P : List SentDatagram → Prop) (id : SkbId) (state : PacketState) :
    Preserves (fun w => P w.sent) (RxWorkers.publishSource id state) :=
  (publishSource_sent id state).wp P

theorem decryptPrepare_sent : SameView WGWorld.sent RxWorkers.prepareSource := by
  sent_frame [RxWorkers.prepareSource]
    using [getRxSkb_sent_spec,setRxSkb_sent_spec,decryptPacket_sent_spec,publishSource_sent_spec]

theorem decryptStep_sent_of_callbacks (softirq irq : Leanux.M Unit)
    (softirqFrame : SameView (fun w : World => w.wg.sent) softirq)
    (irqFrame : SameView (fun w : World => w.wg.sent) irq) :
    SameView (fun w : World => w.wg.sent) (decryptStep softirq irq) := by
  intro initial
  change Preserves (fun w : World => w.wg.sent = initial) _
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind (softirqFrame initial)
  intro doneUnit
  apply preserves_bind (Leanux.Proofs.WG.PublicationPoll.native_product _ _ (decryptPrepare_sent initial))
  intro prepared
  cases prepared with
  | none => exact preserves_pure false
  | some pid =>
    apply preserves_bind (irqFrame initial)
    intro doneIrq
    apply preserves_bind (Leanux.Proofs.WG.PublicationPoll.native_product _ _ (peerPut_sent (some pid) initial))
    intro paid
    exact preserves_bind (softirqFrame initial) (fun _ => preserves_pure true)

end Leanux.Proofs.WG.AuthenticatedEffects
