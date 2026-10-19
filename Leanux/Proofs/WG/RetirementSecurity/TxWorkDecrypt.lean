import Leanux.Proofs.WG.RetirementSecurity.TxActorNapi

/-! Actual decrypt preparation retains TX service while changing RX material
and publishing its peer's NAPI work. The callback placements are composed with
their concrete actor-preserving contracts in the next product source cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem decrypt_packet_work (pkt : RxPacket) : SameView queued (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w=>queued w=initial))
    | tx_work_step initial

theorem rx_publish_work (skb : SkbId) (state : PacketState) : SameView queued (RxWorkers.publishSource skb state) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold RxWorkers.publishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head peerGet; exact (peer_get _).wp (·=initial))
    | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head setRxSkb; exact (skb_work _).wp (·=initial))
    | tx_work_step initial

theorem service_device (f : Device→Device)
    (peers : ∀d,(f d).peers=d.peers) (packets : ∀d,(f d).txSkbs=d.txSkbs)
    (ring : ∀d,(f d).encryptQueue=d.encryptQueue) (work : ∀d,(f d).txWorkQueue=d.txWorkQueue) :
    Preserves (Obligations crypt tx) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run
  apply before.frame
  · funext pid; simp [Queues.RxCredits.handoffTxView,Option.bind_map,Function.comp_def,peers]
  · funext id; simp [TxDisposition.txPackets,Option.bind_map,Function.comp_def,packets]
  · simp [txCryptItems,Option.map_map,Function.comp_def,ring]
  · simp [queued,Option.map_map,Function.comp_def,work]

theorem decrypt_prepare_service : Preserves (Obligations crypt tx) RxWorkers.prepareSource := by
  let P:=Obligations crypt tx
  have packet (pkt : RxPacket) : Preserves P (decryptPacket pkt) :=
    passive (OccurrenceDecrypt.packet_wire pkt) (OccurrenceDecrypt.packet_queues pkt) (decrypt_packet_work pkt)
  have publish (skb : SkbId) (state : PacketState) : Preserves P (RxWorkers.publishSource skb state) :=
    passive (OccurrenceDecrypt.publish_wire skb state) (OccurrenceDecrypt.publish_queues skb state) (rx_publish_work skb state)
  have read (skb : SkbId) : Preserves P (getRxSkb skb) := ReceiveOccurrences.get_rx skb P
  have write (skb : SkbId) (f : RxPacket→RxPacket) : Preserves P (setRxSkb skb f) :=
    passive (ReceiveOccurrences.set_rx_wire skb f) (ReceiveOccurrences.skb_queues _) (skb_work _)
  have device:Preserves P getDev := service_store getDev_sameWGStore
  have ring (queue : PtrRing SkbId) : Preserves P (modifyDev fun d=>{d with decryptQueue:=queue}) :=
    service_device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Preserves P _
  rxstack_preserves_source [RxWorkers.prepareSource,branch,invariant] using [packet,publish,read,write,device,ring,ambient]

theorem serving_decrypt_prepare : Preserves (Serving locals crypt tx) RxWorkers.prepareSource :=
  serving_join decrypt_prepare_service (TxCovered.join OccurrenceDecrypt.prepare TxCoverageDecrypt.prepare)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
