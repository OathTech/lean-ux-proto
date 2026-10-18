import Leanux.Proofs.WG.RetirementSecurity.OccurrenceNapi

/-! Native decrypt preparation changes only RX material and publication
bookkeeping. Its key validity mutation does not allocate or consume TX work. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits OccurrenceStack

theorem packet_wire (pkt : RxPacket) : SameView txCryptWire (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head setRxSkb; exact (ReceiveOccurrences.set_rx_wire _ _).wp (· = initial))
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = initial))
    | crypt_wire_step initial

theorem packet_queues (pkt : RxPacket) : SameView handoffTxView (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head setRxSkb; exact (ReceiveOccurrences.skb_queues _).wp (· = initial))
    | crypt_queue_step initial

theorem packet_occurrences (pkt : RxPacket) : Preserves (TxOccurrences locals active) (decryptPacket pkt) :=
  occurrence_passive (packet_wire pkt) (packet_queues pkt)

theorem publish_wire (id : SkbId) (state : PacketState) : SameView txCryptWire (RxWorkers.publishSource id state) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold RxWorkers.publishSource peerGet refcountInc
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,requireNotPending,unsupported]
  repeat' first
    | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head setRxSkb; exact (ReceiveOccurrences.set_rx_wire _ _).wp (· = initial))
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = initial))
    | crypt_wire_step initial

theorem publish_queues (id : SkbId) (state : PacketState) : SameView handoffTxView (RxWorkers.publishSource id state) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold RxWorkers.publishSource peerGet refcountInc
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,requireNotPending,unsupported]
  repeat' first
    | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head setRxSkb; exact (ReceiveOccurrences.skb_queues _).wp (· = initial))
    | crypt_queue_step initial

theorem publish_occurrences (id : SkbId) (state : PacketState) : Preserves (TxOccurrences locals active) (RxWorkers.publishSource id state) :=
  occurrence_passive (publish_wire id state) (publish_queues id state)

theorem prepare_occurrences : Preserves (TxOccurrences locals active) RxWorkers.prepareSource := by
  have packet := packet_occurrences (locals := locals) (active := active)
  have publish := publish_occurrences (locals := locals) (active := active)
  have read (id : SkbId) := ReceiveOccurrences.get_rx id (TxOccurrences locals active)
  have write (id : SkbId) (f : RxPacket → RxPacket) := occurrence_passive (locals := locals) (active := active)
    (ReceiveOccurrences.set_rx_wire id f) (ReceiveOccurrences.skb_queues _)
  have device := ReceiveOccurrences.store (locals := locals) (active := active) getDev_sameWGStore
  have ring (queue : PtrRing SkbId) : Preserves (TxOccurrences locals active)
      (modifyDev fun d => {d with decryptQueue := queue}) :=
    ReceiveOccurrences.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxOccurrences locals active) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [RxWorkers.prepareSource,branch,invariant] using [packet,publish,read,write,device,ring,ambient]

theorem prepare : Preserves (Ready locals active) RxWorkers.prepareSource :=
  RxPollOccurrences.join RxWorkers.prepare_erases RxWorkers.prepare_preserves prepare_occurrences

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt
