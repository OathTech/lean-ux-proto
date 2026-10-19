import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastFrames

/-! Native leaf frames for the historical-encryption projection. Changes to
peer/key state and packet contents do not alter the allocation epoch/frontier
or the live encryption ring. Packet allocation and ring admission are separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem modify_fields (f : Device → Device) (epoch : ∀d,(f d).ifindex=d.ifindex)
    (frontier : ∀d,(f d).nextSkb=d.nextSkb) (ring : ∀d,(f d).encryptQueue=d.encryptQueue) :
    SameView view (modifyDev f) := by
  intro initial
  apply hoare_modify
  intro w before
  simpa only [view,Option.map_map,Function.comp_def,epoch,frontier,ring] using before

theorem read_key (id : KeypairId) : SameView view (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b run
  exact congrArg view (KeyTimes.getKeypair_return id w v k a b run).1

theorem key_put (id : Option KeypairId) (now : Bool) : SameView view (keypairPut id now) :=
  parts ((keypairPut_rest id now).factor (fun s => s.2.2)) (TxRing.keypairPut_frame id now)

private theorem skb_ring (action : SkbM α) : SameView TxRing.nativeCell (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  simpa only [TxRing.nativeCell,device,Option.map_some] using before

theorem free_packet (id : SkbId) : SameView view (freeTxSkb id) := by
  apply parts
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact (freeTxSkb_retention id w v a b run).metadata
  · exact skb_ring _

theorem free_rx (id : SkbId) : SameView view (freeRxSkb id) := by
  apply parts
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact (freeRxSkb_retention id w v a b run).metadata
  · exact skb_ring _

theorem read_rx (id : SkbId) : SameView view (getRxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a packet v b run
  exact congrArg view (Packets.getRxSkb_current id w v packet a b run).1

theorem set_rx (id : SkbId) (f : RxPacket → RxPacket) : SameView view (setRxSkb id f) :=
  parts (setRxSkb_metadata id f) (skb_ring _)

theorem index (action : IndexM α) : SameView view (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table before device
  simpa only [view,device,Option.map_some] using before

macro "encryption_past_passive " initial:term : tactic => `(tactic| first
  | (rx_retention_head getKeypair; exact (read_key _).wp (· = $initial))
  | (rx_retention_head keypairPut; exact (key_put _ _).wp (· = $initial))
  | (rx_retention_head getRxSkb; exact (read_rx _).wp (· = $initial))
  | (rx_retention_head setRxSkb; exact (set_rx _ _).wp (· = $initial))
  | (rx_retention_head freeRxSkb; exact (free_rx _).wp (· = $initial))
  | (rx_retention_head freeTxSkb; exact (free_packet _).wp (· = $initial))
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head modifyDev; apply (modify_fields _ ?_ ?_ ?_).wp (· = $initial); all_goals intro d; rfl)
  | (rx_retention_head ForIn.forIn; apply list_view_spec id (fun w => view w = $initial); intro x b; change Preserves (fun w => view w = $initial) _)
  | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor view).wp (· = $initial))
  | (allocation_release_lift_from IndexM; exact (index _).wp (· = $initial))
  | (allocation_release_lift_from Net.M; exact (store (liftRouting_sameWGStore _)).wp (· = $initial))
  | (rx_retention_head modify; apply hoare_modify; intro w before; exact before)
  | encryption_past_frame $initial)

theorem key_get (id : Option KeypairId) : SameView view (keypairGet id) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' encryption_past_passive initial

theorem free_list (items : List SkbId) : SameView view (freeList items) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold freeList
  repeat' encryption_past_passive initial

theorem queued (pid : PeerId) (retry : Bool) : SameView view (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp only [branch,peekQueuedUnit,recordQueued]
  repeat' encryption_past_passive initial

theorem no_key (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) :
    SameView view (stagedOutNokey pid packets key invalid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold stagedOutNokey
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (queued _ _).wp (· = initial))
    | encryption_past_passive initial

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
