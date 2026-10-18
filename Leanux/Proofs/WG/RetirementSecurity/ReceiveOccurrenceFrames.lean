import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryHolders

/-! RX store and queue bookkeeping cannot modify TX cells, their pending
encryption ring, or physical TX ownership. Peer release is handled separately
because an empty peer queue can disappear with the peer record. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReceiveOccurrences
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem skb_queues (action : SkbM α) : SameView handoffTxView (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  funext pid
  simpa only [handoffTxView,device,Option.bind_some] using congrFun before pid

theorem get_rx_wire (id : SkbId) : SameView txCryptWire (getRxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact congrArg txCryptWire (Packets.getRxSkb_current id w v result a b run).1

theorem new_rx_wire (packet : RxPacket) : SameView txCryptWire (newRxSkb packet) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases device : w.dev with
  | none => simp [newRxSkb,liftSkb_run,device] at run
  | some d =>
    rw [Packets.newRxSkb_run w a d packet device] at run
    cases run
    simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Packets.update,device]

theorem set_rx_wire (id : SkbId) (f : RxPacket → RxPacket) : SameView txCryptWire (setRxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [setRxSkb,liftSkb_run,device] at run
  | some d =>
    cases resident : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some packet =>
      rw [Packets.setRxSkb_run w a d id packet f device resident] at run
      cases run
      simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Packets.update,device]

theorem free_rx_wire (id : SkbId) : SameView txCryptWire (freeRxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [freeRxSkb,liftSkb_run,device] at run
  | some d =>
    cases resident : d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some packet =>
      rw [Packets.freeRxSkb_run w a d id packet device resident] at run
      cases run
      simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Packets.update,device]

theorem peer_get_wire (peer : Option PeerId) : SameView txCryptWire (peerGetMaybeZero peer) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peerGetMaybeZero refcountIncNotZero
  simp only [requireNotPending,branch,branchCmp,invariant,unsupported]
  repeat' crypt_wire_step initial

theorem owner_wire (owner : IndexOwner) (word : Option PeerId) :
    SameView txCryptWire (owner.setPeerWord word) := by
  cases owner <;> intro initial
  all_goals change Preserves (fun w => txCryptWire w = initial) _
  all_goals unfold IndexOwner.setPeerWord
  all_goals repeat' crypt_wire_step initial

theorem owner_queues (owner : IndexOwner) (word : Option PeerId) :
    SameView handoffTxView (owner.setPeerWord word) := by
  cases owner <;> intro initial
  all_goals change Preserves (fun w => handoffTxView w = initial) _
  all_goals unfold IndexOwner.setPeerWord
  all_goals repeat' crypt_queue_step initial

theorem acquire_owner_wire (owner : IndexOwner) : SameView txCryptWire (Affiliation.acquireOwner owner) := by
  intro initial
  unfold Affiliation.acquireOwner
  apply preserves_bind (indexOwner_peerWord_preserves owner _)
  intro word
  apply preserves_bind ((peer_get_wire word).wp (· = initial))
  intro result
  apply preserves_bind ((owner_wire owner result).wp (· = initial))
  intro _
  exact preserves_pure _

theorem acquire_owner_queues (owner : IndexOwner) : SameView handoffTxView (Affiliation.acquireOwner owner) := by
  intro initial
  unfold Affiliation.acquireOwner
  apply preserves_bind (indexOwner_peerWord_preserves owner _)
  intro word
  apply preserves_bind ((ownership_queues (peerGetMaybe_ownership word)).wp (· = initial))
  intro result
  apply preserves_bind ((owner_queues owner result).wp (· = initial))
  intro _
  exact preserves_pure _

theorem index_lookup (kinds : List IndexKind) (index : Nat) :
    Preserves (TxOccurrences locals active) (indexLookup kinds index) := by
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · apply hoare_liftIndex
    intro w d table before device
    have wire : txCryptWire {w with dev := some {d with indexTable := table}} = txCryptWire w := by
      simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,device]
    have queues : handoffTxView {w with dev := some {d with indexTable := table}} = handoffTxView w := by
      funext pid; simp [handoffTxView,device]
    exact ⟨before.1.wire_queues wire queues,before.2.frame_packets (congrArg Prod.fst wire)
      (fun _ owner => owner.queues queues) (congrArg Prod.snd wire)⟩
  · intro owner
    exact occurrence_passive (acquire_owner_wire owner) (acquire_owner_queues owner)

end Leanux.Proofs.WG.RetirementSecurity.ReceiveOccurrences
