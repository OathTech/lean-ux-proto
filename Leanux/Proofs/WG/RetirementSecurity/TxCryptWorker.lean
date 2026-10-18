import Leanux.Proofs.WG.RetirementSecurity.TxCryptSendFrames

/-! The actual TX worker cannot free a packet still pending encryption.
The native readiness guard, queue uniqueness and UNCRYPTED alias marks
discharge separation before dropping the owning queue occurrence. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem tx_ready_native (a b : Ambient)
    (run : ((txReadySource selected).run w).run a = .ok ((true,v),b)) :
    v = w ∧ ∃ items first, selected = some items ∧ items.head? = some first ∧
      (TxDisposition.HeadState first .dead w ∨ TxDisposition.HeadState first .crypted w) := by
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame selected (fun s => s = w))
    w a true v b rfl run
  refine ⟨same,?_⟩
  cases selected with
  | none => cases run
  | some items =>
    cases items with
    | nil => cases run
    | cons first tail =>
      change (((do
        let packet ← getTxSkb first
        branch .txNotUncrypted (packet.state != .uncrypted) : WG.M Bool).run w).run
          (CounterWindow.record a .txPacket true)) = .ok ((true,v),b) at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨packet,u,c,readRun,branchRun⟩ := run
      obtain ⟨world,_,d,device,stored⟩ := Packets.getTxSkb_current first w u packet _ c readRun
      subst u
      have resident : TxDisposition.txPackets w first = some packet := by
        simp [TxDisposition.txPackets,device,stored]
      refine ⟨first :: tail,first,rfl,rfl,?_⟩
      cases mark : packet.state with
      | uncrypted => simp only [mark] at branchRun; cases branchRun
      | dead => exact Or.inl ⟨packet,resident,mark⟩
      | crypted => exact Or.inr ⟨packet,resident,mark⟩

theorem TxCryptInventory.ready_tail (crypt : TxCryptInventory active w)
    (inventory : TxInventory locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = some items)
    (head : items.head? = some first)
    (ready : TxDisposition.HeadState first .dead w ∨ TxDisposition.HeadState first .crypted w)
    (a b : Ambient)
    (run : ((txReadyTail pid (some items)).run w).run a = .ok ((result,v),b)) :
    result = true ∧ TxCryptInventory active v := by
  rw [txReadyTail_factor pid items first head,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,c,readRun,tail⟩ := run
  obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current first w u packet a c readRun
  subst u
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨_,dropped,e,dropRun,tail⟩ := tail
  obtain ⟨d,p,device,stored,_,_⟩ := txDrop_effect pid a e dropRun
  have found : peerAt w pid = some p := by simp [peerAt,device,stored]
  have queue : p.txQueue.all = items :: p.txQueue.dropPeeked.all := by
    simp [PrevQueue.all,PrevQueue.dropPeeked,cached p found]
  have outside := crypt.ready_outside inventory found queue head ready
  have droppedPhase := crypt.drop_native outside cached a e dropRun
  have droppedInventory := inventory.drop_native cached a e dropRun
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨_,completed,f,completeRun,disposeRun⟩ := tail
  have completedPhase := droppedPhase.send_completion pid items packet e f completeRun
  have completedInventory := droppedInventory.complete pid items packet e f completeRun
  exact completedPhase.dispose (completedPhase.local_outside completedInventory) pid packet.keypair f b disposeRun

theorem TxCryptInventory.body (crypt : TxCryptInventory active w)
    (inventory : TxInventory locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = selected)
    (a b : Ambient)
    (run : ((TxDisposition.bodySource pid selected).run w).run a = .ok ((result,v),b)) :
    TxCryptInventory active v := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,testRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame selected (fun s => s = w))
    w a ready u c rfl testRun
  subst u
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail; exact crypt
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨_,items,first,selectedEq,head,mark⟩ := tx_ready_native a c testRun
    subst selected
    exact (crypt.ready_tail inventory cached head mark c b tail).2

theorem TxCryptInventory.peek (crypt : TxCryptInventory active w) (pid : PeerId)
    (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    TxCryptInventory active v := by
  obtain ⟨d,p,queue,device,stored,contents,_,after⟩ := txPeek_effect pid a b run
  apply crypt.frame_packets
  · simp [TxRing.nativeCell,after,replacePeer,device]
  · intro items owned
    apply owned.queues
    funext other
    by_cases same : pid = other
    · subst other
      simp [RxCredits.handoffTxView,after,replacePeer,device,stored,contents]
    · simp [RxCredits.handoffTxView,after,replacePeer,device,Std.TreeMap.getElem?_insert,same]
  · funext id
    simp [TxDisposition.txPackets,after,replacePeer,device]

/-- The original TX worker preserves pending/active encryption exclusivity
without a separate disposal-separation assumption. The actual readiness guard
and physical queue inventory supply it before any packet free. -/
theorem TxCryptInventory.step (crypt : TxCryptInventory active w)
    (inventory : TxInventory locals w) (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    TxCryptInventory active v := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peekRun,bodyRun⟩ := run
  have selected := crypt.peek pid a c peekRun
  have physical := inventory.peek pid a c peekRun
  obtain ⟨d,p,queue,_,_,_,cached,after⟩ := txPeek_effect pid a c peekRun
  apply selected.body physical (a := c) (b := b) (run := bodyRun)
  intro q resident
  have same : q = {p with txQueue := queue} := by
    simpa [peerAt,after,replacePeer] using resident.symm
  subst q
  exact cached

end Leanux.Proofs.WG.RetirementSecurity
