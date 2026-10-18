import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceDisposal

/-! The native TX worker selects one actual peer-queue occurrence, moves
it to a selected caller local, completes it and disposes it. All surviving
packet occurrences remain unique; stopped iterations consume none. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem TxInventory.complete (inventory : TxInventory locals w)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (a b : Ambient)
    (run : ((txCompletionSource pid items head).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := by
  simp only [txCompletionSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨crypted,u,c,branchRun,tail⟩ := run
  have same : u = w := by cases branchRun; rfl
  subst u
  cases crypted with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact inventory
  | true =>
    simp only [ite_true] at tail
    exact inventory.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (createDataDone_ownership pid items) w c () v b tail)

theorem TxInventory.ready_tail (inventory : TxInventory locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((txReadyTail pid first).run w).run a = .ok ((result,v),b)) :
    result = true ∧ TxInventory locals v := by
  cases first with
  | none => simp only [txReadyTail] at run; cases run
  | some items =>
    cases headId : items.head? with
    | none => simp only [txReadyTail,headId] at run; cases run
    | some id =>
      rw [txReadyTail_factor pid items id headId,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨head,u,c,readRun,tail⟩ := run
      obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current id w u head a c readRun
      subst u
      subst c
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,dropped,e,dropRun,tail⟩ := tail
      have selected := inventory.drop_native cached a e dropRun
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,completed,f,completeRun,disposeRun⟩ := tail
      exact (selected.complete pid items head e f completeRun).dispose head.keypair f b disposeRun

theorem TxInventory.body (inventory : TxInventory locals w)
    (cached : ∀ p, peerAt w pid = some p → p.txQueue.peeked = first)
    (a b : Ambient)
    (run : ((Queues.TxDisposition.bodySource pid first).run w).run a = .ok ((result,v),b)) :
    TxInventory locals v := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,readRun,tail⟩ := run
  have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (fun s => s = w))
    w a ready u c rfl readRun
  subst u
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail; exact inventory
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    exact (inventory.ready_tail cached c b tail).2

theorem TxInventory.step (inventory : TxInventory locals w) (pid : PeerId)
    (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) : TxInventory locals v := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peekRun,bodyRun⟩ := run
  have selected := inventory.peek pid a c peekRun
  obtain ⟨d,p,queue,_,_,_,cached,after⟩ := txPeek_effect pid a c peekRun
  apply selected.body (a := c) (b := b) (run := bodyRun)
  intro q resident
  have same : q = {p with txQueue := queue} := by
    simpa [peerAt,after,replacePeer] using resident.symm
  subst q
  exact cached

theorem HolderAccount.tx_step_inventory (account : HolderAccount temporary w)
    (inventory : TxInventory locals w) (funded : PeerReleaseFunded pid w)
    (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v ∧ TxInventory locals v :=
  ⟨account.tx_step (inventory.separated pid) funded a b run,inventory.step pid a b run⟩

theorem initial_tx_inventory (net bare : Bool) : TxInventory [] (Runner.initialWG net bare) := by
  have empty : ∀ pid p, peerAt (Runner.initialWG net bare) pid ≠ some p := by
    intro pid p
    cases net <;> cases bare <;> simp [peerAt,Runner.initialWG]
  exact ⟨by simp [txLocalItems],fun pid p found => (empty pid p found).elim,
    fun pid p _ _ found => (empty pid p found).elim,
    fun pid p found => (empty pid p found).elim,
    by simp [txLocalItems],fun pid p found => (empty pid p found).elim⟩

end Leanux.Proofs.WG.RetirementSecurity
