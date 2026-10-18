import Leanux.Proofs.WG.RetirementSecurity.HolderClear
import Leanux.Proofs.WG.Queues.PrevQueue

/-! The original per-peer TX setters transfer exactly one key-reference
occurrence per batch. A cached peek remains a durable holder until the actual
drop setter; device-ring aliases contribute no additional occurrence. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem peer_tx_exchange (old : peerLoans w pid p = some loans)
    (before : p.txQueue.all.mapM (transmitLoan w pid) = some tx)
    (after : queue.all.mapM (transmitLoan w pid) = some tx')
    (transfer : (tx.map (·.allocation) ++ temporary).Perm
      (tx'.map (·.allocation) ++ temporary')) :
    ∃ loans', peerLoans w pid {p with txQueue := queue} = some loans' ∧
      (loans.map (·.allocation) ++ temporary).Perm
        (loans'.map (·.allocation) ++ temporary') := by
  cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) with
  | none => simp [peerLoans_eq,hn] at old
  | some next =>
    cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) with
    | none => simp [peerLoans_eq,hn,hp] at old
    | some previous =>
      cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) with
      | none => simp [peerLoans_eq,hn,hp,hc] at old
      | some current =>
        cases hr : p.rxQueue.all.mapM (receiveLoan w pid) with
        | none => simp [peerLoans_eq,hn,hp,hc,before,hr] at old
        | some rx =>
          simp [peerLoans_eq,hn,hp,hc,before,hr] at old
          subst loans
          refine ⟨next ++ previous ++ current ++ tx' ++ rx,?_,?_⟩
          · simp [peerLoans_eq,hn,hp,hc,after,hr]
          · apply List.perm_iff_count.mpr
            intro allocation
            have moved := transfer.count_eq allocation
            simp only [List.map_append,List.count_append] at moved ⊢
            omega

theorem HolderAccount.set_tx_queue (account : HolderAccount temporary w)
    (found : peerAt w pid = some p)
    (before : p.txQueue.all.mapM (transmitLoan w pid) = some tx)
    (after : queue.all.mapM (transmitLoan w pid) = some tx')
    (transfer : (tx.map (·.allocation) ++ temporary).Perm
      (tx'.map (·.allocation) ++ temporary')) (a b : Ambient)
    (run : ((setPeer pid {p with txQueue := queue}).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary' v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨loans',named',moved⟩ := peer_tx_exchange named before after transfer
  exact account.set_peer found named named' moved a b run

theorem HolderAccount.enqueue_tx (account : HolderAccount (allocation :: temporary) w)
    (found : peerAt w pid = some p)
    (batch : transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩)
    (a b : Ambient)
    (run : ((setPeer pid {p with txQueue := p.txQueue.enqueue item}).run w).run a =
      .ok (((),v),b)) : HolderAccount temporary v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  cases before : p.txQueue.all.mapM (transmitLoan w pid) with
  | none =>
    simp only [peerLoans_eq] at named
    cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) <;>
      cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) <;>
      cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) <;>
      simp [hn,hp,hc,before] at named
  | some tx =>
    apply account.set_tx_queue found before (tx' := tx ++ [⟨.transmit pid item,allocation⟩])
      ?_ ?_ a b run
    · simp [Queues.prev_enqueue_all,List.mapM_append,before,batch]
    · apply List.perm_iff_count.mpr
      intro other
      simp only [List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil]
      omega

theorem HolderAccount.drop_tx (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (peeked : p.txQueue.peeked = some item)
    (a b : Ambient)
    (run : ((setPeer pid {p with txQueue := p.txQueue.dropPeeked}).run w).run a =
      .ok (((),v),b)) :
    ∃ allocation, transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  have beforeShape : p.txQueue.all = item :: p.txQueue.dropPeeked.all := by
    simp [PrevQueue.all,PrevQueue.dropPeeked,peeked]
  cases batch : transmitLoan w pid item with
  | none =>
    simp only [peerLoans_eq] at named
    cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) <;>
      cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) <;>
      cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) <;>
      simp [hn,hp,hc,beforeShape,List.mapM_cons,batch] at named
  | some loan =>
    have holder : loan.holder = .transmit pid item := by
      unfold transmitLoan at batch
      cases head : item.head? with
      | none => simp [head] at batch
      | some id =>
        cases packet : w.dev.bind (fun d => d.txSkbs[id]?) with
        | none => simp [head,packet] at batch
        | some pkt =>
          have name : nameLoan w (.transmit pid item) pkt.keypair = some loan := by
            simpa [head,packet] using batch
          exact (nameLoan_resident name).1
    cases loan with
    | mk label allocation =>
      simp only at holder
      subst label
      refine ⟨allocation,rfl,?_⟩
      cases after : p.txQueue.dropPeeked.all.mapM (transmitLoan w pid) with
      | none =>
        simp only [peerLoans_eq] at named
        cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) <;>
          cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) <;>
          cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) <;>
          simp [hn,hp,hc,beforeShape,List.mapM_cons,batch,after] at named
      | some tx =>
        apply account.set_tx_queue found (tx := ⟨.transmit pid item,allocation⟩ :: tx)
          ?_ after ?_ a b run
        · simp [beforeShape,List.mapM_cons,batch,after]
        · exact List.perm_middle.symm

end Leanux.Proofs.WG.RetirementSecurity
