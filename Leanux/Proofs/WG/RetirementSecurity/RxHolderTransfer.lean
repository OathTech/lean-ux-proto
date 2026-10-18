import Leanux.Proofs.WG.RetirementSecurity.SlotProjection
import Leanux.Proofs.WG.RetirementSecurity.TxHolderTransfer

/-! Native RX queue admission and selection exchange one physical packet
holder for one source-local key reference. Queue multiplicity is explicit;
no extra credit is assigned to the decrypt-ring alias. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem peer_rx_exchange (old : peerLoans w pid p = some loans)
    (before : p.rxQueue.all.mapM (receiveLoan w pid) = some rx)
    (after : queue.all.mapM (receiveLoan w pid) = some rx')
    (transfer : (rx.map (·.allocation) ++ temporary).Perm
      (rx'.map (·.allocation) ++ temporary')) :
    ∃ loans', peerLoans w pid {p with rxQueue := queue} = some loans' ∧
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
        cases ht : p.txQueue.all.mapM (transmitLoan w pid) with
        | none => simp [peerLoans_eq,hn,hp,hc,ht] at old
        | some tx =>
          simp [peerLoans_eq,hn,hp,hc,ht,before] at old
          subst loans
          refine ⟨next ++ previous ++ current ++ tx ++ rx',?_,?_⟩
          · simp [peerLoans_eq,hn,hp,hc,ht,after]
          · apply List.perm_iff_count.mpr
            intro allocation
            have moved := transfer.count_eq allocation
            simp only [List.map_append,List.count_append] at moved ⊢
            omega

theorem HolderAccount.set_rx_queue (account : HolderAccount temporary w)
    (found : peerAt w pid = some p)
    (before : p.rxQueue.all.mapM (receiveLoan w pid) = some rx)
    (after : queue.all.mapM (receiveLoan w pid) = some rx')
    (transfer : (rx.map (·.allocation) ++ temporary).Perm
      (rx'.map (·.allocation) ++ temporary')) (a b : Ambient)
    (run : ((setPeer pid {p with rxQueue := queue}).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary' v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨loans',named',moved⟩ := peer_rx_exchange named before after transfer
  exact account.set_peer found named named' moved a b run

theorem HolderAccount.enqueue_rx {id : SkbId} (account : HolderAccount (allocation :: temporary) w)
    (found : peerAt w pid = some p)
    (packet : receiveLoan w pid id = some ⟨.receive pid id,allocation⟩)
    (a b : Ambient)
    (run : ((setPeer pid {p with rxQueue := p.rxQueue.enqueue id}).run w).run a =
      .ok (((),v),b)) : HolderAccount temporary v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨parts⟩ := peer_parts named
  apply account.set_rx_queue found parts.rxRun
    (rx' := parts.rx ++ [⟨.receive pid id,allocation⟩]) ?_ ?_ a b run
  · simp [Queues.prev_enqueue_all,List.mapM_append,parts.rxRun,packet]
  · apply List.perm_iff_count.mpr
    intro other
    simp only [List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil]
    omega

theorem HolderAccount.drop_rx {id : SkbId} (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (peeked : p.rxQueue.peeked = some id)
    (a b : Ambient)
    (run : ((setPeer pid {p with rxQueue := p.rxQueue.dropPeeked}).run w).run a =
      .ok (((),v),b)) :
    ∃ allocation, receiveLoan w pid id = some ⟨.receive pid id,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨parts⟩ := peer_parts named
  have oldRx := parts.rxRun
  have beforeShape : p.rxQueue.all = id :: p.rxQueue.dropPeeked.all := by
    simp [PrevQueue.all,PrevQueue.dropPeeked,peeked]
  cases packet : receiveLoan w pid id with
  | none => simp [beforeShape,List.mapM_cons,packet] at oldRx
  | some loan =>
    have holder : loan.holder = .receive pid id := by
      unfold receiveLoan at packet
      cases resident : w.dev.bind (fun d => d.rxSkbs[id]?) with
      | none => simp [resident] at packet
      | some pkt =>
        have name : nameLoan w (.receive pid id) pkt.keypair = some loan := by
          simpa [resident] using packet
        exact (nameLoan_resident name).1
    cases loan with
    | mk label allocation =>
      simp only at holder
      subst label
      refine ⟨allocation,rfl,?_⟩
      cases after : p.rxQueue.dropPeeked.all.mapM (receiveLoan w pid) with
      | none => simp [beforeShape,List.mapM_cons,packet,after] at oldRx
      | some rx =>
        apply account.set_rx_queue found (rx := ⟨.receive pid id,allocation⟩ :: rx)
          ?_ after ?_ a b run
        · simp [beforeShape,List.mapM_cons,packet,after]
        · exact List.perm_middle.symm

end Leanux.Proofs.WG.RetirementSecurity
