import Leanux.Proofs.WG.RetirementSecurity.HolderPublication

/-! A native clear moves each concrete slot occurrence to its saved local,
then pays that occurrence. The resulting holder account is reconstructed from
the actual post-state, including all RX and TX holders that remain. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem peer_clear_transfer (pid : PeerId) (p : Peer) (slot : KeySlot)
    (run : peerLoans w pid p = some loans) :
    ∃ loan : Option Credits.Allocation, ∃ remaining : List KeyLoan,
      loan.map (·.slot) = slot.get p ∧
      peerLoans w pid (slot.clear p) = some remaining ∧
      (loans.map (·.allocation)).Perm (loan.toList ++ remaining.map (·.allocation)) := by
  cases hn : p.keypairNext.toList.mapM (nameLoan w (.peerSlot pid .next)) with
  | none => simp [peerLoans_eq,hn] at run
  | some next =>
    cases hp : p.keypairPrevious.toList.mapM (nameLoan w (.peerSlot pid .previous)) with
    | none => simp [peerLoans_eq,hn,hp] at run
    | some previous =>
      cases hc : p.keypairCurrent.toList.mapM (nameLoan w (.peerSlot pid .current)) with
      | none => simp [peerLoans_eq,hn,hp,hc] at run
      | some current =>
        cases ht : p.txQueue.all.mapM (transmitLoan w pid) with
        | none => simp [peerLoans_eq,hn,hp,hc,ht] at run
        | some tx =>
          cases hr : p.rxQueue.all.mapM (receiveLoan w pid) with
          | none => simp [peerLoans_eq,hn,hp,hc,ht,hr] at run
          | some rx =>
            simp [peerLoans_eq,hn,hp,hc,ht,hr] at run
            subst loans
            cases slot with
            | next =>
              obtain ⟨loan,aligned,mapped⟩ := optional_slot_funding _ _ hn
              refine ⟨loan,previous ++ current ++ tx ++ rx,aligned,?_,?_⟩
              · simp [peerLoans_eq,KeySlot.clear,hp,hc,ht,hr]
              · simp only [List.map_append,mapped]
                exact List.Perm.of_eq (by simp only [List.append_assoc])
            | previous =>
              obtain ⟨loan,aligned,mapped⟩ := optional_slot_funding _ _ hp
              refine ⟨loan,next ++ current ++ tx ++ rx,aligned,?_,?_⟩
              · simp [peerLoans_eq,KeySlot.clear,hn,hc,ht,hr]
              · apply List.perm_iff_count.mpr
                intro allocation
                simp only [List.map_append,mapped,List.count_append]
                omega
            | current =>
              obtain ⟨loan,aligned,mapped⟩ := optional_slot_funding _ _ hc
              refine ⟨loan,next ++ previous ++ tx ++ rx,aligned,?_,?_⟩
              · simp [peerLoans_eq,KeySlot.clear,hn,hp,ht,hr]
              · apply List.perm_iff_count.mpr
                intro allocation
                simp only [List.map_append,mapped,List.count_append]
                omega

theorem HolderAccount.update_slot (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (slot : KeySlot) (a b : Ambient)
    (run : ((updateSlot pid slot).run w).run a = .ok (((),v),b)) :
    ∃ loan : Option Credits.Allocation, loan.map (·.slot) = slot.get p ∧
      HolderAccount (loan.toList ++ temporary) v := by
  rw [updateSlot,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨read,u,c,readRun,setRun⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,peer⟩ := Origins.getPeer_return pid w u read a c readRun
  subst u
  subst c
  have same : read = p := by
    have readFound : peerAt w pid = some read := by simp [peerAt,device,peer]
    exact Option.some.inj (readFound.symm.trans found)
  subst read
  obtain ⟨loans,loansRun⟩ := account.peer_loans found
  obtain ⟨loan,remaining,aligned,remainingRun,order⟩ := peer_clear_transfer pid p slot loansRun
  refine ⟨loan,aligned,account.set_peer found loansRun remainingRun ?_ a b setRun⟩
  apply List.perm_iff_count.mpr
  intro allocation
  have moved := order.count_eq allocation
  simp only [List.count_append] at moved ⊢
  omega

theorem HolderAccount.put_optional (loan : Option Credits.Allocation)
    (account : HolderAccount (loan.toList ++ temporary) w) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (loan.map (·.slot)) now).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  cases loan with
  | none =>
    simp [keypairPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact account
  | some loan => exact account.put now a b run

theorem HolderAccount.clear_slot (account : HolderAccount temporary w)
    (pid : PeerId) (slot : KeySlot) (a b : Ambient)
    (run : ((clearSlot pid slot).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [clearSlot,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,tailRun⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,peer⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at tailRun
  obtain ⟨result,middle,middleAmbient,updateRun,putRun⟩ := tailRun
  cases result
  have found : peerAt w pid = some p := by simp [peerAt,device,peer]
  obtain ⟨loan,aligned,moved⟩ := account.update_slot found slot a middleAmbient updateRun
  rw [←aligned] at putRun
  exact moved.put_optional loan true middleAmbient b putRun

theorem clear_slot_preserves (pid : PeerId) (slot : KeySlot) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (clearSlot pid slot) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  cases result
  exact account.clear_slot pid slot a b run

theorem clear_holders (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (keypairsClear pid) := by
  rw [clear_source]
  exact preserves_bind (clear_slot_preserves pid .next temporary) (fun _ =>
    preserves_bind (clear_slot_preserves pid .previous temporary) (fun _ =>
      clear_slot_preserves pid .current temporary))

end Leanux.Proofs.WG.RetirementSecurity
