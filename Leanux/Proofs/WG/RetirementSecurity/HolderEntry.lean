import Leanux.Proofs.WG.RetirementSecurity.HolderCreation

/-! Entry funding derived from actual durable holders. These lemmas extract
the selected peer's slot occurrences from the native projection; callers do
not supply an unrelated slot ledger. Reassembling the projection after a
publication or removal is a separate transport obligation. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem mapM_member (f : α → Option β) (xs : List α) (ys : List β)
    (run : xs.mapM f = some ys) (member : x ∈ xs) :
    ∃ y, f x = some y ∧ y ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons,head] at run
    | some value =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons,head,tail] at run
      | some values =>
        simp [List.mapM_cons,head,tail] at run
        subst ys
        rcases List.mem_cons.mp member with same | inside
        · subst x
          exact ⟨value,head,by simp⟩
        · obtain ⟨y,found,belongs⟩ := ih values tail inside
          exact ⟨y,found,by simp [belongs]⟩

theorem optional_slot_funding (slot : Option KeypairId) (holder : KeyHolder)
    (run : slot.toList.mapM (nameLoan w holder) = some loans) :
    ∃ allocation : Option Credits.Allocation,
      allocation.map (·.slot) = slot ∧ loans.map (·.allocation) = allocation.toList := by
  cases slot with
  | none =>
    simp at run
    subst loans
    exact ⟨none,rfl,rfl⟩
  | some id =>
    cases named : nameLoan w holder id with
    | none => simp [named] at run
    | some loan =>
      simp [named] at run
      subst loans
      exact ⟨some loan.allocation,by simp [(nameLoan_resident named).2.1],rfl⟩

theorem peer_slot_funding (pid : PeerId) (p : Peer)
    (run : peerLoans w pid p = some loans) :
    ∃ slots : SlotLoans, ∃ queueCredits : Credits.Ledger,
      slots.Aligned p ∧ loans.map (·.allocation) = slots.credits ++ queueCredits := by
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
            obtain ⟨nextLoan,nextAligned,nextMap⟩ := optional_slot_funding _ _ hn
            obtain ⟨previousLoan,previousAligned,previousMap⟩ := optional_slot_funding _ _ hp
            obtain ⟨currentLoan,currentAligned,currentMap⟩ := optional_slot_funding _ _ hc
            refine ⟨⟨nextLoan,previousLoan,currentLoan⟩,(tx ++ rx).map (·.allocation),
              ⟨nextAligned,previousAligned,currentAligned⟩,?_⟩
            simp [SlotLoans.credits,List.map_append,nextMap,previousMap,currentMap,List.append_assoc]

theorem HolderAccount.peer_funding (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) :
    ∃ slots : SlotLoans, ∃ remaining : Credits.Ledger,
      slots.Aligned p ∧ PeerAccount pid p (slots.credits ++ remaining) w := by
  obtain ⟨loans,projected,credits⟩ := account
  cases device : w.dev with
  | none => simp [peerAt,device] at found
  | some d =>
    have peer : d.peers[pid]? = some p := by simpa [peerAt,device] using found
    cases mapped : d.peers.toList.mapM (fun (id,peer) => peerLoans w id peer) with
    | none => simp [durableLoans,device,mapped] at projected
    | some groups =>
      simp [durableLoans,device,mapped] at projected
      subst loans
      obtain ⟨group,groupRun,groupMember⟩ := mapM_member _ _ _ mapped
        (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr peer)
      obtain ⟨slots,queueCredits,aligned,slotMap⟩ := peer_slot_funding pid p groupRun
      obtain ⟨earlier,later,split⟩ := List.mem_iff_append.mp groupMember
      subst groups
      refine ⟨slots,queueCredits ++ earlier.flatten.map (·.allocation) ++
        later.flatten.map (·.allocation) ++ temporary,aligned,found,?_⟩
      apply credits.perm
      apply List.perm_iff_count.mpr
      intro allocation
      simp only [List.flatten_append,List.flatten_cons,List.map_append,
        List.count_append,slotMap]
      omega

theorem HolderAccount.peer_loans (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) : ∃ loans, peerLoans w pid p = some loans := by
  obtain ⟨loans,projected,_⟩ := account
  cases device : w.dev with
  | none => simp [peerAt,device] at found
  | some d =>
    have peer : d.peers[pid]? = some p := by simpa [peerAt,device] using found
    cases mapped : d.peers.toList.mapM (fun (id,peer) => peerLoans w id peer) with
    | none => simp [durableLoans,device,mapped] at projected
    | some groups =>
      obtain ⟨group,groupRun,_⟩ := mapM_member _ _ _ mapped
        (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr peer)
      exact ⟨group,groupRun⟩

end Leanux.Proofs.WG.RetirementSecurity
