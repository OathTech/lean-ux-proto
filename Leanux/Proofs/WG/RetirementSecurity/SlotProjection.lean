import Leanux.Proofs.WG.RetirementSecurity.HolderReassembly

/-! Concrete slot and queue components used to reconstruct a selected peer
after a native slot rotation. Slot names may move while allocation identities
and the single reference per TX batch remain unchanged. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

structure PeerParts (w : WGWorld) (pid : PeerId) (p : Peer) (loans : List KeyLoan) where
  slots : SlotLoans
  aligned : slots.Aligned p
  tx : List KeyLoan
  rx : List KeyLoan
  txRun : p.txQueue.all.mapM (transmitLoan w pid) = some tx
  rxRun : p.rxQueue.all.mapM (receiveLoan w pid) = some rx
  credits : loans.map (·.allocation) = slots.credits ++ (tx ++ rx).map (·.allocation)

theorem peer_parts (run : peerLoans w pid p = some loans) :
    Nonempty (PeerParts w pid p loans) := by
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
            refine ⟨⟨⟨nextLoan,previousLoan,currentLoan⟩,
              ⟨nextAligned,previousAligned,currentAligned⟩,tx,rx,ht,hr,?_⟩⟩
            simp [SlotLoans.credits,List.map_append,nextMap,previousMap,currentMap,List.append_assoc]

def slotNames (holder : KeyHolder) (loan : Option Credits.Allocation) : List KeyLoan :=
  loan.toList.map fun allocation => ⟨holder,allocation⟩

theorem slotNames_credits (holder : KeyHolder) (loan : Option Credits.Allocation) :
    (slotNames holder loan).map (·.allocation) = loan.toList := by
  cases loan <;> rfl

theorem slot_names_run (holder : KeyHolder) (loan : Option Credits.Allocation)
    (slot : Option KeypairId) (aligned : loan.map (·.slot) = slot)
    (resident : ∀ allocation ∈ loan.toList, ∃ k,
      keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp) :
    slot.toList.mapM (nameLoan w holder) = some (slotNames holder loan) := by
  rw [←aligned]
  cases loan with
  | none => rfl
  | some allocation =>
    obtain ⟨k,found,stamp⟩ := resident allocation (by simp)
    cases allocation
    simp [slotNames,nameLoan,found,stamp]

theorem peer_rebuild (pid : PeerId) (p : Peer) (slots : SlotLoans)
    (aligned : slots.Aligned p) (tx rx : List KeyLoan)
    (txRun : p.txQueue.all.mapM (transmitLoan w pid) = some tx)
    (rxRun : p.rxQueue.all.mapM (receiveLoan w pid) = some rx)
    (resident : ∀ allocation ∈ slots.credits, ∃ k,
      keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp) :
    ∃ loans, peerLoans w pid p = some loans ∧
      loans.map (·.allocation) = slots.credits ++ (tx ++ rx).map (·.allocation) := by
  have hn := slot_names_run (.peerSlot pid .next) slots.next p.keypairNext aligned.1
    (fun allocation member => resident allocation (by simp [SlotLoans.credits,member]))
  have hp := slot_names_run (.peerSlot pid .previous) slots.previous p.keypairPrevious aligned.2.1
    (fun allocation member => resident allocation (by simp [SlotLoans.credits,member]))
  have hc := slot_names_run (.peerSlot pid .current) slots.current p.keypairCurrent aligned.2.2
    (fun allocation member => resident allocation (by simp [SlotLoans.credits,member]))
  refine ⟨slotNames (.peerSlot pid .next) slots.next ++ slotNames (.peerSlot pid .previous) slots.previous ++
    slotNames (.peerSlot pid .current) slots.current ++ tx ++ rx,?_,?_⟩
  · simp [peerLoans_eq,hn,hp,hc,txRun,rxRun]
  · simp [List.map_append,slotNames_credits,SlotLoans.credits,List.append_assoc]

theorem transmitLoan_transport (shape : (carrierShape v).2 = (carrierShape w).2)
    (found : transmitLoan w pid batch = some loan)
    (resident : ∃ k, keyAt v loan.allocation.slot = some k ∧
      k.internalId = loan.allocation.stamp) : transmitLoan v pid batch = some loan := by
  unfold transmitLoan at found ⊢
  cases head : batch.head? with
  | none => simp [head] at found
  | some id =>
    cases packet : w.dev.bind (fun d => d.txSkbs[id]?) with
    | none => simp [head,packet] at found
    | some pkt =>
      have samePacket := congrFun (congrArg (fun shape => shape.1) shape) id
      simp only [carrierShape] at samePacket
      rw [packet] at samePacket
      have named : nameLoan w (.transmit pid batch) pkt.keypair = some loan := by
        simpa [head,packet] using found
      simpa [head,samePacket] using nameLoan_transport named resident

theorem receiveLoan_transport {id : SkbId} (shape : (carrierShape v).2 = (carrierShape w).2)
    (found : receiveLoan w pid id = some loan)
    (resident : ∃ k, keyAt v loan.allocation.slot = some k ∧
      k.internalId = loan.allocation.stamp) : receiveLoan v pid id = some loan := by
  unfold receiveLoan at found ⊢
  cases packet : w.dev.bind (fun d => d.rxSkbs[id]?) with
  | none => simp [packet] at found
  | some pkt =>
    have samePacket := congrFun (congrArg (fun shape => shape.2) shape) id
    simp only [carrierShape] at samePacket
    rw [packet] at samePacket
    have named : nameLoan w (.receive pid id) pkt.keypair = some loan := by
      simpa [packet] using found
    simpa [samePacket] using nameLoan_transport named resident

theorem PeerParts.rebuild (parts : PeerParts w pid p oldLoans)
    (q : Peer) (slots : SlotLoans) (aligned : slots.Aligned q)
    (tx : q.txQueue = p.txQueue) (rx : q.rxQueue = p.rxQueue)
    (packets : (carrierShape v).2 = (carrierShape w).2)
    (credits : Credits.Exact
      (slots.credits ++ (parts.tx ++ parts.rx).map (·.allocation) ++ remaining) v) :
    ∃ loans, peerLoans v pid q = some loans ∧
      loans.map (·.allocation) = slots.credits ++ (parts.tx ++ parts.rx).map (·.allocation) := by
  have txRun := mapM_transport _ (transmitLoan v pid) _ _ parts.txRun (by
    intro batch loan member found
    apply transmitLoan_transport packets found
    obtain ⟨k,resident,stamp,_⟩ := credits.resident
      (allocation := loan.allocation) (by simp [List.map_append,List.mem_map_of_mem member])
    exact ⟨k,resident,stamp⟩)
  have rxRun := mapM_transport _ (receiveLoan v pid) _ _ parts.rxRun (by
    intro id loan member found
    apply receiveLoan_transport packets found
    obtain ⟨k,resident,stamp,_⟩ := credits.resident
      (allocation := loan.allocation) (by simp [List.map_append,List.mem_map_of_mem member])
    exact ⟨k,resident,stamp⟩)
  apply peer_rebuild pid q slots aligned parts.tx parts.rx
    (by simpa only [tx] using txRun) (by simpa only [rx] using rxRun)
  intro allocation member
  obtain ⟨k,resident,stamp,_⟩ := credits.resident
    (allocation := allocation) (by simp [member])
  exact ⟨k,resident,stamp⟩

end Leanux.Proofs.WG.RetirementSecurity
