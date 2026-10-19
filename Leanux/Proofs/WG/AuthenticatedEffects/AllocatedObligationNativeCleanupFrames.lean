import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedCleanupFrames

/-! Ordinary completion frees emit lifetime access events, not named-drop
receipts. These contracts use the original native free directly and preserve
the same first-terminal ledger entries while discharging physical debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

theorem native_free_views (skb : SkbId) (w v : World)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    Packets.epoch v.wg = Packets.epoch w.wg ∧
    PacketMaterial.view v.wg skb = none ∧
    ∀ id, id ≠ skb → PacketMaterial.view v.wg id = PacketMaterial.view w.wg id := by
  obtain ⟨device,packet,atDevice,_,after⟩ := Terminal.native_free skb w v run
  rw [after]
  refine ⟨?_,?_,?_⟩
  · simp [Packets.epoch,Packets.update,atDevice]
  · simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice]
  · intro id different
    simp [PacketMaterial.view,TxDisposition.txPackets,Packets.update,atDevice,
      Std.TreeMap.getElem?_erase,Ne.symm different]

theorem Resident.native_free (before : Resident history ledger w.wg)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v))
    (unused : Unused history ledger w.wg skb) : Resident history ledger v.wg := by
  obtain ⟨epoch,_,other⟩ := native_free_views skb w v run
  intro ticket position ordinal member
  obtain ⟨generation,id,value,origin,time,cell⟩ := before ticket position ordinal member
  have different : id ≠ skb := by
    intro same
    subst id
    exact unused ticket position ordinal member generation value origin time
  exact ⟨generation,id,value,origin,epoch.trans time,(other id different).trans cell⟩

theorem Covered.native_free (covered : Covered history ledger debts w.wg)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    Covered history ledger (forgetFreedCell history generation skb debts) v.wg := by
  obtain ⟨epoch,erased,other⟩ := native_free_views skb w v run
  intro id value cell
  have different : id ≠ skb := by
    intro same
    subst id
    rw [erased] at cell
    cases cell
  obtain ⟨oldGeneration,ticket,position,ordinal,time,origin,tracked⟩ :=
    covered id value ((other id different).symm.trans cell)
  refine ⟨oldGeneration,ticket,position,ordinal,epoch.trans time,origin,?_⟩
  rcases tracked with pending | ⟨outcome,debt,terminal⟩
  · exact Or.inl pending
  · refine Or.inr ⟨outcome,mem_forgetFreedCell.mpr ⟨debt,?_⟩,terminal⟩
    rintro ⟨_,otherOrigin⟩
    exact different (origin.unique otherOrigin).2.1

theorem DebtsResident.native_free (resident : DebtsResident history ledger debts w.wg)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v))
    (atEpoch : Packets.epoch w.wg = some generation) :
    DebtsResident history ledger (forgetFreedCell history generation skb debts) v.wg := by
  obtain ⟨epoch,_,other⟩ := native_free_views skb w v run
  intro debt member
  obtain ⟨old,notRefers⟩ := mem_forgetFreedCell.mp member
  obtain ⟨terminal,oldGeneration,id,value,origin,time,cell⟩ := resident debt old
  have sameEpoch : oldGeneration = generation := Option.some.inj (time.symm.trans atEpoch)
  subst oldGeneration
  have different : id ≠ skb := by
    intro same
    subst id
    exact notRefers ⟨value,origin⟩
  exact ⟨terminal,generation,id,value,origin,epoch.trans time,(other id different).trans cell⟩

/-- The actual reason-free native cleanup removes the identified terminal
debt. Mixed uniqueness excludes pending aliases; the unchanged ledger keeps
every first outcome. No named-drop receipt is manufactured for this cut. -/
theorem cleanup_native_mixed
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v))
    (validLedger : Valid births ledger) (mixed : MixedInjective history ledger debts)
    (resident : Resident history ledger w.wg) (covered : Covered history ledger debts w.wg)
    (cleanup : DebtsResident history ledger debts w.wg)
    (debt : CleanupDebt) (member : debt ∈ debts)
    (origin : Origin history debt.position debt.ordinal generation skb value)
    (epoch : Packets.epoch w.wg = some generation) :
    let afterDebts := forgetFreedCell history generation skb debts
    Resident history ledger v.wg ∧ MixedInjective history ledger afterDebts ∧
      Covered history ledger afterDebts v.wg ∧ DebtsResident history ledger afterDebts v.wg ∧
      (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧ debt ∉ afterDebts := by
  have terminal := (cleanup debt member).1
  have unused := mixed.unused validLedger debt member terminal origin epoch
  refine ⟨resident.native_free run unused,mixed.forget generation skb,
    covered.native_free run,cleanup.native_free run epoch,terminal,?_⟩
  intro retained
  exact (mem_forgetFreedCell.mp retained).2 ⟨value,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
