import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverageCleanup

/-! The original free removes exactly its native allocation cell. Coverage
and cleanup backing are transported together; pending backing still requires
the separately proved no-pending-alias condition at this source cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

/-- Actual physical deletion discharges precisely the debts for this epoch
and cell, retaining every other allocation and terminal ledger result. -/
theorem Covered.free (covered : Covered history ledger debts receipt.run.before.wg)
    (native : (receipt : Terminal.Receipt).Valid) :
    Covered history ledger (forgetFreedCell history generation receipt.skb debts) receipt.run.after.wg := by
  obtain ⟨epoch,erased,other⟩ := free_views receipt native
  intro id value cell
  have different : id ≠ receipt.skb := by
    intro same
    subst id
    rw [erased] at cell
    cases cell
  have before : PacketMaterial.view receipt.run.before.wg id = some value :=
    (other id different).symm.trans cell
  obtain ⟨oldGeneration,ticket,position,ordinal,time,origin,tracked⟩ := covered id value before
  refine ⟨oldGeneration,ticket,position,ordinal,epoch.trans time,origin,?_⟩
  rcases tracked with pending | ⟨outcome,debt,terminal⟩
  · exact Or.inl pending
  · refine Or.inr ⟨outcome,mem_forgetFreedCell.mpr ⟨debt,?_⟩,terminal⟩
    intro refers
    obtain ⟨_,otherOrigin⟩ := refers
    exact different (origin.unique otherOrigin).2.1

theorem DebtsResident.free (resident : DebtsResident history ledger debts receipt.run.before.wg)
    (native : (receipt : Terminal.Receipt).Valid)
    (atEpoch : Packets.epoch receipt.run.before.wg = some generation) :
    DebtsResident history ledger (forgetFreedCell history generation receipt.skb debts) receipt.run.after.wg := by
  obtain ⟨epoch,_,other⟩ := free_views receipt native
  intro debt member
  obtain ⟨old,notRefers⟩ := mem_forgetFreedCell.mp member
  obtain ⟨terminal,oldGeneration,id,value,origin,time,cell⟩ := resident debt old
  have sameEpoch : oldGeneration = generation := Option.some.inj (time.symm.trans atEpoch)
  subst oldGeneration
  have different : id ≠ receipt.skb := by
    intro same
    subst id
    exact notRefers ⟨value,origin⟩
  exact ⟨terminal,generation,id,value,origin,epoch.trans time,(other id different).trans cell⟩

/-- At a genuine native free, the no-pending-alias premise and converse
coverage force a corresponding terminal cleanup debt before any storage is
forgotten. The native reason/first-terminal certificate belongs to the caller. -/
theorem cleanup_covered (receipt : Terminal.Receipt) (native : receipt.Valid)
    (covered : Covered history ledger debts receipt.run.before.wg)
    (resident : Resident history ledger receipt.run.before.wg)
    (cleanup : DebtsResident history ledger debts receipt.run.before.wg)
    (unused : Unused history ledger receipt.run.before.wg receipt.skb)
    (epoch : Packets.epoch receipt.run.before.wg = some generation) :
    (∃ debt ∈ debts, (debt.ticket,Status.terminal debt.outcome) ∈ ledger ∧
      debt.Refers history generation receipt.skb) ∧
    Resident history ledger receipt.run.after.wg ∧
    Covered history ledger (forgetFreedCell history generation receipt.skb debts) receipt.run.after.wg ∧
    DebtsResident history ledger (forgetFreedCell history generation receipt.skb debts) receipt.run.after.wg := by
  obtain ⟨device,packet,atDevice,found,_⟩ := native.effects
  have cell : PacketMaterial.view receipt.run.before.wg receipt.skb = some (PacketMaterial.material packet) := by
    simp only [PacketMaterial.view,TxDisposition.txPackets,atDevice,Option.bind_some,found,Option.map_some]
  obtain ⟨debt,member,terminal,oldGeneration,time,origin⟩ := covered.requires_debt unused cell
  have sameEpoch : oldGeneration = generation := Option.some.inj (time.symm.trans epoch)
  subst oldGeneration
  exact ⟨⟨debt,member,terminal,_,origin⟩,resident.free native unused,
    covered.free native,cleanup.free native epoch⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
