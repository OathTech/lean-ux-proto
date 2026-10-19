import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCoverage

/-! Projection and history frames for physical obligation coverage. Backward
survivor transport permits actual frees in Covered; the separate Resident and
DebtsResident carriers prevent silent loss of pending or cleanup obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations

theorem Covered.append (covered : Covered history ledger debts w)
    (suffix : List CausalJournal.Event) : Covered (history ++ suffix) ledger debts w := by
  intro id value cell
  obtain ⟨generation,ticket,position,ordinal,epoch,origin,tracked⟩ := covered id value cell
  exact ⟨generation,ticket,position,ordinal,epoch,origin.append suffix,tracked⟩

theorem DebtsResident.append (resident : DebtsResident history ledger debts w)
    (suffix : List CausalJournal.Event) : DebtsResident (history ++ suffix) ledger debts w := by
  intro debt member
  obtain ⟨terminal,backed⟩ := resident debt member
  exact ⟨terminal,backed.append suffix⟩

theorem Covered.retains (covered : Covered history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : ∀ id value, PacketMaterial.view v id = some value →
      PacketMaterial.view w id = some value) : Covered history ledger debts v := by
  intro id value cell
  obtain ⟨generation,ticket,position,ordinal,time,origin,tracked⟩ := covered id value (cells id value cell)
  exact ⟨generation,ticket,position,ordinal,epoch.trans time,origin,tracked⟩

theorem Covered.views (covered : Covered history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : Covered history ledger debts v :=
  covered.retains epoch (fun id _ cell => (congrFun cells id).symm.trans cell)

theorem DebtsResident.views (resident : DebtsResident history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : DebtsResident history ledger debts v := by
  intro debt member
  obtain ⟨terminal,backed⟩ := resident debt member
  exact ⟨terminal,backed.views epoch cells⟩

/-- The ordinary native frame can be used under any observer whose separate
history proof identifies its actual appended suffix. -/
theorem covered_native {action : WG.M α}
    (epoch : Leanux.Proofs.Framing.SameView Packets.epoch action)
    (material : Leanux.Proofs.Framing.SameView PacketMaterial.view action) :
    Leanux.Proofs.Framing.Preserves (Covered history ledger debts) action := by
  apply (Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b covered run
  exact covered.views
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp material w a value v b run)

/-- Exact ordinary native material frames preserve all three directions:
pending backing, converse live-cell coverage, and terminal cleanup backing. -/
theorem physical_native {action : WG.M α}
    (epoch : Leanux.Proofs.Framing.SameView Packets.epoch action)
    (material : Leanux.Proofs.Framing.SameView PacketMaterial.view action) :
    Leanux.Proofs.Framing.Preserves
      (fun w => Resident history ledger w ∧ Covered history ledger debts w ∧
        DebtsResident history ledger debts w) action := by
  apply (Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have time := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run
  have cells := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp material w a value v b run
  refine ⟨?_,before.2.1.views time cells,before.2.2.views time cells⟩
  intro ticket position ordinal member
  exact (before.1 ticket position ordinal member).views time cells

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
