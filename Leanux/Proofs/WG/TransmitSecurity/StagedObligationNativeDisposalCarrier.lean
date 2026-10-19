import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalMaterialFrames

/-! Named native purge/overflow receipts transport the canonical fixed ledger,
with their actual counter increments and unchanged allocated-cell material. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Staged.Origins
open AuthenticatedEffects CausalJournal

/-- Whole native purge settles the exact staged prefix (the entire queue)
under its own counted arm and retains every other ledger component. -/
theorem core_purge (pid : PeerId) (r : WGRunWitness Unit)
    (native : r.Valid (purgeStagedPackets pid)) (before : Core history ledger debts r.before) :
    ∃ (p : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after) (generation : Nat),
      p.removed = p.packets.length ∧ Packets.epoch r.before = some generation ∧
      let selected := (pendingAt (.staged generation pid p.stamp) ledger).take p.removed
      let after := settle selected (.counted history.length .purge) ledger
      Step ledger after ∧ Core (history ++ [.stagedDisposal (.purge pid r)]) after debts r.after ∧
        selected.length = p.removed ∧
        (∀ ticket ∈ selected, (ticket,Status.terminal (.counted history.length .purge)) ∈ after) ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+selected.length)) := by
  obtain ⟨p,whole⟩ := HandshakeSecurity.StagedDisposal.purge_exact pid r native
  obtain ⟨d,_,device,_,_⟩ := Staged.purge pid r native
  have epoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
  have cells := (ProjectedAction.iff_run_ambient _ _ _).mp (purge_packet_material pid)
    r.before r.ambientBefore r.value r.after r.ambientAfter native
  exact ⟨p,d.ifindex,whole,epoch,core_counted p before epoch _ rfl .purge cells⟩

/-- Native overflow settles exactly its counted removed prefix at the actual
receipt position. The retained suffix and all allocated cleanup debts survive. -/
theorem core_overflow (pid : PeerId) (r : WGRunWitness Unit)
    (native : r.Valid (xmitTrim pid)) (before : Core history ledger debts r.before) :
    ∃ (p : HandshakeSecurity.StagedDisposal.Partition pid r.before r.after) (generation : Nat),
      Packets.epoch r.before = some generation ∧
      let selected := (pendingAt (.staged generation pid p.stamp) ledger).take p.removed
      let after := settle selected (.counted history.length .overflow) ledger
      Step ledger after ∧ Core (history ++ [.stagedDisposal (.overflow pid r)]) after debts r.after ∧
        selected.length = p.removed ∧
        (∀ ticket ∈ selected, (ticket,Status.terminal (.counted history.length .overflow)) ∈ after) ∧
        (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+selected.length)) := by
  obtain ⟨p⟩ := HandshakeSecurity.StagedDisposal.overflow_exact pid r native
  cases device : r.before.dev with
  | none =>
    have present := p.before
    simp [stagedAt,device] at present
  | some d =>
    have epoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
    have cells := (ProjectedAction.iff_run_ambient _ _ _).mp (trim_packet_material pid)
      r.before r.ambientBefore r.value r.after r.ambientAfter native
    exact ⟨p,d.ifindex,epoch,core_counted p before epoch _ rfl .overflow cells⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
