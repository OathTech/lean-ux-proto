import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueueBounds

/-! Full semantic entry transport at the actual queue-admission components.
The native owner changes at install; the same ledger, birth links and earlier
terminal evidence travel through all four source components. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation QueueHandoff

theorem owned (before : Inv history ledger debts locals w.wg) :
    QueueHandoff.Owned ledger debts locals history w :=
  ⟨before.core,before.coverage,before.inventory⟩

theorem semantic {w v : World} (before : Inv history ledger debts locals w.wg) (suffix : List CausalJournal.Event)
    (atCut : QueueHandoff.Owned ledger debts next (history ++ suffix) v)
    (bounds : Packets.Inv v.wg) : Inv (history ++ suffix) ledger debts next v.wg :=
  ⟨atCut.1,before.justified.append suffix,before.allocationLinks.append suffix,before.noSelected,
    bounds,atCut.2.1,atCut.2.2⟩

theorem before_entry (pid : PeerId) (items : List SkbId)
    (before : Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (performed : runPrefix (focused (QueueHandoff.before pid items)) w history = (.ok (candidate,v),last)) :
    Inv last ledger debts (⟨.unpublished,pid,items⟩ :: locals) v.wg ∧
    ∀ p, candidate = some p → ∃ d, v.wg.dev = some d ∧ d.peers[pid]? = some p := by
  obtain ⟨atCut,cached⟩ := QueueHandoff.before_entry pid items (owned before) performed
  have bounds := focused_bounds (before_erases pid items) (before_bounds pid items) before.packets performed
  obtain ⟨suffix,extended,_⟩ := focused_quiet (QueueHandoff.before pid items) w history
  simp only [focused] at performed
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [extended] at atCut ⊢
  exact ⟨semantic before suffix atCut bounds,cached⟩

theorem install_entry (pid : PeerId) (p : Peer) (items : List SkbId)
    (device : w.wg.dev = some d) (found : d.peers[pid]? = some p)
    (before : Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    ∃ v writes,
      runPrefix (focused (install pid p items)) w history =
        (.ok ((),v),(history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ∧
      Inv ((history ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ledger debts locals v.wg := by
  obtain ⟨v,writes,performed,atCut⟩ := install_core pid p items device found (owned before)
  have bounds := focused_bounds (install_erases pid p items) (install_bounds pid p items) before.packets performed
  refine ⟨v,writes,performed,?_⟩
  have result := semantic before (writes ++ [CausalJournal.txEvent (.queued pid items)])
    (by simpa only [List.append_assoc] using atCut) bounds
  simpa only [List.append_assoc] using result

theorem after_entry (items : List SkbId) (before : Inv history ledger debts locals w.wg)
    (performed : runPrefix (focused (QueueHandoff.after items)) w history = (.ok (ret,v),last)) :
    Inv last ledger debts locals v.wg ∧ (ret = 0 ∨ ret = -WG.EPIPE) := by
  obtain ⟨atCut,code⟩ := QueueHandoff.after_entry items (owned before) performed
  have bounds := focused_bounds (after_erases items) (after_bounds items) before.packets performed
  obtain ⟨suffix,extended,_⟩ := focused_quiet (QueueHandoff.after items) w history
  simp only [focused] at performed
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [extended] at atCut ⊢
  exact ⟨semantic before suffix atCut bounds,code⟩

theorem offered_entry (items : List SkbId) (ret : Int) (before : Inv history ledger debts locals w.wg) :
    ∃ suffix, runPrefix (focused (offered items ret)) w history = (.ok (ret,w),history ++ suffix) ∧
      Inv (history ++ suffix) ledger debts locals w.wg := by
  obtain ⟨suffix,performed,atCut⟩ := offered_total items ret (owned before)
  exact ⟨suffix,performed,semantic before suffix atCut before.packets⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
