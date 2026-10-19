import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionHistory

/-! Disposal receipts do not invent queued-work or timer selection evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem disposal_history (body : WGPrefix HandshakeSecurity.StagedDisposal.Event α) :
    Driver.StateHistorySafe Safe (focusStatePrefix Event.stagedDisposal stagedDisposal? body) := by
  intro w a h hi
  let suffix := ((runWGPrefix body w a (h.filterMap stagedDisposal?)).2.drop
    (h.filterMap stagedDisposal?).length).map Event.stagedDisposal
  have good : Safe (h ++ suffix) := hi.quiet (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    trivial)
  refine ⟨suffix,rfl,good,?_⟩
  cases (runPrefix (StateT.run (focusStatePrefix Event.stagedDisposal stagedDisposal? body) w) a h).1 <;> trivial

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
