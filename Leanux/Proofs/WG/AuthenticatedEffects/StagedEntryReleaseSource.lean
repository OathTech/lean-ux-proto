import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRelease

/-! Complete actual nested release, including the counted erase followed by
a stopped timer check. A stopped result carries its reached physical owner
cut and exact source execution; provenance alone is never substituted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Release
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations AllocatedObligation PeerRelease
set_option pp.structureInstances false

inductive Frontier (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (owned : Inv history ledger debts locals w.wg)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error stop,last))
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (a : Ambient)
      (cutHistory : List CausalJournal.Event) (after : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory))
      (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
      (settlement : Successor value w.wg cutHistory.length ledger after)
      (owned : Inv (cutHistory ++ [receipt peer value w.wg g w.ambient a]) after debts locals g)
      (failed : runPrefix (finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) = (.error stop,last))

def Returned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (last : List CausalJournal.Event) (v : World) : Prop :=
  ∃ value g a cutHistory after,
    runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory) ∧
    last = cutHistory ++ [receipt peer value w.wg g w.ambient a] ∧
    Staged.Obligations.Step ledger after ∧ AllocatedFrame ledger after ∧
    Successor value w.wg cutHistory.length ledger after ∧
    Inv last after debts locals v.wg

/-- Every actual nested peer release either returns the precisely settled
fixed ledger or retains its real failed cut/continuation and physical owner
state. No completed enclosing create or completion callback is assumed. -/
theorem actual_cases (peer : Option PeerId)
    (owned : Inv history ledger debts locals w.wg) :
    match (runPrefix (Admission.actualOps.release peer) w history).1 with
    | .error stop => Frontier ledger debts locals peer w history stop
        (runPrefix (Admission.actualOps.release peer) w history).2
    | .ok ((),v) => Returned ledger debts locals peer w history
        (runPrefix (Admission.actualOps.release peer) w history).2 v := by
  rw [actual_run]
  cases performed : runWGPrefix (cut peer) w.wg w.ambient history with
  | mk outcome cutHistory =>
    cases outcome with
    | error stop => exact .cutStopped owned performed
    | ok out =>
      obtain ⟨⟨value,g⟩,a⟩ := out
      obtain ⟨after,step,frame,settlement,atCut⟩ := cut_entry peer owned performed
      simp only []
      cases suffix : runPrefix (finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) with
      | mk outcome last =>
        cases outcome with
        | error stop => exact .finishStopped value g a cutHistory after performed step frame settlement atCut suffix
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          obtain ⟨hist,final⟩ := finish_entry value atCut suffix
          exact ⟨value,g,a,cutHistory,after,performed,hist,step,frame,settlement,final⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Release
