import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFinishFrames

/-! Complete actual nested release, including the counted erase followed by
a stopped timer check. A stopped result carries its reached physical owner
cut and exact source execution; provenance alone is never substituted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations QueueHandoff
set_option pp.structureInstances false

inductive Frontier (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (peer : Option PeerId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | cutStopped
      (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg)
      (failed : runWGPrefix (cut peer) w.wg w.ambient history = (.error stop,last))
  | finishStopped (value : Option (PeerId × Peer)) (g : WGWorld) (a : Ambient)
      (cutHistory : List CausalJournal.Event) (after : Ledger)
      (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),a),cutHistory))
      (step : Staged.Obligations.Step ledger after) (frame : AllocatedFrame ledger after)
      (settlement : Successor value w.wg cutHistory.length ledger after)
      (owned : Owned after debts locals (cutHistory ++ [receipt peer value w.wg g w.ambient a])
        {w with wg := g,ambient := a}) (bounded : Packets.Inv g)
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
    Owned after debts locals last v ∧ Packets.Inv v.wg

/-- Every actual nested peer release either returns the precisely settled
fixed ledger or retains its real failed cut/continuation and physical owner
state. No completed enclosing create or completion callback is assumed. -/
theorem actual_cases (peer : Option PeerId)
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg) :
    match (runPrefix (Admission.actualOps.release peer) w history).1 with
    | .error stop => Frontier ledger debts locals peer w history stop
        (runPrefix (Admission.actualOps.release peer) w history).2
    | .ok ((),v) => Returned ledger debts locals peer w history
        (runPrefix (Admission.actualOps.release peer) w history).2 v := by
  rw [actual_run]
  cases performed : runWGPrefix (cut peer) w.wg w.ambient history with
  | mk outcome cutHistory =>
    cases outcome with
    | error stop => exact .cutStopped owned bounded performed
    | ok out =>
      obtain ⟨⟨value,g⟩,a⟩ := out
      obtain ⟨after,step,frame,settlement,atCut,bounds⟩ := cut_owned peer owned bounded performed
      simp only []
      cases suffix : runPrefix (finish value) {w with wg := g,ambient := a}
        (cutHistory ++ [receipt peer value w.wg g w.ambient a]) with
      | mk outcome last =>
        cases outcome with
        | error stop => exact .finishStopped value g a cutHistory after performed step frame settlement atCut bounds suffix
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          obtain ⟨hist,final,bounds⟩ := finish_returned value atCut bounds suffix
          exact ⟨value,g,a,cutHistory,after,performed,hist,step,frame,settlement,final,bounds⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
