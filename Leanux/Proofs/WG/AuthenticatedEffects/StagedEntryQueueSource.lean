import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueue

/-! Result-aware ownership at the actual enqueue source. A failure names its
real source component and a reached owned cut. The unpublished local is
consumed only by the queue write. Neither error branch substitutes history
provenance for ownership or invents a final World after Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation QueueHandoff
set_option pp.structureInstances false

inductive EnqueueFrontier (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (w : World) (history : List CausalJournal.Event) (stop : Stop)
    (last : List CausalJournal.Event) : Prop where
  | beforeStopped
      (entry : Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
      (failed : runPrefix (focused (QueueHandoff.before pid items)) w history = (.error stop,last))
  | queuedStopped (p : Peer) (u v : World) (readHistory writes : List CausalJournal.Event)
      (read : runPrefix (focused (QueueHandoff.before pid items)) w history = (.ok (some p,u),readHistory))
      (installed : runPrefix (focused (install pid p items)) u readHistory =
        (.ok ((),v),(readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]))
      (owned : Inv ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) ledger debts locals v.wg)
      (failed : runPrefix (focused (QueueHandoff.after items)) v
        ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) = (.error stop,last))

def EnqueueReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (ret : Int) (history : List CausalJournal.Event) (w : World) : Prop :=
  (ret = -WG.ENOSPC ∧ Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) ∨
    ((ret = 0 ∨ ret = -WG.EPIPE) ∧ Inv history ledger debts locals w.wg)

/-- Every result of the actual queue-admission source has either its returned
phase or an exact stopped source frontier, over the same fixed canonical
ledger. No completed enclosing createData call is required. -/
theorem enqueue_cases (pid : PeerId) (items : List SkbId)
    (owned : Inv history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    match (runPrefix (Admission.actualOps.enqueue pid items) w history).1 with
    | .error stop => EnqueueFrontier ledger debts locals pid items w history stop
        (runPrefix (Admission.actualOps.enqueue pid items) w history).2
    | .ok (ret,v) => EnqueueReturned ledger debts locals pid items ret
        (runPrefix (Admission.actualOps.enqueue pid items) w history).2 v := by
  rw [actual_enqueue]
  simp only [enqueueFocused,runPrefix_bind]
  cases read : runPrefix (focused (QueueHandoff.before pid items)) w history with
  | mk result readHistory =>
    cases result with
    | error stop => exact .beforeStopped owned read
    | ok out =>
      obtain ⟨candidate,u⟩ := out
      obtain ⟨kept,cached⟩ := before_entry pid items owned read
      cases candidate with
      | none =>
        simp only [runPrefix_pure]
        obtain ⟨suffix,done,final⟩ := offered_entry items (-WG.ENOSPC) kept
        rw [done]
        exact Or.inl ⟨rfl,final⟩
      | some p =>
        obtain ⟨d,device,found⟩ := cached p rfl
        obtain ⟨v,writes,installed,atCut⟩ := install_entry pid p items device found kept
        change runPrefix (focused (install pid p items)) u readHistory = _ at installed
        simp only [runPrefix_bind,installed]
        cases tail : runPrefix (focused (QueueHandoff.after items)) v
          ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]) with
        | mk outcome tailHistory =>
          cases outcome with
          | error stop => exact .queuedStopped p u v readHistory writes read installed atCut tail
          | ok out =>
            obtain ⟨ret,lastWorld⟩ := out
            obtain ⟨atReturn,code⟩ := after_entry items atCut tail
            obtain ⟨suffix,done,final⟩ := offered_entry items ret atReturn
            simp only
            rw [done]
            exact Or.inr ⟨code,final⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
