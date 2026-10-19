import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntrySource

/-! The full create contract at the shared driver's WG callback. The pending
batch premise belongs to the actual preceding allocation, while stopped
frontiers remain explicit inputs to the caller's global history certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

/-- The real shared create callback consumes the unpublished local and returns
the same caller debts, or exports its actual stopped source frontier. Incoming
pending-ticket assignment is explicit and must be derived at allocation. -/
theorem checked (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (Safe : List CausalJournal.Event → Prop)
    (stopSafe : ∀ w h stop last, CreatedStop ledger debts locals pid items w h stop last → Safe last)
    (entrySafe : ∀ afterLedger h w, StagedEntry.Inv h afterLedger debts locals w → Safe h)
    (Post : List CausalJournal.Event → WGWorld → Ambient → Prop)
    (entryPost : ∀ afterLedger h w a, StagedEntry.Inv h afterLedger debts locals w → Post h w a) :
    StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w ∧
        PendingBatch h ledger items)
      Safe (CausalJournal.create pid items) (fun _ => Post) := by
  intro w a history before
  have result := create_cases pid items (w := NativeAdapter.world w a) before.1 before.2
  obtain ⟨suffix,extended⟩ := (CausalJournal.CallbackQuiet.create (fun _ => (none : Option Unit))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items).1 w a history
  refine ⟨suffix,extended,?_⟩
  have lowered := NativeAdapter.run_lower
    (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w a history
  change runPrefix ((CausalJournal.create pid items).run w) a history = _ at lowered
  rw [lowered]
  cases performed : runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items)
      (NativeAdapter.world w a) history with
  | mk outcome last =>
    rw [performed] at result
    cases outcome with
    | error stop => exact ⟨stopSafe _ _ _ _ result,True.intro⟩
    | ok out =>
      obtain ⟨ignored,v⟩ := out
      cases ignored
      obtain ⟨first,ret,u,middle,afterLedger,_,_,_,entry,_⟩ := result
      exact ⟨entrySafe _ _ _ entry,entryPost _ _ _ _ entry⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
