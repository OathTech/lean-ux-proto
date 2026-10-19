import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxBody

/-! Actual TX worker source transport with Entry and terminal completeness
on the same ledger. Normal paths retain their branch witness; stopped paths
retain the reached native cut and source run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open StagedEntry.CompleteCarrier StagedTerminalComplete TxWorker
open Staged.Obligations
set_option pp.structureInstances false

inductive TransmitStop (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | peek
      (entry : Accounted history ledger [] locals w.wg)
      (performed : runPrefix (TxSelection.peek pid) w history = (.error stop,last))
  | body (first : Option (List SkbId)) (u : World) (middle : List CausalJournal.Event)
      (peeked : runPrefix (TxSelection.peek pid) w history = (.ok (first,u),middle))
      (entry : Accounted middle ledger [] locals u.wg)
      (cached : ∀ p, peerAt u.wg pid = some p → p.txQueue.peeked = first)
      (frontier : BodyStop ledger locals pid first u middle stop last)

/-- The actual worker preserves paired accounting with no crypted callback
premise. Normal paths restore empty debts and exact caller locals. -/
theorem transmit_cases
    (pid : PeerId) (before : Accounted history ledger [] locals w.wg) :
    match (runPrefix (CausalJournal.transmit pid) w history).1 with
    | .error stop => TransmitStop ledger locals pid w history stop
        (runPrefix (CausalJournal.transmit pid) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (CausalJournal.transmit pid) w history).2 v := by
  have paired := peek_complete pid before.complete w
  rw [TxWorker.transmit_factor,runPrefix_bind]
  cases peeked : runPrefix (TxSelection.peek pid) w history with
  | mk outcome middle =>
    rw [peeked] at paired
    cases outcome with
    | error stop => exact .peek before peeked
    | ok out =>
      obtain ⟨first,u⟩ := out
      simp only []
      obtain ⟨entry,cached,_⟩ := TxSelection.peek_entry pid before.entry peeked
      have entry : Accounted middle ledger [] locals u.wg := ⟨entry,paired⟩
      have result := body_cases pid first entry cached
      cases performed : runPrefix (TxWorker.body pid first) u middle with
      | mk final last =>
        rw [performed] at result
        cases final with
        | error stop => exact .body first u middle peeked entry cached result
        | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
