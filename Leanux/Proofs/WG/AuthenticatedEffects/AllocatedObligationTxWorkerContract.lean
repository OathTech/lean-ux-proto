import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxBodyContract

/-! Complete actual TX worker composition at an idle debt-free entry. The
sole remaining callback is crypted completion. No completed enclosing
caller is required to retain ownership at a stopped worker prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations
set_option pp.structureInstances false

inductive TransmitStop (failed : CryptFailure) (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | peek
      (entry : StagedEntry.Inv history ledger [] locals w.wg)
      (performed : runPrefix (TxSelection.peek pid) w history = (.error stop,last))
  | body (first : Option (List SkbId)) (u : World) (middle : List CausalJournal.Event)
      (peeked : runPrefix (TxSelection.peek pid) w history = (.ok (first,u),middle))
      (entry : StagedEntry.Inv middle ledger [] locals u.wg)
      (cached : ∀ p, peerAt u.wg pid = some p → p.txQueue.peeked = first)
      (frontier : BodyStop failed ledger locals pid first u middle stop last)

/-- The actual TX worker transfers each selected queue occurrence to its
original crypted or DEAD disposal path. From a debt-free idle entry, normal
return restores the caller's exact locals and empty debts; a stopped run
retains the reached source cut and its full indexed ownership. Crypted
completion is the sole explicit callback obligation. -/
theorem transmit_cases (failed : CryptFailure) (completed : CryptContract failed)
    (pid : PeerId) (before : StagedEntry.Inv history ledger [] locals w.wg) :
    match (runPrefix (CausalJournal.transmit pid) w history).1 with
    | .error stop => TransmitStop failed ledger locals pid w history stop
        (runPrefix (CausalJournal.transmit pid) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (CausalJournal.transmit pid) w history).2 v := by
  rw [transmit_factor,runPrefix_bind]
  cases peeked : runPrefix (TxSelection.peek pid) w history with
  | mk outcome middle =>
    cases outcome with
    | error stop => exact .peek before peeked
    | ok out =>
      obtain ⟨first,u⟩ := out
      simp only []
      obtain ⟨entry,cached,_⟩ := TxSelection.peek_entry pid before peeked
      have result := body_cases failed completed pid first entry cached
      cases performed : runPrefix (body pid first) u middle with
      | mk final last =>
        rw [performed] at result
        cases final with
        | error stop => exact .body first u middle peeked entry cached result
        | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
