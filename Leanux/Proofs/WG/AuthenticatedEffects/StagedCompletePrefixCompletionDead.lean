import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionCrypted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingCreateLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxDispatch

/-! The DEAD branch retains every logical output prefix through the actual
labelled frees and key/peer repayments, alongside its original source frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedConservation

theorem global_account_safe : AccountSafe CompleteProduct.Safe :=
  fun h ledger debts locals w before => ⟨debts,.accounted ledger locals h w before⟩

theorem ledger_quiet (action : PrefixM CausalJournal.Event α)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action)
    (accountSafe : AccountSafe Safe)
    (before : CompleteCarrier.Accounted history ledger debts locals w.wg)
    (earlier : All Safe history) : All Safe (runPrefix action w history).2 := by
  obtain ⟨suffix,grown⟩ := appends w history
  have paired := Converse.history_preserved before.complete appends quiet (w := w)
  rw [grown] at paired ⊢
  exact earlier.append (FixedHistory.cuts Safe (fun l h g => accountSafe h l _ _ g) before
    (ledger_history_birth_free quiet w history suffix grown) paired)

theorem dead_repay (pid : PeerId) (key : KeypairId)
    (accountSafe : AccountSafe Safe)
    (before : CompleteCarrier.Accounted history ledger debts locals w.wg)
    (earlier : All Safe history) : All Safe (runPrefix (DeadEntry.repay pid key) w history).2 := by
  have keyPrefix := ledger_quiet (Admission.actualOps.access (keypairPutPrefix (some key) false))
    (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _) accountSafe before earlier
  have keyComplete : Complete (runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history).2 ledger :=
    Converse.history_preserved before.complete (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _) (w := w)
  unfold DeadEntry.repay
  rw [runPrefix_bind]
  cases performed : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history with
  | mk outcome middle =>
    rw [performed] at keyPrefix keyComplete
    cases outcome with
    | error stop => exact keyPrefix
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      have atPeer : CompleteCarrier.Accounted middle ledger debts locals u.wg :=
        ⟨DeadEntry.key_entry key before.entry performed,keyComplete⟩
      obtain ⟨suffix,grown,cuts⟩ := Disposal.nested_cuts (some pid) Safe
        (fun l h g => accountSafe h l _ _ g) u middle ⟨ledger,atPeer⟩
      have allPeer := keyPrefix.append cuts
      simp only []
      rw [runPrefix_bind]
      cases released : runPrefix (Admission.actualOps.release (some pid)) u middle with
      | mk outcome last =>
        rw [released] at grown
        rw [← grown] at allPeer
        cases outcome with
        | error stop => exact allPeer
        | ok out => exact allPeer

theorem dead (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : CompleteCarrier.Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : CreateDisposal.PendingBatch history ledger items)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2 ∧
      match (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).1 with
      | .error reason => Converse.Dead.Stopped ledger debts locals pid items head w history reason
          (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
            CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2
      | .ok (value,v) => Converse.Dead.Returned ledger debts locals pid items head w history
          (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
            CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2 value v := by
  refine ⟨?_,Converse.Dead.dead_cases pid items head before pending⟩
  rw [DeadEntry.dead_factor,runPrefix_bind]
  obtain ⟨u,suffix,after,freed,cuts,_,accounted⟩ :=
    Staging.Creation.free_loop_cuts (.deadBatch pid head) .selected items before pending
  rw [freed]
  exact dead_repay pid head.keypair global_account_safe accounted (earlier.append cuts)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
