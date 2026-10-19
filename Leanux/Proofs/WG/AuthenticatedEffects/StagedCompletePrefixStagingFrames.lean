import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingSelection

/-! Selected nonce prefixes retain the actual take anchor, ledger and receipt
meaning. Only the explicitly observed progress events may use this extension. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation

theorem active_append (before : CompleteSelected.Active ledger debts generation pid peer position h)
    (allowed : ∀ event∈suffix, HeldFrontier.progress event=true) :
    CompleteSelected.Active ledger debts generation pid peer position (h++suffix) :=
  ⟨⟨before.1.1.append allowed,before.1.2.1.append suffix,before.1.2.2.1.append suffix,before.1.2.2.2⟩,
    before.2.1.append_quiet (fun event member=>CompleteSelected.progress_terminal_quiet (allowed event member)),
    before.2.2.append suffix⟩

theorem progress_cuts (before : CompleteSelected.Active ledger debts generation pid peer position h)
    (allowed : ∀ event∈suffix, HeldFrontier.progress event=true) :
    Cuts CompleteProduct.Safe h suffix := by
  intro n _
  exact ⟨debts,.selected ledger generation pid peer position _
    (active_append before (fun event member=>allowed event (List.mem_of_mem_take member)))⟩

theorem selected_native {action : WG.M α}
    (endpoint : StatePrefixPreserves
      (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (liftWGPrefix action)) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (liftWGPrefix action)
      (fun _=>CompleteSelected.Ready ledger debts locals generation pid peer position) :=
  single endpoint (fun _ _ _ before=>ready_safe before) (fun _ _ _ _=>Or.inl rfl)

theorem reserve (kid : KeypairId) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (state (Journal.reserve kid))
      (fun _=>CompleteSelected.Ready ledger debts locals generation pid peer position) := by
  apply StateEnsures.of_cuts (CompleteSelected.reserve
    (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) kid)
  intro w a h before
  have frame : StateHistoryFrame HeldFrontier.blocking? (state (Journal.reserve kid)) := by
    apply Staged.Origins.focused_history_frame _ _ HeldFrontier.blocking? _ ((StateAppends.focus _ _ _).receiptWGObserved _)
    exact StateHistoryFrame.receiptWGObserved
      (fun w=>focusPrefix_other _ _ _ (fun _=>rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _=>rfl)
  obtain ⟨suffix,extended⟩ := StateAppends.focus _ _ _ w a h
  exact ⟨suffix,extended,progress_cuts before.active (HeldFrontier.suffix_progress frame extended)⟩

/-- A truly silent history frame upgrades a source contract without inferring
anything about internal native worlds. -/
theorem silent {P : List Event→WGWorld→Ambient→Prop} {Safe : List Event→Prop}
    {Q : α→List Event→WGWorld→Ambient→Prop} {body : WGPrefix Event α}
    (endpoint : StatePrefixEnsures P Safe body Q)
    (initial : ∀ h w a,P h w a→Safe h)
    (history : ∀ (Good : List Event→Prop), Driver.StateHistorySafe Good body) :
    StateEnsures P Safe body Q := by
  apply single endpoint initial
  intro w a h _
  obtain ⟨_,_,same,_⟩ := history (fun out=>out=h) w a h rfl
  exact Or.inl same

theorem before_restore_history (Good : List Event→Prop)
    (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    Driver.StateHistorySafe Good (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) : Driver.StateHistorySafe Good (do
      liftWGPrefix (keypairPut kp false)
      for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
      _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply Driver.History.state_bind (Driver.History.state_lift _)
    intro _
    apply Driver.History.state_bind
    · apply Driver.History.state_forIn
      intro packet acc
      exact Driver.History.state_bind (Driver.History.state_lift _) (fun _=>Driver.History.state_pure _)
    · intro _
      exact Driver.History.state_bind (Driver.History.state_lift _) (fun _=>Driver.History.state_pure _)
  unfold RestoreEntry.prefixWith
  dsimp only
  split
  · split
    · exact Driver.History.state_bind (Driver.History.state_lift _) (fun _=>
        Driver.History.state_bind (Driver.History.state_lift _) (fun _=>tail _))
    · exact Driver.History.state_bind (Driver.History.state_lift _) (fun _=>tail _)
  · exact tail _

theorem before_restore (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid)
      (fun _=>CompleteSelected.Ready ledger debts locals generation pid peer position) :=
  silent (CompleteSelected.before_restore
    (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩) packets keypair invalid)
    (fun _ _ _ before=>ready_safe before) (fun Good=>before_restore_history Good packets keypair invalid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
