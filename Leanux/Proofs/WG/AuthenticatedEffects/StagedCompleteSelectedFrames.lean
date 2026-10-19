import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelected
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyRestore
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyAllocation

/-! Native selected-state transport and independent terminal-quiet history
transport are paired on one ledger. These frames do not apply to consuming
callbacks such as final peer release, allocation or counted disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedTerminalComplete CompleteCarrier

theorem progress_terminal_quiet (allowed : HeldFrontier.progress event = true) :
    StagedTerminalComplete.Quiet event := by
  cases event <;> try { cases allowed } <;> try { intro position; rfl }
  case old event =>
    cases event <;> try { cases allowed } <;> intro position <;> rfl

theorem reserve_history (kid : KeypairId) :
    Driver.StateHistorySafe (fun h => Complete h ledger) (state (Journal.reserve kid)) := by
  have quiet : StateHistoryFrame HeldFrontier.blocking? (state (Journal.reserve kid)) := by
    apply Staged.Origins.focused_history_frame _ _ HeldFrontier.blocking? _ ((StateAppends.focus _ _ _).receiptWGObserved _)
    exact StateHistoryFrame.receiptWGObserved
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl)
  intro w a h before
  obtain ⟨suffix,extended⟩ := StateAppends.focus _ _ _ w a h
  change (runPrefix ((state (Journal.reserve kid)).run w) a h).2 = h ++ suffix at extended
  have allowed := HeldFrontier.suffix_progress quiet extended
  have complete : Complete (runPrefix ((state (Journal.reserve kid)).run w) a h).2 ledger := by
    rw [extended]
    exact before.append_quiet (fun event member => progress_terminal_quiet (allowed event member))
  refine ⟨suffix,extended,complete,?_⟩
  cases result : (runPrefix ((state (Journal.reserve kid)).run w) a h).1 with
  | error stop => trivial
  | ok out => exact complete

theorem decorate {action : WGPrefix Event α} {Safe : List Event → Prop}
    (rule : StatePrefixPreserves (ReadyCarrier.Ready ledger debts locals generation pid peer position)
      (SoundHeld.Active ledger debts generation pid peer position) action)
    (history : Driver.StateHistorySafe (fun h => Complete h ledger) action)
    (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,active,post⟩ := rule w a h before.toReady
  obtain ⟨_,_,complete,_⟩ := history w a h before.complete
  have anchor : NativeAnchor position (runPrefix (action.run w) a h).2 := by
    rw [extended]
    exact before.nativeAnchor.append suffix
  refine ⟨suffix,extended,frontier _ ⟨active,complete,anchor⟩,?_⟩
  cases result : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using post,complete,anchor⟩

variable {Safe : List Event → Prop}
variable (frontier : ∀ h, Active ledger debts generation pid peer position h → Safe h)

include frontier in
theorem ambient (action : AmbientM α) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe
      (liftWGPrefix (monadLift action : WG.M α)) :=
  decorate (ReadyCarrier.ambient (fun _ => id) action) (Driver.History.state_lift _) frontier

include frontier in
theorem world (action : WG.M α) (same : SameView id action) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix action) :=
  decorate (ReadyCarrier.world (fun _ => id) action same) (Driver.History.state_lift _) frontier

include frontier in
theorem read_key (kid : KeypairId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix (getKeypair kid)) :=
  decorate (ReadyCarrier.read_key (fun _ => id) kid) (Driver.History.state_lift _) frontier

include frontier in
theorem reserve (kid : KeypairId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (state (Journal.reserve kid)) :=
  decorate (ReadyCarrier.reserve (fun _ => id) kid) (reserve_history kid) frontier

include frontier in
theorem acquire_peer (owner : PeerId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix (peerGet owner)) :=
  decorate (ReadyCarrier.acquire_peer (fun _ => id) owner) (Driver.History.state_lift _) frontier

theorem prefix_history (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    Driver.StateHistorySafe (fun h => Complete h ledger)
      (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) : Driver.StateHistorySafe (fun h => Complete h ledger) (do
      liftWGPrefix (keypairPut kp false)
      for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
      _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply Driver.History.state_bind (Driver.History.state_lift _)
    intro _
    apply Driver.History.state_bind
    · apply Driver.History.state_forIn
      intro packet acc
      exact Driver.History.state_bind (Driver.History.state_lift _)
        (fun _ => Driver.History.state_pure _)
    · intro _
      exact Driver.History.state_bind (Driver.History.state_lift _)
        (fun _ => Driver.History.state_pure _)
  unfold RestoreEntry.prefixWith
  dsimp only
  split
  · split
    · exact Driver.History.state_bind (Driver.History.state_lift _) (fun _ =>
        Driver.History.state_bind (Driver.History.state_lift _) (fun _ => tail _))
    · exact Driver.History.state_bind (Driver.History.state_lift _) (fun _ => tail _)
  · exact tail _

include frontier in
theorem before_restore (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe
      (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) :=
  decorate (ReadyCarrier.before_restore (fun _ => id) packets keypair invalid)
    (prefix_history packets keypair invalid) frontier

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
