import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseAcquire
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueued

/-! Rejection retains selected ownership through invalidation, repayment and
the original finite orphan walk. Restoration records the same ordered
cohort before queued initiation. The latter is a named child with its actual
paired nonfinal repayment trace, not a blanket release-quiet premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points CompleteCarrier HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem covers_transport {left right : WGPrefix Event α} (same : left=right) (shape : Shape left) :
    Covers E (same ▸ shape) w a h=Covers E shape w a h := by
  cases same
  rfl

theorem list_covers (xs : List α) (initial : σ) (body : α → σ → WGPrefix Event (ForInStep σ))
    (shapes : ∀ value acc,Shape (body value acc))
    (keeps : ∀ value acc h w a,E h w a → Covers E (shapes value acc) w a h)
    (before : E h w a) : Covers E (listShape xs initial body shapes) w a h := by
  induction xs generalizing initial h w a with
  | nil=>exact before
  | cons value rest ih=>
    change Covers E ((List.forIn_cons body value rest initial).symm ▸
      Shape.bind (shapes value initial) (fun next=>match next with
        | .done final=>.pure final
        | .yield acc=>listShape rest acc body shapes)) w a h
    rw [covers_transport]
    have first:=keeps value initial h w a before
    apply covers_bind first
    intro next u b middle run
    cases next with
    | done final=>exact first.normal run
    | yield acc=>exact ih acc (first.normal run)

theorem orphan_covers (packets : List Packet)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (orphanShape packets) w a h := by
  unfold orphanShape
  have first:=list_covers packets PUnit.unit _
    (fun _ _=>Shape.bind (.native (.branch .stagedOrphanWalk true)) (fun _=>.pure (.yield PUnit.unit)))
    (fun _ _ _ _ _ ready=>by
      have branch:=selected_ambient (.branch .stagedOrphanWalk true) _ rfl ready
      exact covers_bind branch (fun _ _ _ _ run=>branch.normal run)) before
  apply covers_bind first
  intro ignored u b middle run
  have last:=selected_ambient (.branch .stagedOrphanWalk false) _ rfl (first.normal run)
  exact covers_bind last (fun _ _ _ _ final=>last.normal final)

theorem reject_prefix_covers (packets : List Packet) (key : Option KeypairId) (invalid : Bool)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (rejectPrefixShape packets key invalid) w a h := by
  have tail (kp : Option KeypairId) h w a
      (ready : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
      Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
        (.bind (.child (.repayment kp)) (fun _=>orphanShape packets)) w a h :=
    covers_bind (selected_put_key kp ready) (fun _ _ _ _ run=>orphan_covers packets ((selected_put_key kp ready).normal run))
  unfold rejectPrefixShape
  cases invalid <;> dsimp only
  · exact tail key _ _ _ before
  · cases key with
    | none=>
      have failed:=invariant_covers (α:=Unit) before
      exact covers_bind failed (fun _ _ _ _ run=>tail none _ _ _ (failed.normal run))
    | some kid=>
      have read:=selected_key kid before
      apply covers_bind read
      intro key u b middle found
      have write:=selected_write_key kid {key with sending:={key.sending with isValid:=false}} (read.normal found)
      exact covers_bind write (fun _ _ _ _ run=>tail (some kid) _ _ _ (write.normal run))

theorem queued_same_account (before : Accounted h ledger debts locals w)
    (run : runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
      w a h=(.ok (((),v),b),last)) : Accounted last ledger debts locals v := by
  obtain ⟨entry,trace⟩:=Queued.normal pid before.entry a b run
  refine ⟨entry,?_⟩
  cases trace with
  | idle=>exact before.complete
  | repaid=>exact before.complete.append_quiet (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)
  | queued=>exact before.complete.append_quiet (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)

theorem queued_covers (before : Accounted h ledger debts locals w)
    (steps : Staged.Obligations.Step root ledger) (pid : PeerId) (a : Ambient) :
    Covers (Evidence root debts locals) (.child (.queued pid)) w a h := by
  refine ⟨.accounted ledger steps before,?_⟩
  intro value v b last run
  cases value
  exact .accounted ledger steps (queued_same_account before run)

theorem rejected_covers (key : Option KeypairId) (invalid : Bool)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (steps : Staged.Obligations.Step root ledger) :
    Covers (Evidence root debts locals) (rejectedShape pid peer key invalid) w a h := by
  unfold rejectedShape
  dsimp only [Covers,id]
  erw [covers_mpr (Staging.Points.rejection_factor pid peer key invalid)]
  have leading:=reject_prefix_covers peer.staged key invalid before
  apply covers_bind (leading.mono (fun _ _ _ ready=>.selected ledger steps ready))
  intro ignored u b middle performed
  have ready:=leading.normal performed
  have restored:=restore_covers ready
  apply covers_bind (restored.mono (fun _ _ _ phase=>restore_evidence steps phase))
  intro ignored v c last restoreRun
  have actual:=Staging.normal (CompleteSelected.restore ledger debts locals generation pid peer position
    (fun _=>True) (fun _ _ _=>True.intro)) ready restoreRun
  exact queued_covers actual (steps.trans (transferLocation_step _ _ _)) pid c

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
