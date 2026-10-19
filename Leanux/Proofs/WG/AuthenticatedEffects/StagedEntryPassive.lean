import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerSource

/-! Bind-compatible local accounting retains a full entry witness even on
Stop. It does not identify a final stopped native world or prove historical
conservation by itself. Native frames and receipt rules below establish each
retained witness at their own actual call; ticket-consuming callbacks require
their separate settlement contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Passive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal

def Safe (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (h : List Event) : Prop := ∃ w, Inv h ledger debts locals w

abbrev Checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (action : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (fun h w _ => Inv h ledger debts locals w) (Safe ledger debts locals) action

variable {ledger : Ledger} {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem pure_checked (value : α) : Checked ledger debts locals (pure value) :=
  StatePrefixEnsures.pure value (fun _ w _ entry => ⟨w,entry⟩) (fun _ _ _ entry => entry)

theorem bind_checked {action : WGPrefix Event α} {next : α → WGPrefix Event β}
    (head : Checked ledger debts locals action) (tail : ∀ x, Checked ledger debts locals (next x)) :
    Checked ledger debts locals (action >>= next) := StatePrefixEnsures.bind head tail

/-- The native frame proves the same fixed ledger and physical ownership at
normal return. Failure retains the incoming accounted entry in Safe. -/
theorem native (action : WG.M α) (frame : SameView StagedEntry.view action) :
    Checked ledger debts locals (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ w _ entry => ⟨w,entry⟩)
  intro h w a value v b entry run
  exact entry.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run)

theorem ambient (action : AmbientM α) :
    Checked ledger debts locals (liftWGPrefix (monadLift action : WG.M α)) :=
  native _ (fun initial => hoare_liftAmbient action (fun w => StagedEntry.view w = initial))

theorem emit (event : Event) (quiet : birthPackets event = []) :
    Checked ledger debts locals (emitStatePrefix event) := by
  have kept : ∀ h w, Inv h ledger debts locals w → Inv (h ++ [event]) ledger debts locals w := by
    intro h w entry
    exact Queued.Inv.history entry [event] (by simpa using quiet)
  exact StatePrefixEnsures.emit event (fun h w _ entry => ⟨w,kept h w entry⟩)
    (fun h w _ entry => kept h w entry)

theorem receipt (action : WG.M α) (frame : SameView StagedEntry.view action)
    (record : WGRunWitness α → Event) (quiet : ∀ r, birthPackets (record r) = []) :
    Checked ledger debts locals (receiptWGObserved (liftWGPrefix action) record) := by
  unfold receiptWGObserved
  apply bind_checked (StatePrefixPreserves.captureWGObserved (native action frame))
  intro r
  exact bind_checked (emit (record r) (quiet r)) (fun _ => pure_checked r.value)

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    Checked ledger debts locals (effects.arm pid timer delay clock) := by
  intro w a h entry
  exact receipt (armTimer pid timer delay clock) (TimerFrames.arm pid timer delay clock)
    (fun r => .armed ⟨CausalScope.current scope? h,pid,timer,delay,clock,r⟩)
    (fun _ => rfl) w a h entry

theorem update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue) :
    Checked ledger debts locals (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p))) := by
  rw [← Queued.lift_bind]
  exact native _ (Queued.update pid f same)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Passive
