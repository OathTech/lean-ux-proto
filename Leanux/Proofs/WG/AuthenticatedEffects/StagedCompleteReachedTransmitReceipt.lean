import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitStaging

/-! The successful splice precedes its birth receipt. The fixed source
prefix exposes that actual world without asserting the post-receipt account
at an earlier journal. No native action intervenes before recording it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier

/-- The literal input marker followed by the same front body, just before
the enclosing completed-run receipt is emitted. -/
def bodyPrefix (input : Input) : WGPrefix Event (Except Int PeerId) := do
  emitStatePrefix (.transmitInput input)
  body input

theorem Path.pre_receipt (path : Path input h w a value v b prior) :
    runWGPrefix (bodyPrefix input) w a h=(.ok ((value,v),b),prior) := by
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind,runStatePrefix_emit]
  exact path.performed

theorem Path.recorded (path : Path input h w a value v b prior) :
    runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      runWGPrefix (do
        emitStatePrefix (StagedAdmission.Front.routedEvent input (receipt value w v a b))
        pure value) v b prior := by
  rw [path.front]
  rfl

/-- The entry ledger's debts and local owners are retained at the completed
receipt. The same pre-receipt world is exposed separately by `pre_receipt`. -/
theorem Path.receipt_account (path : Path input h w a value v b prior)
    (before : Accounted h ledger debts locals w) :
    ∃ after,
      runWGPrefix (bodyPrefix input) w a h=(.ok ((value,v),b),prior) ∧
      Accounted (resultHistory input value w v a b prior) after debts locals v ∧
      runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
        runWGPrefix (tail value) v b (resultHistory input value w v a b prior) := by
  obtain ⟨after,accounted,_⟩:=path.accounted before
  exact ⟨after,path.pre_receipt,accounted,path.continuation⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
