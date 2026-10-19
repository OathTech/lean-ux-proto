import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptFrames

/-! Actual decrypt preparation retains paired accounting independently of
its crypto result. The original RX observer supplies all emitted receipts;
none is a staged birth or terminal demand. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDecrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier

/-- Actual preparation, including failed decryption and stopped prefixes,
preserves the same complete ledger. Later IRQ/release calls are separate. -/
theorem checked (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    CompletePoll.Checked debts locals Safe hooks.prepare := by
  apply CompleteRing.focused Safe accountSafe Event.old old?
    (TransportDriver.prepare Journal.Event.rxOrigin Journal.origin?)
  · exact Appends.focus _ _ _
  · exact focusPrefix_other Journal.Event.rxOrigin Journal.origin? (CompleteRing.demand? ∘ Event.old)
      (fun _ => CompleteRing.demand_none rfl (fun _ => rfl)) _
  · exact TransportDriver.prepare_erases _ _
  · intro h ledger
    apply PublicationPoll.native_product (Inv h ledger debts locals)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp prepare w a value v b run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDecrypt
