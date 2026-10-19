import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourcePassive

/-! Receipt and lexical-scope composition for actual entry accounting. These
events introduce no staged birth; ticket-changing bodies retain their own
source contracts and may select a successor ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourceEvents
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem emit (event : Event) (quiet : birthPackets event = []) :
    Checked debts locals Safe (emitStatePrefix event) :=
  fixed Safe entrySafe (fun _ => Passive.emit event quiet)

theorem receipt (body : WGPrefix Event α) (record : WGRunWitness α → Event)
    (checked : Checked debts locals Safe body) (quiet : ∀ r, birthPackets (record r) = []) :
    Checked debts locals Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved checked)
  intro r
  exact bind_checked Safe (emit Safe entrySafe (record r) (quiet r))
    (fun _ => pure_checked Safe entrySafe r.value)

theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe
      (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  bind_checked Safe (emit Safe entrySafe _ rfl) (fun _ => checked)

theorem scope (cause : Cause) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (CausalScope.scope Event.scope cause body) := by
  intro w a h entry
  exact bind_checked Safe (emit Safe entrySafe (.scope (.entered ⟨h.length,cause⟩)) rfl)
    (fun _ => bind_checked Safe checked (fun value =>
      bind_checked Safe (emit Safe entrySafe (.scope (.exited h.length)) rfl)
        (fun _ => pure_checked Safe entrySafe value))) w a h entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourceEvents
