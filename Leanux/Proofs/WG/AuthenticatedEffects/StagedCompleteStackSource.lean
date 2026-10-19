import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollBase
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames
import Leanux.Proofs.WG.Lifetimes.StackSource

/-! Actual stack replies and tagged GRO callbacks preserve both directions
of ticket accounting. The real transmit callback is an explicit source
contract; stack input metadata is never used as an authentication premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteStack
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePoll
open CompleteCarrier (Accounted)
open Queues.RxCredits
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)

include accountSafe in
theorem safe (h : List Event) (w : World) (before : Carrier debts locals h w) : Safe h := by
  obtain ⟨ledger,accounted⟩ := before
  exact accountSafe ledger h w.wg accounted

theorem stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (before : Carrier debts locals h w) :
    Carrier debts locals h v := by
  obtain ⟨ledger,accounted⟩ := before
  have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  change v.wg.dev = w.wg.dev at device
  refine ⟨ledger,accounted.same_view ?_⟩
  change StagedEntry.view {dev := v.wg.dev} = StagedEntry.view {dev := w.wg.dev}
  rw [device]

include accountSafe in
theorem scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (checked : ∀ token, Checked debts locals Safe (body token)) :
    Checked debts locals Safe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h before
  exact bind_checked Safe (emit Safe accountSafe (.scope (.entered ⟨h.length,cause⟩)) rfl (fun _ => rfl))
    (fun _ => bind_checked Safe (checked ⟨h.length,cause⟩) (fun value =>
      bind_checked Safe (emit Safe accountSafe (.scope (.exited h.length)) rfl (fun _ => rfl))
        (fun _ => pure_checked Safe accountSafe value))) w h before

variable (transmit : ∀ family addr packets mtu, CompletePassive.Checked debts locals Safe
  (Driver.transmitObserved CausalJournal.hooks family addr packets mtu))
include accountSafe transmit

/-- The native stack reply source uses the actual transmit callback on the
same accounted ledger and retains the supplied stopped-prefix predicate. -/
theorem stack (bytes : List UInt8) : Checked debts locals Safe (Driver.stackObserved hooks bytes) :=
  stackReceiveWith_preserves (safe Safe accountSafe) stable _
    (fun bytes => receive4With_preserves (safe Safe accountSafe) stable _
      (fun dst reply => reply4With_preserves (safe Safe accountSafe) stable _
        (fun family addr packets mtu => CompletePoll.state Safe (transmit family addr packets mtu))
        dst reply) bytes) bytes

theorem tagged (entries : List GroOccurrence.Entry) : Checked debts locals Safe
    (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks) entries) :=
  GroOccurrence.stack_preserves (Carrier debts locals) Safe (safe Safe accountSafe)
    hooks.stackInput (Driver.stackObserved hooks) (stack Safe accountSafe transmit)
    (fun entry _ checked => scope Safe accountSafe (.stackInput entry) _ (fun _ => checked)) entries

theorem receive (buffer : GroOccurrence.Buffer) (entry : GroOccurrence.Entry) : Checked debts locals Safe
    (GroOccurrence.receiveWith liftPrefix
      (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks)) buffer entry) :=
  GroOccurrence.receive_preserves (Carrier debts locals) Safe (safe Safe accountSafe) _
    (tagged Safe accountSafe transmit) buffer entry

theorem flush (buffer : GroOccurrence.Buffer) : Checked debts locals Safe
    (GroOccurrence.flushAllWith
      (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks)) buffer) :=
  GroOccurrence.flushAll_preserves (Carrier debts locals) Safe (safe Safe accountSafe) _
    (tagged Safe accountSafe transmit) buffer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteStack
