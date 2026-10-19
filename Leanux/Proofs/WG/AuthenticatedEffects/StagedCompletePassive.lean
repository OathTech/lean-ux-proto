import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDisposalChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceEvents

/-! Bind-compatible entry and converse accounting use one ledger at every
cut. Passive events must introduce neither births nor terminal demands;
counted releases use their exact paired successor contracts separately. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePassive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier StagedTerminalComplete

abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event → Prop) (action : WGPrefix Event α) : Prop :=
  StatePrefixPreserves (Carrier debts locals) Safe action

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)

include accountSafe in
theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  StatePrefixEnsures.pure value
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before; exact accountSafe ledger h w entry)
    (fun _ _ _ before => before)

theorem bind_checked {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (head : Checked debts locals Safe body) (tail : ∀ x, Checked debts locals Safe (next x)) :
    Checked debts locals Safe (body >>= next) := StatePrefixEnsures.bind head tail

include accountSafe in
theorem fixed {body : WGPrefix Event α}
    (checked : ∀ ledger, CompleteCarrier.Checked ledger debts locals body) :
    Checked debts locals Safe body := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  obtain ⟨suffix,extended,safe,kept⟩ := checked ledger w a h entry
  refine ⟨suffix,extended,?_,?_⟩
  · obtain ⟨cut,accounted⟩ := safe
    exact accountSafe ledger _ cut accounted
  · cases performed : (runPrefix (body.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      rw [performed] at kept
      exact ⟨ledger,kept⟩

include accountSafe in
theorem native (action : WG.M α) (frame : SameView StagedEntry.view action) :
    Checked debts locals Safe (liftWGPrefix action) :=
  fixed Safe accountSafe (fun _ => CompleteCarrier.native action frame)

include accountSafe in
theorem ambient (action : AmbientM α) :
    Checked debts locals Safe (liftWGPrefix (monadLift action : WG.M α)) :=
  native Safe accountSafe _ (fun initial => hoare_liftAmbient action (fun w => StagedEntry.view w = initial))

theorem emit_fixed (event : Event) (birth : birthPackets event = []) (terminal : Quiet event) :
    CompleteCarrier.Checked ledger debts locals (emitStatePrefix event) := by
  have keep : ∀ h w, Accounted h ledger debts locals w → Accounted (h ++ [event]) ledger debts locals w := by
    intro h w before
    exact before.append_quiet [event] (by simpa using birth) (by simpa using terminal)
  exact StatePrefixEnsures.emit event (fun h w _ before => ⟨w,keep h w before⟩)
    (fun h w _ before => keep h w before)

include accountSafe in
theorem emit (event : Event) (birth : birthPackets event = []) (terminal : Quiet event) :
    Checked debts locals Safe (emitStatePrefix event) :=
  fixed Safe accountSafe (fun _ => emit_fixed event birth terminal)

include accountSafe in
theorem receipt (body : WGPrefix Event α) (record : WGRunWitness α → Event)
    (checked : Checked debts locals Safe body) (birth : ∀ r, birthPackets (record r) = [])
    (terminal : ∀ r, Quiet (record r)) :
    Checked debts locals Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved checked)
  intro r
  exact bind_checked Safe (emit Safe accountSafe (record r) (birth r) (terminal r))
    (fun _ => pure_checked Safe accountSafe r.value)

include accountSafe in
theorem callback (kind : HandshakeCausal.Kind) (pid : PeerId) (body : WGPrefix Event α)
    (checked : Checked debts locals Safe body) : Checked debts locals Safe
      (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body) :=
  bind_checked Safe (emit Safe accountSafe _ rfl (fun _ => rfl)) (fun _ => checked)

include accountSafe in
theorem scope (cause : Cause) (body : WGPrefix Event α) (checked : Checked debts locals Safe body) :
    Checked debts locals Safe (CausalScope.scope Event.scope cause body) := by
  intro w a h before
  exact bind_checked Safe (emit Safe accountSafe (.scope (.entered ⟨h.length,cause⟩)) rfl (fun _ => rfl))
    (fun _ => bind_checked Safe checked (fun value =>
      bind_checked Safe (emit Safe accountSafe (.scope (.exited h.length)) rfl (fun _ => rfl))
        (fun _ => pure_checked Safe accountSafe value))) w a h before

include accountSafe in
theorem update_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WGPrefix Event α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ value, Checked debts locals Safe (next value)) : Checked debts locals Safe
      (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next) := by
  simpa only [Queued.lift_bind,bind_assoc] using
    bind_checked Safe (native Safe accountSafe _ (Queued.update pid f same)) tail

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePassive
