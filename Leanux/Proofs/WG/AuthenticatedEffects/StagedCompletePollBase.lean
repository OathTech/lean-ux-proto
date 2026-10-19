import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNative
import Leanux.Proofs.WG.TransmitSecurity.StagedCounter

/-! Product-world poll contracts retain the same paired ledger, independent
of candidate labels. Counter and candidate receipts have no ticket demand;
actual confirmation and release callbacks retain their separate proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePoll
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier (Accounted)

abbrev Carrier (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (h : List Event) (w : World) : Prop := CompleteCarrier.Carrier debts locals h w.wg w.ambient
abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event → Prop) (body : PrefixM Event α) : Prop :=
  PrefixEnsures (Carrier debts locals) Safe body (fun _ => Carrier debts locals)

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)

include accountSafe in
theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  PrefixEnsures.pure (fun h _ before => by obtain ⟨ledger,accounted⟩ := before; exact accountSafe ledger h _ accounted)
    (fun _ _ before => before)

theorem bind_checked {body : PrefixM Event α} {next : α → PrefixM Event β}
    (head : Checked debts locals Safe body) (tail : ∀ value, Checked debts locals Safe (next value)) :
    Checked debts locals Safe (body >>= next) := PrefixEnsures.bind head tail

theorem state {body : WGPrefix Event α} (checked : CompletePassive.Checked debts locals Safe body) :
    Checked debts locals Safe (liftWGObserver body) := checked.liftWGObserver

include accountSafe in
theorem native (body : WG.M α) (frame : SameView StagedEntry.view body) :
    Checked debts locals Safe (liftPrefix (liftWG body)) := by
  simpa only [liftWGObserver_lift] using state Safe (CompletePassive.native Safe accountSafe body frame)

include accountSafe in
theorem emit (event : Event) (birth : birthPackets event = []) (terminal : StagedTerminalComplete.Quiet event) :
    Checked debts locals Safe (emitPrefix event) := by
  intro w h before
  obtain ⟨ledger,accounted⟩ := before
  have kept := accounted.append_quiet [event] (by simpa using birth) (by simpa using terminal)
  exact ⟨[event],rfl,accountSafe _ _ _ kept,ledger,kept⟩

include accountSafe in
theorem receipt {body : PrefixM Event α} (record : RunWitness α → Event)
    (checked : Checked debts locals Safe body) (birth : ∀ r, birthPackets (record r) = [])
    (terminal : ∀ r, StagedTerminalComplete.Quiet (record r)) :
    Checked debts locals Safe (receiptObserved body record) := by
  unfold receiptObserved
  have captured : Checked debts locals Safe (captureObserved body) :=
    (PrefixEnsures.captureObserved checked).consequence (fun _ _ before => before)
      (fun run _ _ after => by simpa only [after.1] using after.2.1)
  exact bind_checked Safe captured (fun run =>
    bind_checked Safe (emit Safe accountSafe (record run) (birth run) (terminal run))
      (fun _ => pure_checked Safe accountSafe run.value))

include accountSafe in
theorem counter (skb : SkbId) (packet : RxPacket) :
    Checked debts locals Safe (hooks.counterCheck skb packet) := by
  change Checked debts locals Safe (focusPrefix Event.old old? (TransportDriver.counter Journal.Event.replay skb packet))
  unfold TransportDriver.counter
  rw [Staged.Origins.focused_product_receipt]
  exact receipt Safe accountSafe _ (native Safe accountSafe _ (CompletePollNative.counter packet.keypair packet.nonce))
    (fun _ => rfl) (fun _ _ => rfl)

include accountSafe in
theorem candidate (skb : SkbId) (packet : RxPacket) :
    Checked debts locals Safe (hooks.candidateEnter skb packet) := by
  intro w h before
  obtain ⟨ledger,accounted⟩ := before
  have kept := accounted.append_quiet [.scope (.entered ⟨h.length,.candidate skb packet⟩)]
    (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
    (by intro event member position; simp only [List.mem_singleton] at member; subst event; rfl)
  exact ⟨[_],rfl,accountSafe _ _ _ kept,ledger,kept⟩

include accountSafe in
theorem leave (token : Nat) : Checked debts locals Safe (hooks.candidateLeave token) :=
  emit Safe accountSafe _ rfl (fun _ => rfl)

include accountSafe in
theorem list {α β : Type} (items : List α) (initial : β)
    (body : α → β → PrefixM Event (ForInStep β))
    (checked : ∀ item acc, PrefixEnsures (Carrier debts locals) Safe
      (body item acc) (fun _ => Carrier debts locals)) :
    Checked debts locals Safe (forIn items initial body) :=
  PrefixEnsures.forInInvariant items initial body (fun _ => Carrier debts locals) Safe
    (fun _ h _ before => by obtain ⟨ledger,accounted⟩ := before; exact accountSafe ledger h _ accounted) checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePoll
