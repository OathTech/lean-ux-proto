import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveConsumer
import Leanux.Proofs.WG.TransmitSecurity.StagedCounter

/-! Product-world poll contracts retain the same paired ledger, independent
of candidate labels. Counter and candidate receipts have no ticket demand;
actual confirmation and release callbacks retain their separate proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceivePoll
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier (Accounted)

abbrev Carrier (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (h : List Event) (w : World) : Prop := CompleteCarrier.Carrier debts locals h w.wg w.ambient
abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event → Prop) (body : PrefixM Event α) : Prop :=
  Ensures (Carrier debts locals) Safe body (fun _ => Carrier debts locals)

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)

theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  Ensures.pure value (fun _ _ before=>before)

theorem bind_checked {body : PrefixM Event α} {next : α → PrefixM Event β}
    (head : Checked debts locals Safe body) (tail : ∀ value, Checked debts locals Safe (next value)) :
    Checked debts locals Safe (body >>= next) := Ensures.bind head tail

theorem state {body : WGPrefix Event α} (checked : Passive.Checked debts locals Safe body) :
    Checked debts locals Safe (liftWGObserver body) := checked.liftWG

include accountSafe in
theorem native (body : WG.M α) (frame : SameView StagedEntry.view body) :
    Checked debts locals Safe (liftPrefix (liftWG body)) := by
  simpa only [liftWGObserver_lift] using state Safe (Passive.native Safe accountSafe body frame)

include accountSafe in
theorem emit (event : Event) (birth : birthPackets event=[]) (terminal : StagedTerminalComplete.Quiet event) :
    Checked debts locals Safe (emitPrefix event) := by
  have keep : ∀ h w,Carrier debts locals h w→Carrier debts locals (h++[event]) w := by
    intro h w ⟨ledger,accounted⟩
    exact ⟨ledger,accounted.append_quiet [event] (by simpa using birth) (by simpa using terminal)⟩
  exact Ensures.emit event (fun h w before=>(keep h w before).elim (fun ledger kept=>accountSafe ledger _ w.wg kept)) keep

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
      (fun _ => pure_checked Safe run.value))

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
  obtain ⟨ledger,accounted⟩ := before.1
  have kept := accounted.append_quiet [.scope (.entered ⟨h.length,.candidate skb packet⟩)]
    (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
    (by intro event member position; simp only [List.mem_singleton] at member; subst event; rfl)
  have all := before.2.append (Cuts.singleton before.2.last (accountSafe _ _ _ kept))
  exact ⟨[_],rfl,all,⟨ledger,kept⟩,all⟩

include accountSafe in
theorem leave (token : Nat) : Checked debts locals Safe (hooks.candidateLeave token) :=
  emit Safe accountSafe _ rfl (fun _ => rfl)

theorem list {α β : Type} (items : List α) (initial : β)
    (body : α→β→PrefixM Event (ForInStep β))
    (checked : ∀ item acc,Checked debts locals Safe (body item acc)) :
    Checked debts locals Safe (forIn items initial body) :=
  Ensures.forIn items initial body (fun _=>Carrier debts locals) checked

include accountSafe in
/-- RX erasure preserves the native bounds by its original contract; only
its unchanged journal is used for the additional logical prefix certificate. -/
theorem free_rx (skb : SkbId) : Passive.Checked debts locals Safe (liftWGPrefix (freeRxSkb skb)) :=
  StateEnsures.quiet (CompletePollNative.free_rx Safe accountSafe skb) (fun _ _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceivePoll
