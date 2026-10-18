import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationEligibilitySource

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Receipt where
  counter : WGRunWitness Bool
  confirmation : Confirmation.Receipt

def Receipt.Valid (r : Receipt) : Prop :=
  r.counter.Valid (counterValidate r.confirmation.packet.keypair r.confirmation.packet.nonce) ∧
  r.counter.value = true ∧ r.confirmation.packet.state = .crypted ∧ r.confirmation.Valid

def consumeObserved (counter : WGRunWitness Bool) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    WGPrefix Receipt (Option (List UInt8)) := do
  liftWGPrefix (setPeerEndpoint pid ep)
  let confirmed ← receiptWGObserved (liftWGPrefix (receivedWithKeypair pid pkt.keypair))
    (fun execution => ⟨counter, ⟨pid, pkt, ep, execution⟩⟩)
  liftWGPrefix (afterConfirmation pid pkt confirmed)

def afterCounter (counter : WGRunWitness Bool) (pid : PeerId) (pkt : RxPacket) :
    WGPrefix Receipt (Option (Option (List UInt8))) := do
  if !(← liftWGPrefix (branch .rxPollCounterInvalid !counter.value)) then
    let endpoint ← liftWGPrefix (endpointFromSkb pkt.source)
    if !(← liftWGPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
      let some e := endpoint | liftWGPrefix (invariant "unreachable")
      return some (← consumeObserved counter pid pkt e)
  return none

def eligibleObserved (pid : PeerId) (pkt : RxPacket) : WGPrefix Receipt (Option (Option (List UInt8))) := do
  if !(← liftWGPrefix (branch .rxPollNotCrypted (pkt.state != .crypted))) then
    afterCounter (← captureWGRun (counterValidate pkt.keypair pkt.nonce)) pid pkt
  else return none

private theorem capture_bind_erases {α β : Type} (action : WG.M α)
    (g : WGRunWitness α → WGPrefix Receipt β) (f : α → WG.M β)
    (hg : ∀ r, ErasesStatePrefix (g r) (f r.value)) :
    ErasesStatePrefix (captureWGRun action >>= g) (action >>= f) := by
  intro w a h
  change (runStatePrefix (captureWGRun action >>= g) w a h).1 = _
  rw [runStatePrefix_bind]
  have equation := runWGPrefix_captureWGRun (E := Receipt) action w a h
  change runStatePrefix (captureWGRun action) w a h = _ at equation
  rw [equation]
  simp only [StateT.run_bind]
  cases run : (action.run w).run a with
  | error stop => rfl
  | ok out =>
    rcases out with ⟨⟨value, v⟩, b⟩
    exact hg ⟨value, w, v, a, b⟩ v b h

theorem consume_erases (counter : WGRunWitness Bool) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (consumeObserved counter pid pkt ep) (consumeDataDone pid pkt ep) := by
  rw [Confirmation.source]
  unfold consumeObserved
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  intro _
  exact erasesStatePrefix_lift _

private theorem lifted {α : Type} (action : WG.M α) :
    ErasesStatePrefix (liftWGPrefix action : WGPrefix Receipt α) action :=
  erasesStatePrefix_lift action

private theorem erases_if {α : Type} (c : Prop) [Decidable c]
    (x y : WGPrefix Receipt α) (a b : WG.M α)
    (hx : ErasesStatePrefix x a) (hy : ErasesStatePrefix y b) :
    ErasesStatePrefix (if c then x else y) (if c then a else b) := by
  split <;> assumption

theorem eligible_erases (pid : PeerId) (pkt : RxPacket) :
    ErasesStatePrefix (eligibleObserved pid pkt)
      (Poll.eligibleWith (fun a => a) (fun pkt => counterValidate pkt.keypair pkt.nonce)
        consumeDataDone pid pkt) := by
  unfold eligibleObserved Poll.eligibleWith
  apply erasesStatePrefix_bind (lifted _)
  intro rejected
  apply erases_if
  · apply capture_bind_erases
    intro counter
    unfold afterCounter
    repeat' first
      | with_reducible exact consume_erases _ _ _ _
      | with_reducible exact lifted _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
      | with_reducible apply erases_if
      | (session_origin_intro_forall; try dsimp only)
      | split
    all_goals simp_all
  · exact erasesStatePrefix_pure _

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization
