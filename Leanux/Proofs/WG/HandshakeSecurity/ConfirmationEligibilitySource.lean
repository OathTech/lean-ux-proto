import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged

def eligibleWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (counter : RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (pid : PeerId) (pkt : RxPacket) : m (Option (Option (List UInt8))) := do
  if !(← step (branch .rxPollNotCrypted (pkt.state != .crypted))) then
    if !(← step (branch .rxPollCounterInvalid !(← counter pkt))) then
      let endpoint ← step (endpointFromSkb pkt.source)
      if !(← step (branch .rxPollEndpointFailed endpoint.isNone)) then
        let some e := endpoint | step (invariant "unreachable")
        return some (← consume pid pkt e)
  return none

def withEligibility {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (eligible : PeerId → RxPacket → m (Option (Option (List UInt8))))
    (receive : GroState → List UInt8 → m GroState) (flush : GroState → m Unit)
    (pid : PeerId) (budget : Nat) : m Nat := do
  if ← step (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let (first, q) ← step (do (← getPeer pid).rxQueue.peek)
    step (do setPeer pid { (← getPeer pid) with rxQueue := q })
    let go ← step (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted))
    if !go then
      drained := true
      break
    let some id := first | step (invariant "unreachable")
    let pkt ← step (getRxSkb id)
    if pkt.peer != pid then step (invariant "a packet on another peer's rx_queue")
    step (do setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked })
    let mut free := true
    match ← eligible pid pkt with
    | none => pure ()
    | some inner =>
      for bytes in inner.toList do gro ← receive gro bytes
      free := false
    step (keypairPut (some pkt.keypair) false)
    step (peerPut (some pid))
    _ ← step (branch .rxPollFree free)
    step (freeRxSkb id)
    workDone := workDone + 1
    if ← step (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then step (invariant "the rx_queue did not drain")
  if ← step (branch .rxPollComplete (workDone < budget)) then
    step (do setPeer pid { (← getPeer pid) with napiScheduled := false })
    flush gro
  else step (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

private theorem invariant_bind {α β : Type} (why : String) (f : α → WG.M β) :
    (invariant why >>= f) = (invariant why : WG.M β) := by
  rfl

private theorem eligible_bind {α : Type} (pid : PeerId) (pkt : RxPacket)
    (f : Option (Option (List UInt8)) → WG.M α) :
    (eligibleWith (fun a => a) (fun pkt => counterValidate pkt.keypair pkt.nonce)
      consumeDataDone pid pkt >>= f) = (do
      if !(← branch .rxPollNotCrypted (pkt.state != .crypted)) then
        if !(← branch .rxPollCounterInvalid !(← counterValidate pkt.keypair pkt.nonce)) then
          let endpoint ← endpointFromSkb pkt.source
          if !(← branch .rxPollEndpointFailed endpoint.isNone) then
            let some e := endpoint | invariant "unreachable"
            return ← f (some (← consumeDataDone pid pkt e))
      f none) := by
  simp only [eligibleWith, bind_assoc, Queues.RxCredits.bind_if_source, pure_bind,
    invariant_bind]
  congr 1
  funext rejected
  split
  · congr 1
    funext accepted
    congr 1
    funext invalid
    split
    · congr 1
      funext endpoint
      congr 1
      funext invalidEndpoint
      split
      · cases endpoint <;> simp only [bind_assoc, pure_bind, invariant_bind]
      · rfl
    · rfl
  · rfl

theorem eligibility_factor (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → WG.M Unit) :
    rxPoll pid budget toStack =
      withEligibility (fun a => a)
        (eligibleWith (fun a => a) (fun pkt => counterValidate pkt.keypair pkt.nonce) consumeDataDone)
        (napiGroReceive toStack) (napiGroFlushAll toStack) pid budget := by
  rw [source]
  simp only [sourceWith, withEligibility, eligible_bind, bind_assoc,
    invariant_bind]
  congr 1

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
