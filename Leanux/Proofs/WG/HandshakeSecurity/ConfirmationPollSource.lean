import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationSource

/-! Literal native poll with receive callbacks exposed. The specialization
is the original poll; the source still checks crypted state, replay acceptance
and the endpoint before calling the confirmation-bearing consumer. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged

def sourceWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (counter : RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
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
    if !(← step (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← step (branch .rxPollCounterInvalid !(← counter pkt))) then
        let endpoint ← step (endpointFromSkb pkt.source)
        if !(← step (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | step (invariant "unreachable")
          for inner in (← consume pid pkt e).toList do
            gro ← receive gro inner
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

theorem source (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit) :
    rxPoll pid budget toStack =
      sourceWith (fun a => a) (fun pkt => counterValidate pkt.keypair pkt.nonce)
        consumeDataDone (napiGroReceive toStack) (napiGroFlushAll toStack) pid budget := by
  simp only [rxPoll, sourceWith, monadLift_self, bind_assoc]
  congr 1

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
