import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollMatching
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxContracts

/-! Complete occurrence-tagged native poll with its nested final peer release
exposed. Candidate, replay, consumer and GRO callbacks retain their positions. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def pollWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (release : Option PeerId → m Unit)
    (enter : SkbId → RxPacket → m Nat) (leave : Nat → m Unit)
    (counter : SkbId → RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → m GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → m Unit)
    (pid : PeerId) (budget : Nat) : m Nat := do
  if ← step (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroOccurrence.Buffer := {}
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
      let scope ← enter id pkt
      if !(← step (branch .rxPollCounterInvalid !(← counter id pkt))) then
        let endpoint ← step (endpointFromSkb pkt.source)
        if !(← step (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | step (invariant "unreachable")
          for inner in (← consume pid pkt e).toList do
            gro ← receive gro ⟨scope, id, pkt, inner⟩
          free := false
      leave scope
    step (keypairPut (some pkt.keypair) false)
    release (some pid)
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

theorem poll_native {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (enter : SkbId → RxPacket → m Nat) (leave : Nat → m Unit)
    (counter : SkbId → RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option Key))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → m GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → m Unit) (pid : PeerId) (budget : Nat) :
    pollWith step (fun peer => step (peerPut peer)) enter leave counter consume receive flush pid budget =
      GroOccurrencePoll.sourceWith step enter leave counter consume receive flush pid budget := rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
