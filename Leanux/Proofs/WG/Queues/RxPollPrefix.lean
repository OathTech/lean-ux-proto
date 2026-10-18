import Leanux.Proofs.WG.Queues.RxPollPrimitives
import Leanux.Proofs.Logged.PrefixLoops
import Leanux.Proofs.Logged.PrefixGro

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-! Removal observations at the original receive-poll queue update. The log
contains skb occurrences in removal order and survives every later Stop.
It does not classify completion results as stack delivery. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

def dropRxPrefix (pid : PeerId) (id : SkbId) : PrefixM SkbId Unit := do
  liftPrefix (liftWG (dropRxQueue pid))
  emitPrefix id

theorem dropRxPrefix_erases (pid : PeerId) (id : SkbId) :
    ErasesPrefix (dropRxPrefix pid id) (liftWG (dropRxQueue pid)) := by
  intro w h
  simp only [dropRxPrefix, runPrefix_bind, runPrefix_lift]
  cases hr : (liftWG (dropRxQueue pid)).run w with
  | error e => rfl
  | ok out => cases out; rfl

/-- A successful original drop emits exactly one event; a failed drop emits
none. This is the local source-coverage boundary used by the poll observer. -/
theorem dropRxPrefix_run (pid : PeerId) (id : SkbId) (w : World) (h : List SkbId) :
    runPrefix (dropRxPrefix pid id) w h =
      match (liftWG (dropRxQueue pid)).run w with
      | .error stop => (.error stop, h)
      | .ok (_, v) => (.ok ((), v), h ++ [id]) := by
  simp only [dropRxPrefix, runPrefix_bind, runPrefix_lift]
  cases (liftWG (dropRxQueue pid)).run w with
  | error e => rfl
  | ok out => cases out; rfl

def completeRxQueue (pid : PeerId) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with napiScheduled := false }

/-- A source grouping with the original result and complete World/Stop.
Its only change is naming the peek/cache and two-getter drop boundaries. -/
def rxPollGrouped (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) : Leanux.M Nat := do
  if ← branch .rxPollNoBudget (budget == 0) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← peekRxQueue pid
    let go ← WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)
    if !go then
      drained := true
      break
    let some id := first | invariant "unreachable"
    let pkt ← getRxSkb id
    if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
    dropRxQueue pid
    let mut free := true
    if !(← branch .rxPollNotCrypted (pkt.state != .crypted)) then
      if !(← branch .rxPollCounterInvalid !(← counterValidate pkt.keypair pkt.nonce)) then
        let endpoint ← endpointFromSkb pkt.source
        if !(← branch .rxPollEndpointFailed endpoint.isNone) then
          let some e := endpoint | invariant "unreachable"
          for inner in (← consumeDataDone pid pkt e).toList do
            gro ← napiGroReceive callback gro inner
          free := false
    keypairPut (some pkt.keypair) false
    peerPut (some pid)
    _ ← branch .rxPollFree free
    freeRxSkb id
    workDone := workDone + 1
    if ← branch .rxPollBudgetDone (workDone ≥ budget) then break
  if !drained && workDone < budget then invariant "the rx_queue did not drain"
  if ← branch .rxPollComplete (workDone < budget) then
    completeRxQueue pid
    napiGroFlushAll callback gro
  else unsupported "a NAPI poll that used its whole budget (a repoll)"
  return workDone

theorem rxPollGrouped_eq (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) :
    rxPollGrouped pid budget callback = rxPoll pid budget callback := by
  have hl {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  simp only [rxPollGrouped, rxPoll, hl, peekRxQueue, dropRxQueue, completeRxQueue,
    liftWG_bind, liftWG_pure, bind_assoc, pure_bind]
  repeat' first | rfl | (congr 1) | (intro x; try cases x)

def rxPollRemovals (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) : PrefixM SkbId Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← liftPrefix (liftWG (peekRxQueue pid))
    let go ← liftPrefix (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let pkt ← liftPrefix (liftWG (getRxSkb id))
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    dropRxPrefix pid id
    let mut free := true
    if !(← liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← liftPrefix (liftWG (counterValidate pkt.keypair pkt.nonce))))) then
        let endpoint ← liftPrefix (liftWG (endpointFromSkb pkt.source))
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          for inner in (← liftPrefix (liftWG (consumeDataDone pid pkt e))).toList do
            gro ← napiGroReceivePrefix (fun bytes => liftPrefix (callback bytes)) gro inner
          free := false
    liftPrefix (liftWG (keypairPut (some pkt.keypair) false))
    liftPrefix (liftWG (peerPut (some pid)))
    _ ← liftPrefix (branch .rxPollFree free)
    liftPrefix (liftWG (freeRxSkb id))
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    liftPrefix (liftWG (completeRxQueue pid))
    napiGroFlushAllPrefix (fun bytes => liftPrefix (callback bytes)) gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

/-- Erasure covers every input, including missing peers, malformed queues,
full-budget refusal and a callback that itself fails. -/
theorem rxPollRemovals_erases (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) :
    ErasesPrefix (rxPollRemovals pid budget callback) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
  unfold rxPollRemovals rxPollGrouped
  have hl {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  simp only [hl]
  repeat' first
    | with_reducible exact napiGroReceivePrefix_erases _ _ (fun _ => erasesPrefix_lift _) _ _
    | with_reducible exact napiGroFlushAllPrefix_erases _ _ (fun _ => erasesPrefix_lift _) _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact dropRxPrefix_erases _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

end Leanux.Proofs.WG.Queues
