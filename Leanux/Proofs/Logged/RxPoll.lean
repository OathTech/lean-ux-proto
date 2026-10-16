import Leanux.Proofs.Logged.Basic
import Lean.Elab.Tactic

/-! A proof-side receive-poll observer. Its control flow is the pinned mirror's
rxPoll; only successful-validator observations and callback lifting are added. -/
set_option pp.structureInstances false

namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def groNormalListLogged (toStack : List (List UInt8) → GhostM Unit) (gro : GroState) : GhostM GroState := do
  if gro.rxCount == 0 then return gro
  toStack gro.rxList
  return { gro with rxList := [], rxCount := 0 }

def groNormalOneLogged (toStack : List (List UInt8) → GhostM Unit) (gro : GroState)
    (pkt : List UInt8) (segs : Nat) : GhostM GroState := do
  let gro := { gro with rxList := gro.rxList ++ [pkt], rxCount := gro.rxCount + segs }
  if gro.rxCount ≥ GRO_NORMAL_BATCH then groNormalListLogged toStack gro else return gro

def napiGroReceiveLogged (toStack : List (List UInt8) → GhostM Unit) (gro : GroState)
    (pkt : List UInt8) : GhostM GroState := do
  if groTakenAtOnce pkt then groNormalOneLogged toStack gro pkt 1
  else
    if !gro.held.isEmpty then unsupported "GRO holds a second TCP segment in one poll (coalescing, or the hash buckets' flush order)"
    return { gro with held := gro.held ++ [pkt] }

def napiGroFlushAllLogged (toStack : List (List UInt8) → GhostM Unit) (gro : GroState) : GhostM Unit := do
  let mut g := gro
  for pkt in gro.held do g ← groNormalOneLogged toStack g pkt 1
  g := { g with held := [] }
  _ ← groNormalListLogged toStack g

def rxPollLogged (pid : PeerId) (budget : Nat) (napiCompleteDone : List (List UInt8) → GhostM Unit) : GhostM Nat := do
  if ← branch .rxPollNoBudget (budget == 0) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- `(skb = wg_prev_queue_peek(&peer->rx_queue)) != NULL` (W7: the queue as
    -- data; an UNCRYPTED head stays peeked across polls)
    let (first, q) ← (← getPeer pid).rxQueue.peek
    setPeer pid { (← getPeer pid) with rxQueue := q }
    -- `&& (state = atomic_read_acquire(&PACKET_CB(skb)->state)) != PACKET_STATE_UNCRYPTED`
    let go ← WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)
    if !go then
      drained := true
      break
    let some id := first | invariant "unreachable"
    let pkt ← getRxSkb id
    if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
    -- wg_prev_queue_drop_peeked
    setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }
    let mut free := true
    if !(← branch .rxPollNotCrypted (pkt.state != .crypted)) then
      if !(← branch .rxPollCounterInvalid !(← liftWGGhost (counterLogged pkt.keypair pkt.nonce))) then
        let endpoint ← endpointFromSkb pkt.source
        if !(← branch .rxPollEndpointFailed endpoint.isNone) then
          let some e := endpoint | invariant "unreachable"
          -- wg_reset_packet(skb, false) (a cut point)
          for inner in (← consumeDataDone pid pkt e).toList do
            gro ← napiGroReceiveLogged napiCompleteDone gro inner
          free := false
    -- next:
    keypairPut (some pkt.keypair) false
    peerPut (some pid)
    _ ← branch .rxPollFree free   -- dev_kfree_skb
    freeRxSkb id   -- freed, or napi_gro_receive's (review 4.2)
    workDone := workDone + 1
    if ← branch .rxPollBudgetDone (workDone ≥ budget) then break
  if !drained && workDone < budget then invariant "the rx_queue did not drain"
  if ← branch .rxPollComplete (workDone < budget) then
    -- napi_complete_done: NAPI_STATE_SCHED cleared, GRO flushed
    setPeer pid { (← getPeer pid) with napiScheduled := false }
    napiGroFlushAllLogged napiCompleteDone gro
  else unsupported "a NAPI poll that used its whole budget (a repoll)"
  return workDone


-- Keep Erases opaque while introducing the bind/loop callback parameters.
elab "intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro a))

theorem groNormalListLogged_erases
    (logged : List (List UInt8) → GhostM Unit) (original : List (List UInt8) → Leanux.M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets)) (gro : GroState) :
    Erases (groNormalListLogged logged gro) (groNormalList original gro) := by
  unfold groNormalListLogged groNormalList
  split
  · exact erases_pure _
  · exact erases_bind (h _) (fun _ => erases_pure _)

theorem groNormalOneLogged_erases
    (logged : List (List UInt8) → GhostM Unit) (original : List (List UInt8) → Leanux.M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets))
    (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    Erases (groNormalOneLogged logged gro pkt segs) (groNormalOne original gro pkt segs) := by
  unfold groNormalOneLogged groNormalOne
  dsimp only
  split
  · exact groNormalListLogged_erases logged original h _
  · exact erases_pure _

theorem napiGroReceiveLogged_erases
    (logged : List (List UInt8) → GhostM Unit) (original : List (List UInt8) → Leanux.M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets))
    (gro : GroState) (pkt : List UInt8) :
    Erases (napiGroReceiveLogged logged gro pkt) (napiGroReceive original gro pkt) := by
  unfold napiGroReceiveLogged napiGroReceive
  split
  · exact groNormalOneLogged_erases logged original h _ _ _
  · split
    · exact erases_bind (erases_liftM _) (fun _ => erases_pure _)
    · exact erases_pure _

theorem napiGroFlushAllLogged_erases
    (logged : List (List UInt8) → GhostM Unit) (original : List (List UInt8) → Leanux.M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets)) (gro : GroState) :
    Erases (napiGroFlushAllLogged logged gro) (napiGroFlushAll original gro) := by
  unfold napiGroFlushAllLogged napiGroFlushAll
  repeat' first
    | with_reducible exact groNormalListLogged_erases logged original h _
    | with_reducible exact groNormalOneLogged_erases logged original h _ _ _
    | with_reducible exact erases_pure _
    | with_reducible apply erases_bind
    | with_reducible apply erases_forIn
    | intro_forall
    | (with_reducible intro x; try dsimp only)

set_option maxHeartbeats 2000000 in
/-- The complete receive-poll observer has the original result, state and error. -/
theorem rxPollLogged_erases (pid : PeerId) (budget : Nat)
    (logged : List (List UInt8) → GhostM Unit)
    (original : List (List UInt8) → Leanux.M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets)) :
    Erases (rxPollLogged pid budget logged) (WG.rxPoll pid budget original) := by
  unfold rxPollLogged WG.rxPoll
  repeat' first
    | contradiction
    | with_reducible exact erases_pure _
    | exact erases_liftM _
    | exact erases_lift _
    | exact erases_liftWGGhost (counterLogged_erases _ _)
    | with_reducible apply erases_ite
    | with_reducible apply erases_bind
    | with_reducible apply erases_map
    | with_reducible apply erases_range
    | with_reducible apply erases_forIn
    | with_reducible exact napiGroReceiveLogged_erases logged original h _ _
    | with_reducible exact napiGroFlushAllLogged_erases logged original h _
    | with_reducible exact h _
    | intro_forall
    | (split <;> try simp_all only [Option.some.injEq, reduceCtorEq, forall_eq', not_true_eq_false])
  all_goals
    simp_all only [Option.some.injEq]
    exact erases_liftM _

end Leanux.Proofs.Logged
