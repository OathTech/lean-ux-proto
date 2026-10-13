import Leanux.Proofs.Logged.Basic
import Lean.Elab.Tactic

/-! A proof-side receive-poll observer. Its control flow is the pinned mirror's
rxPoll; only successful-validator observations and callback lifting are added. -/
set_option pp.structureInstances false

namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

def rxPollLogged (pid : PeerId) (budget : Nat) (napiCompleteDone : List (List UInt8) → GhostM Unit) : GhostM Nat := do
  if ← branch .rxPollNoBudget (budget == 0) then return 0
  let mut workDone := 0
  let mut gro : List (List UInt8) := []
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
      if !(← branch .rxPollCounterInvalid !(← counterLogged pkt.keypair pkt.nonce)) then
        let endpoint ← endpointFromSkb pkt.source
        if !(← branch .rxPollEndpointFailed endpoint.isNone) then
          let some e := endpoint | invariant "unreachable"
          -- wg_reset_packet(skb, false) (a cut point)
          gro := gro ++ (← consumeDataDone pid pkt e).toList
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
    napiCompleteDone gro
  else unsupported "a NAPI poll that used its whole budget (a repoll)"
  return workDone


-- Keep Erases opaque while introducing the bind/loop callback parameters.
elab "intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro a))

set_option maxHeartbeats 2000000 in
/-- The complete receive-poll observer has the original result, state and error. -/
theorem rxPollLogged_erases (pid : PeerId) (budget : Nat)
    (logged : List (List UInt8) → GhostM Unit)
    (original : List (List UInt8) → M Unit)
    (h : ∀ packets, Erases (logged packets) (original packets)) :
    Erases (rxPollLogged pid budget logged) (WG.rxPoll pid budget original) := by
  unfold rxPollLogged WG.rxPoll
  repeat' first
    | contradiction
    | with_reducible exact erases_pure _
    | with_reducible exact erases_liftM _
    | with_reducible exact erases_lift _
    | with_reducible exact counterLogged_erases _ _
    | with_reducible apply erases_ite
    | with_reducible apply erases_bind
    | with_reducible apply erases_map
    | with_reducible apply erases_range
    | with_reducible apply erases_forIn
    | with_reducible exact h _
    | intro_forall
    | (split <;> try simp_all only [Option.some.injEq, reduceCtorEq, forall_eq', not_true_eq_false])
  all_goals grind only [erases_liftM]

end Leanux.Proofs.Logged
