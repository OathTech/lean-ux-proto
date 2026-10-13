import Leanux.Proofs.WG.Lifetimes.ReceiveCompletion
import Leanux.Proofs.Logged.PrefixGro

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The complete original poll with an explicit observed stack-flush callback.
The callback follows the original GRO batch and completion flushes; releases
and callbacks retain their source order.
This is neither a concrete IP-stack callback proof nor a delivery property. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem prevQueuePeek_sameKernel (q : PrevQueue α) : SameKernel q.peek := by
  apply sameKernel_of_wp
  intro k
  mvcgen [PrevQueue.peek, PrevQueue.dequeue, branch, invariant, unsupported]

theorem endpointFromSkb_sameKernel (src : SkbSource) : SameKernel (endpointFromSkb src) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [endpointFromSkb, branch, invariant, unsupported]

def rxDropPeekedPrefix (pid : PeerId) : MixedM Unit := do
  setPeerMixed pid {(← getPeerMixed pid) with rxQueue := (← getPeerMixed pid).rxQueue.dropPeeked}

theorem rxDropPeekedPrefix_erases (pid : PeerId) :
    ErasesPrefix (rxDropPeekedPrefix pid)
      (do setPeer pid {(← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked}) :=
  erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem rxDropPeekedPrefix_preserves (c : AmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (rxDropPeekedPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with rxQueue := q.rxQueue.dropPeeked}

def rxPollPrefix (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → MixedM Unit) : MixedM Nat := do
  if ← rxBranch .rxPollNoBudget (budget == 0) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- `(skb = wg_prev_queue_peek(&peer->rx_queue)) != NULL` (W7: the queue as
    -- data; an UNCRYPTED head stays peeked across polls)
    let (first, q) ← liftPrefix ((← getPeerMixed pid).rxQueue.peek)
    modifyPeerKeysPrefix pid fun p => {p with rxQueue := q}
    -- `&& (state = atomic_read_acquire(&PACKET_CB(skb)->state)) != PACKET_STATE_UNCRYPTED`
    let go ← andPrefix (rxBranch .rxPollPacket first.isSome) do
      let some f := first | liftPrefix (invariant "unreachable")
      rxBranch .rxPollNotUncrypted ((← getRxSkbPrefix f).state != .uncrypted)
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let pkt ← getRxSkbPrefix id
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    -- wg_prev_queue_drop_peeked
    rxDropPeekedPrefix pid
    let mut free := true
    if !(← rxBranch .rxPollNotCrypted (pkt.state != .crypted)) then
      if !(← rxBranch .rxPollCounterInvalid !(← counterValidatePrefix pkt.keypair pkt.nonce)) then
        let endpoint ← liftPrefix (endpointFromSkb pkt.source)
        if !(← rxBranch .rxPollEndpointFailed endpoint.isNone) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          -- wg_reset_packet(skb, false) (a cut point)
          for inner in (← consumeDataDonePrefix pid pkt e).toList do
            gro ← napiGroReceivePrefix toStack gro inner
          free := false
    -- next:
    keypairPutPrefix (some pkt.keypair) false
    peerPutMixed (some pid)
    _ ← rxBranch .rxPollFree free   -- dev_kfree_skb
    freeRxSkbPrefix id   -- freed, or napi_gro_receive's (review 4.2)
    workDone := workDone + 1
    if ← rxBranch .rxPollBudgetDone (workDone ≥ budget) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← rxBranch .rxPollComplete (workDone < budget) then
    -- napi_complete_done: NAPI_STATE_SCHED cleared, GRO flushed
    modifyPeerKeysPrefix pid fun p => {p with napiScheduled := false}
    napiGroFlushAllPrefix toStack gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem rxPollPrefix_erases (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → MixedM Unit) (original : List (List UInt8) → M Unit)
    (hc : ∀ gro, ErasesPrefix (callback gro) (original gro)) :
    ErasesPrefix (rxPollPrefix pid budget callback) (rxPoll pid budget original) := by
  unfold rxPollPrefix rxPoll modifyPeerKeysPrefix rxDropPeekedPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact napiGroReceivePrefix_erases callback original hc _ _
    | with_reducible exact napiGroFlushAllPrefix_erases callback original hc _
    | with_reducible exact hc _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact getRxSkbPrefix_erases _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact rxDropPeekedPrefix_erases _
    | with_reducible exact counterValidatePrefix_erases _ _
    | with_reducible exact consumeDataDonePrefix_erases _ _ _
    | with_reducible exact keypairPutPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact freeRxSkbPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

  all_goals simp_all
  all_goals first
    | contradiction
    | exact getRxSkbPrefix_erases _
    | exact freeRxSkbPrefix_erases _
    | exact consumeDataDonePrefix_erases _ _ _

theorem rxPollPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → MixedM Unit)
    (hc : ∀ gro, PrefixPreserves I LifetimeEvent.Safe (callback gro)) :
    PrefixPreserves I LifetimeEvent.Safe (rxPollPrefix pid budget callback) := by
  unfold rxPollPrefix
  repeat' first
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact napiGroReceivePrefix_preserves callback c.safe hc _ _
    | with_reducible exact napiGroFlushAllPrefix_preserves callback c.safe hc _
    | with_reducible exact hc _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.getRx (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact rxDropPeekedPrefix_preserves c _
    | with_reducible exact AmbientContracts.drop (counterValidatePrefix_spec c (fun _ => True) _ _)
    | with_reducible exact consumeDataDonePrefix_preserves_ambient c t r _ _ _
    | with_reducible exact t.put _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact r.free _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (prevQueuePeek_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (endpointFromSkb_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.unsupported (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
