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

theorem prevQueuePeek_sameWGStore (q : PrevQueue α) : SameWGStore q.peek := by
  apply SameView.of_wp
  intro k
  mvcgen [PrevQueue.peek, PrevQueue.dequeue, branch, invariant, unsupported,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]

theorem endpointFromSkb_sameWGStore (src : SkbSource) : SameWGStore (endpointFromSkb src) := by
  apply SameView.of_wp
  intro k
  mvcgen [endpointFromSkb, branch, invariant, unsupported,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]

def rxDropPeekedPrefix (pid : PeerId) : MixedM Unit := do
  setPeerMixed pid {(← getPeerMixed pid) with rxQueue := (← getPeerMixed pid).rxQueue.dropPeeked}

theorem rxDropPeekedPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (rxDropPeekedPrefix pid)
      (do setPeer pid {(← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked}) :=
  erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem rxDropPeekedPrefix_preserves (c : AmbientContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (rxDropPeekedPrefix pid) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply StatePrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with rxQueue := q.rxQueue.dropPeeked}

/-- Original arbitrary product-invariant contract at the actual native lift. -/
theorem rxDropPeekedPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (rxDropPeekedPrefix pid)) := by
  unfold rxDropPeekedPrefix
  simp only [liftWGObserver_bind]
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with rxQueue := q.rxQueue.dropPeeked}

def rxPollPrefix (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → PrefixM LifetimeEvent Unit) : PrefixM LifetimeEvent Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- `(skb = wg_prev_queue_peek(&peer->rx_queue)) != NULL` (W7: the queue as
    -- data; an UNCRYPTED head stays peeked across polls)
    let (first, q) ← liftPrefix ((← liftWGObserver (getPeerMixed pid)).rxQueue.peek)
    liftWGObserver (modifyPeerKeysPrefix pid fun p => {p with rxQueue := q})
    -- `&& (state = atomic_read_acquire(&PACKET_CB(skb)->state)) != PACKET_STATE_UNCRYPTED`
    let go ← liftWGObserver (andPrefix (rxBranch .rxPollPacket first.isSome) do
      let some f := first | liftWGPrefix (invariant "unreachable")
      rxBranch .rxPollNotUncrypted ((← getRxSkbPrefix f).state != .uncrypted))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let pkt ← liftWGObserver (getRxSkbPrefix id)
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    -- wg_prev_queue_drop_peeked
    liftWGObserver (rxDropPeekedPrefix pid)
    let mut free := true
    if !(← liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted))) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))) then
        let endpoint ← liftWGObserver (liftWGPrefix (endpointFromSkb pkt.source))
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          -- wg_reset_packet(skb, false) (a cut point)
          for inner in (← liftWGObserver (consumeDataDonePrefix pid pkt e)).toList do
            gro ← napiGroReceivePrefix toStack gro inner
          free := false
    -- next:
    liftWGObserver (keypairPutPrefix (some pkt.keypair) false)
    liftWGObserver (peerPutMixed (some pid))
    _ ← liftPrefix (branch .rxPollFree free)   -- dev_kfree_skb
    liftWGObserver (freeRxSkbPrefix id)   -- freed, or napi_gro_receive's (review 4.2)
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    -- napi_complete_done: NAPI_STATE_SCHED cleared, GRO flushed
    liftWGObserver (modifyPeerKeysPrefix pid fun p => {p with napiScheduled := false})
    napiGroFlushAllPrefix toStack gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem rxPollPrefix_erases (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM LifetimeEvent Unit) (original : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ gro, ErasesPrefix (callback gro) (original gro)) :
    ErasesPrefix (rxPollPrefix pid budget callback) (rxPoll pid budget original) := by
  have go (first : Option SkbId) : ErasesPrefix (liftWGObserver (andPrefix (rxBranch .rxPollPacket first.isSome) do
        let some f := first | liftWGPrefix (invariant "unreachable")
        rxBranch .rxPollNotUncrypted ((← getRxSkbPrefix f).state != .uncrypted)))
      (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
        let some f := first | invariant "unreachable"
        branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted))) := by
    apply liftWGObserver_erases
    apply andPrefix_erases_state (erasesStatePrefix_lift _)
    cases first with
    | none => exact erasesStatePrefix_lift _
    | some f =>
      exact erasesStatePrefix_bind (getRxSkbPrefix_erases f)
        (fun _ => erasesStatePrefix_lift _)
  unfold rxPollPrefix rxPoll modifyPeerKeysPrefix rxDropPeekedPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, bind_assoc]
  repeat' first
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact napiGroReceivePrefix_erases callback original hc _ _
    | with_reducible exact napiGroFlushAllPrefix_erases callback original hc _
    | with_reducible exact hc _
    | (maintenance_head getPeerMixed; exact liftWGObserver_erases (getPeerMixed_erases _))
    | (maintenance_head setPeerMixed; exact liftWGObserver_erases (setPeerMixed_erases _ _))
    | (maintenance_head getRxSkbPrefix; exact liftWGObserver_erases (getRxSkbPrefix_erases _))
    | (maintenance_head modifyPeerKeysPrefix; exact liftWGObserver_erases (modifyPeerKeysPrefix_erases _ _))
    | (maintenance_head rxDropPeekedPrefix; exact liftWGObserver_erases (rxDropPeekedPrefix_erases _))
    | (maintenance_head counterValidatePrefix; exact liftWGObserver_erases (counterValidatePrefix_erases _ _))
    | (maintenance_head consumeDataDonePrefix; exact liftWGObserver_erases (consumeDataDonePrefix_erases _ _ _))
    | (maintenance_head keypairPutPrefix; exact liftWGObserver_erases (keypairPutPrefix_erases _ _))
    | (maintenance_head peerPutMixed; exact liftWGObserver_erases (peerPutMixed_erases _))
    | (maintenance_head freeRxSkbPrefix; exact liftWGObserver_erases (freeRxSkbPrefix_erases _))
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | (maintenance_head andPrefix; exact go _)
    | (maintenance_head liftWGPrefix; exact liftWGObserver_erases (erasesStatePrefix_lift _))
    | (maintenance_head getRxSkbPrefix; exact getRxSkbPrefix_erases _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

  all_goals simp_all
  all_goals first
    | contradiction
    | exact liftWGObserver_erases (getPeerMixed_erases _)
    | exact liftWGObserver_erases (setPeerMixed_erases _ _)
    | exact liftWGObserver_erases (getRxSkbPrefix_erases _)
    | exact liftWGObserver_erases (freeRxSkbPrefix_erases _)
    | exact liftWGObserver_erases (consumeDataDonePrefix_erases _ _ _)

theorem rxPollPrefix_preserves_ambient (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (r : ProductRxContracts I) (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM LifetimeEvent Unit)
    (hc : ∀ gro, PrefixPreserves I LifetimeEvent.Safe (callback gro)) :
    PrefixPreserves I LifetimeEvent.Safe (rxPollPrefix pid budget callback) := by
  have go (first : Option SkbId) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (andPrefix (rxBranch .rxPollPacket first.isSome) do
        let some f := first | liftWGPrefix (invariant "unreachable")
        rxBranch .rxPollNotUncrypted ((← getRxSkbPrefix f).state != .uncrypted))) := by
    simp only [andPrefix, liftWGObserver_bind, rxBranch, liftWGObserver_lift]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro b
    cases b with
    | false => simpa only [Bool.false_eq_true, ↓reduceIte, liftWGObserver_pure] using PrefixPreserves.pure c.safe false
    | true =>
      simp only [↓reduceIte]
      cases first with
      | none => exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
      | some f =>
        simp only [liftWGObserver_bind, liftWGObserver_lift]
        exact PrefixPreserves.bind (ProductAmbientContracts.drop (c.getRx (fun _ => True) f))
          (fun _ => ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
  have conditional {α : Type} (p : Prop) [Decidable p]
      (a b : PrefixM LifetimeEvent α)
      (ha : p → PrefixEnsures I LifetimeEvent.Safe a (fun _ => I))
      (hb : ¬p → PrefixEnsures I LifetimeEvent.Safe b (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (if p then a else b) (fun _ => I) := by
    by_cases h : p
    · simpa only [if_pos h] using ha h
    · simpa only [if_neg h] using hb h
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold rxPollPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head napiGroReceivePrefix; exact napiGroReceivePrefix_preserves callback c.safe hc _ _)
    | (maintenance_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_preserves callback c.safe hc _)
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head getRxSkbPrefix; exact ProductAmbientContracts.drop (c.getRx (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head rxDropPeekedPrefix; exact rxDropPeekedPrefix_preserves_product c _)
    | (maintenance_head counterValidatePrefix; exact ProductAmbientContracts.drop (counterValidatePrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head consumeDataDonePrefix; exact consumeDataDonePrefix_preserves_product c t r _ _ _)
    | (maintenance_head keypairPutPrefix; exact t.put _ _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head freeRxSkbPrefix; exact r.free _)
    | (maintenance_lift_action_head endpointFromSkb; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (endpointFromSkb_sameWGStore _)))
    | (maintenance_head liftPrefix; exact ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_head liftPrefix; exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _))
    | (maintenance_head liftPrefix; exact ProductAmbientContracts.drop (c.store (fun _ => True) _ (liftWG_sameProductStore _ (prevQueuePeek_sameWGStore _))))
    | (maintenance_head liftPrefix; exact ProductAmbientContracts.drop (c.ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head andPrefix; exact go _)
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _ (fun _ => I) _ (fun _ => c.safe))
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.rangeInvariant _ _ _ (fun _ => I) _ (fun _ => c.safe))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | (maintenance_head ite; apply conditional)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
