import Leanux.Proofs.WG.Queues.StampedGro

/-! A single execution observes original receive accesses and stamped GRO
occurrences. Stamp capture wraps the original second packet getter; there is
no extra getter. Every put, free, batch flush and Stop stays in source order. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def peekAccess (pid : PeerId) : MixedM (Option SkbId) := do
  let (first, q) ← liftWGPrefix ((← getPeerMixed pid).rxQueue.peek)
  modifyPeerKeysPrefix pid fun p => {p with rxQueue := q}
  return first

def readyAccess (first : Option SkbId) : MixedM Bool :=
  andPrefix (rxBranch .rxPollPacket first.isSome) do
    let some f := first | liftWGPrefix (invariant "unreachable")
    rxBranch .rxPollNotUncrypted ((← getRxSkbPrefix f).state != .uncrypted)

def capture (id : SkbId) : Obs (RxPacket × PacketStamp) :=
  fun w => ExceptT.mk fun h =>
    let out := runPrefix (access (liftWGObserver (getRxSkbPrefix id))) w h
    (out.1.map (fun (p, v) => ((p, packetStamp w.wg id), v)), out.2)

def drop (pid : PeerId) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp) : Obs Unit := do
  access (liftWGObserver (rxDropPeekedPrefix pid))
  emitPrefix (.removed occurrence id stamp)

def consume (pid : PeerId) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (pkt : RxPacket) (endpoint : Endpoint) : Obs (Option Entry) := do
  let r ← captureObserved (access (liftWGObserver (consumeDataDonePrefix pid pkt endpoint)))
  let receipt : RxDisposition.ConsumeReceipt := ⟨pid, pkt, endpoint, ⟨r.value, r.before.wg, r.after.wg, r.before.ambient, r.after.ambient⟩⟩
  emitPrefix (.consumed occurrence id stamp receipt)
  match r.value with
  | none => return none
  | some bytes =>
    let e : Entry := ⟨⟨occurrence, id, bytes⟩, stamp, some receipt⟩
    emitPrefix (.buffered e)
    return some e

/-- The captured call is the original access observer at the actual incoming
history. Its Stop keeps every access; normal None also receives a receipt. -/
theorem consume_run (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) (w : World) (h : List Event) :
    runPrefix (consume pid occurrence id stamp pkt ep) w h =
      match runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
      | (.error e, t) => (.error e, t)
      | (.ok (out, v), t) =>
        let receipt : RxDisposition.ConsumeReceipt := ⟨pid, pkt, ep, ⟨out, w.wg, v.wg, w.ambient, v.ambient⟩⟩
        let t := t ++ [.consumed occurrence id stamp receipt]
        match out with
        | none => (.ok (none, v), t)
        | some bytes =>
          let entry : Entry := ⟨⟨occurrence, id, bytes⟩, stamp, some receipt⟩
          (.ok (some entry, v), t ++ [.buffered entry]) := by
  simp only [consume, runPrefix_bind, runPrefix_captureObserved]
  cases runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk out t => cases out with
    | error e => rfl
    | ok result => rcases result with ⟨out, v⟩; cases out <;> rfl

def completeAccess (pid : PeerId) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => {p with napiScheduled := false}

def poll (pid : PeerId) (budget : Nat) : Obs Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : Gro := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← access (liftWGObserver (peekAccess pid))
    let go ← access (liftWGObserver (readyAccess first))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let captured ← capture id
    let pkt := captured.1
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    drop pid workDone id captured.2
    let mut free := true
    if !(← receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState workDone id captured.2 pkt)) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
          (Event.checkedCounter workDone id captured.2 pkt)))) then
        let endpoint ← receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
          (Event.checkedEndpoint workDone id captured.2 pkt)
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          for entry in (← consume pid workDone id captured.2 pkt e).toList do
            gro ← receive gro entry
          free := false
    access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false))
    access (liftWGObserver (peerPutMixed (some pid)))
    _ ← liftPrefix (branch .rxPollFree free)
    access (liftWGObserver (freeRxSkbPrefix id))
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    access (liftWGObserver (completeAccess pid))
    flushAll gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

def pollAccess (pid : PeerId) (budget : Nat) : PrefixM LifetimeEvent Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : GroState := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← liftWGObserver (peekAccess pid)
    let go ← liftWGObserver (readyAccess first)
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
        let endpoint ← liftPrefix (liftWG (endpointFromSkb pkt.source))
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          -- wg_reset_packet(skb, false) (a cut point)
          for inner in (← liftWGObserver (consumeDataDonePrefix pid pkt e)).toList do
            gro ← napiGroReceivePrefix stackFlushPrefix gro inner
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
    liftWGObserver (completeAccess pid)
    napiGroFlushAllPrefix stackFlushPrefix gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem pollAccess_eq (pid : PeerId) (budget : Nat) :
    pollAccess pid budget = rxPollStackPrefix pid budget := by
  simp only [pollAccess, rxPollStackPrefix, rxPollPrefix, peekAccess, readyAccess,
    completeAccess, liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure, bind_assoc, pure_bind]
  repeat' first | rfl | congr 1 | (intro x; try cases x)

end Leanux.Proofs.WG.Queues.RxJoint
