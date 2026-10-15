import Leanux.Proofs.Logged.Tools

/-! Proof-side iteration observers for the activation scheduler. -/
set_option maxHeartbeats 400000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

def workerIterLogged (w : Worker) (pid : Option Nat) (step : GhostM Bool) (afterItem : GhostM Bool) : GhostM IterResult := do
  let _ := (w, pid)
  if !(← step) then return .ended
  return if ← afterItem then .yielded else .continued

theorem workerIterLogged_erases (w : Worker) (pid : Option Nat)
    (gs ga : GhostM Bool) (os oa : M Bool) (hs : Erases gs os) (ha : Erases ga oa) :
    Erases (workerIterLogged w pid gs ga) (workerIter w pid os oa) := by
  unfold workerIterLogged workerIter
  repeat' ghost_step

def workerLoopLogged (w : Worker) (pid : Option Nat) (step : GhostM Bool) (afterItem : GhostM Unit) (bound : Nat)
    (drained : String) : GhostM Unit := do
  for _ in [0:bound] do
    if (← workerIterLogged w pid step (do afterItem; pure false)) == .ended then return
  invariant drained

theorem workerLoopLogged_erases (w : Worker) (pid : Option Nat)
    (gs : GhostM Bool) (ga : GhostM Unit) (os : M Bool) (oa : M Unit)
    (bound : Nat) (drained : String) (hs : Erases gs os) (ha : Erases ga oa) :
    Erases (workerLoopLogged w pid gs ga bound drained) (workerLoop w pid os oa bound drained) := by
  unfold workerLoopLogged workerLoop
  repeat' first | with_reducible apply workerIterLogged_erases | ghost_step

def runWorkerLogged (w : Worker) (body : GhostM Unit) : GhostM Unit := do
  _ ← hidden (.sectionStart w)
  -- W7 stream H (13.2 (ii)): a NET_RX section's steps carry its ordinal in
  -- the operation, after hidden has advanced its count; a softirq never
  -- nests in a softirq, so the ordinal is cleared at its end
  if w == .netRx then
    modifyWorld fun s => { s with netRxSection := s.netRxSections }
  body
  if w == .netRx then modifyWorld fun s => { s with netRxSection := 0 }
  _ ← hidden (.sectionStop w)

theorem runWorkerLogged_erases (w : Worker) (g : GhostM Unit) (o : M Unit)
    (h : Erases g o) : Erases (runWorkerLogged w g) (Env.runWorker w o) := by
  unfold runWorkerLogged Env.runWorker
  repeat' ghost_step

def encryptStepLogged (checksumHelp : Packet → M Packet) (softirq : GhostM Unit) : GhostM Bool := do
  -- ptr_ring_consume_bh: its spin_unlock_bh runs a pending softirq; the
  -- head's slot, discarded by the batch rule
  softirq
  match (← getDev).encryptQueue.consume with
  | (none, _) =>
    _ ← branch .encWorkerConsumed false
    return false
  | (some first, ring) =>
    _ ← branch .encWorkerConsumed true
    modifyDev fun d => { d with encryptQueue := ring }
    let some headId := first.head? | invariant "an empty ring item"
    let head ← getTxSkb headId
    -- skb_list_walk_safe(first, skb, next): each skb encrypted in place
    -- (the store, review 4.2)
    let mut state := PacketState.crypted
    for id in first do
      _ ← branch .encWorkerSkbIterate true
      let encrypted ← encryptPacket checksumHelp head.keypair (← getTxSkb id)
      if ← branch .encWorkerEncrypted encrypted.isSome then
        -- wg_reset_packet(skb, true) (a cut point)
        setTxSkb id fun p => { p with bytes := encrypted.getD [] }
      else
        state := .dead   -- break
        break
    if state == .crypted then _ ← branch .encWorkerSkbIterate false
    enqueuePerPeerTx first state
    return true

theorem encryptStepLogged_erases (checksum : Packet → M Packet) (gs : GhostM Unit) (os : M Unit)
    (hs : Erases gs os) : Erases (encryptStepLogged checksum gs) (WG.encryptStep checksum os) := by
  unfold encryptStepLogged WG.encryptStep
  repeat' ghost_step

def encryptIterLogged (checksumHelp : Packet → M Packet) (softirq : GhostM Unit) (needResched : GhostM Bool) : GhostM IterResult :=
  workerIterLogged .encryptWorker none (encryptStepLogged checksumHelp softirq)
    (do branch .encWorkerNeedResched (← needResched))

theorem encryptIterLogged_erases (checksum : Packet → M Packet)
    (gs : GhostM Unit) (gr : GhostM Bool) (os : M Unit) (orr : M Bool)
    (hs : Erases gs os) (hr : Erases gr orr) :
    Erases (encryptIterLogged checksum gs gr) (WG.encryptIter checksum os orr) := by
  unfold encryptIterLogged WG.encryptIter
  apply workerIterLogged_erases
  · exact encryptStepLogged_erases _ _ _ hs
  · repeat' ghost_step

def txIterLogged (pid : PeerId) (needResched : GhostM Bool) : GhostM IterResult :=
  workerIterLogged .txWorker (some pid) (liftM (WG.txStep pid))
    (do branch .txNeedResched (← needResched))

theorem txIterLogged_erases (pid : PeerId) (g : GhostM Bool) (o : M Bool) (h : Erases g o) :
    Erases (txIterLogged pid g) (WG.txIter pid o) := by
  unfold txIterLogged WG.txIter
  apply workerIterLogged_erases
  · exact erases_liftM _
  · repeat' ghost_step

def handshakeReceiveWorkerLogged (condResched : GhostM Unit) : GhostM Unit :=
  workerLoopLogged .receiveWorker none (liftM receiveStep) condResched
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

theorem handshakeReceiveWorkerLogged_erases (g : GhostM Unit) (o : M Unit) (h : Erases g o) :
    Erases (handshakeReceiveWorkerLogged g) (WG.handshakeReceiveWorker o) := by
  unfold handshakeReceiveWorkerLogged WG.handshakeReceiveWorker
  exact workerLoopLogged_erases _ _ _ _ _ _ _ _ (erases_liftM _) h

def enqueuePerPeerRxLogged (irqExit : GhostM Unit) (id : SkbId) (state : PacketState) : GhostM Unit := do
  let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)   -- PACKET_PEER(skb)
  peerGet pid
  let p ← getPeer pid
  -- atomic_set_release(&PACKET_CB(skb)->state, state): the one skb the
  -- peer's rx_queue (queued or peeked, W7) and the worker name (review 4.2)
  if !(p.rxQueue.all.contains id) then
    invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => { q with state }
  -- napi_schedule: NAPI_STATE_SCHED, and NET_RX raised (a cut point)
  setPeer pid { p with napiScheduled := true }
  irqExit
  peerPut (some pid)

theorem enqueuePerPeerRxLogged_erases (g : GhostM Unit) (o : M Unit) (id : SkbId)
    (state : PacketState) (h : Erases g o) :
    Erases (enqueuePerPeerRxLogged g id state) (WG.enqueuePerPeerRx o id state) := by
  unfold enqueuePerPeerRxLogged WG.enqueuePerPeerRx
  repeat' ghost_step

def decryptStepLogged (softirq irqExit : GhostM Unit) : GhostM Bool := do
  -- ptr_ring_consume_bh: its spin_unlock_bh runs a pending softirq
  softirq
  match (← getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← branch .decWorkerConsumed false
    return false
  | (some id, ring) =>
    _ ← branch .decWorkerConsumed true
    modifyDev fun d => { d with decryptQueue := ring }
    let decrypted ← decryptPacket (← getRxSkb id)
    -- `likely(decrypt_packet(...)) ? PACKET_STATE_CRYPTED : PACKET_STATE_DEAD`:
    -- the plaintext replaces the message in the one skb (review 4.2)
    if ← branch .decWorkerDecrypted decrypted.isSome then
      let some d := decrypted | invariant "unreachable"
      setRxSkb id fun _ => d
      enqueuePerPeerRxLogged irqExit id .crypted
    else enqueuePerPeerRxLogged irqExit id .dead
    -- an interrupt's exit may run the raised softirq before the test
    softirq
    return true

theorem decryptStepLogged_erases (gs gi : GhostM Unit) (os oi : M Unit)
    (hs : Erases gs os) (hi : Erases gi oi) :
    Erases (decryptStepLogged gs gi) (WG.decryptStep os oi) := by
  unfold decryptStepLogged WG.decryptStep
  repeat' first | with_reducible apply enqueuePerPeerRxLogged_erases | ghost_step

def decryptIterLogged (softirq irqExit : GhostM Unit) (needResched : GhostM Bool) : GhostM IterResult :=
  workerIterLogged .decryptWorker none (decryptStepLogged softirq irqExit)
    (do branch .decWorkerNeedResched (← needResched))

theorem decryptIterLogged_erases (gs gi : GhostM Unit) (os oi : M Unit) (gr : GhostM Bool) (orr : M Bool)
    (hs : Erases gs os) (hi : Erases gi oi) (hr : Erases gr orr) :
    Erases (decryptIterLogged gs gi gr) (WG.decryptIter os oi orr) := by
  unfold decryptIterLogged WG.decryptIter
  apply workerIterLogged_erases
  · exact decryptStepLogged_erases _ _ _ _ hs hi
  · repeat' ghost_step

end Leanux.Proofs.Logged
