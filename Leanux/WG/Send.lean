import Leanux.WG.Keypair

/-!
# drivers/net/wireguard/send.c — staging, handshake queueing, and handing
# staged packets to the encrypt worker

Without a session keypair (`current_keypair` is NULL) staged packets stay
staged and a handshake initiation is queued. With one, the staged packets get
nonces from the keypair's `sending_counter` and go to the device's encrypt
queue and the peer's transmit queue (`wg_packet_create_data`); the encrypt and
tx workers are in `Leanux/WG/Data.lean`, run by the environment
(`Leanux/Env.lean`).

The handshake send worker (`wg_packet_handshake_send_worker`) is mirrored in
`Leanux/WG/Handshake.lean`; the environment (`Leanux/Env.lean`) runs it when
the queuing operation waits for it. Within the queuing system call, paths that
read what the worker changes are `unsupported` unless the work was queued in
that same call (`requireNotPending`).

Domain limits (fail-noisy): a staged payload packet meeting a session (its
inner IP header, `ip_tunnel_ecn_encap`, and its encryption are not
mirrored), and more than one item in a crypt queue (the per-device ring or
the peer's `tx_queue`, whose MPSC internals in queueing.c are mirrored as "the
queue yields the packet").
-/

namespace Leanux.WG
open Leanux

def MAX_STAGED_PACKETS : Nat := 128
def ENOSPC : Int := 28
def EPIPE : Int := 32
/-- `MAX_QUEUED_PACKETS` (messages.h:53): the encrypt ring's size
    (`wg_packet_queue_init`) and the bound of a peer's `tx_queue`. -/
def MAX_QUEUED_PACKETS : Nat := 1024
/-- `REJECT_AFTER_TIME`, `REKEY_AFTER_TIME` (seconds) and the message
    counters' bounds (messages.h:41-46). -/
def REJECT_AFTER_TIME : Nat := 180
def REKEY_AFTER_TIME : Nat := 120
def REKEY_AFTER_MESSAGES : Nat := 2 ^ 60
def COUNTER_WINDOW_SIZE : Nat := 8192 - 64   -- COUNTER_BITS_TOTAL - BITS_PER_LONG
def REJECT_AFTER_MESSAGES : Nat := (2 ^ 64 - 1) - COUNTER_WINDOW_SIZE - 1
/-- `dev->mtu` as `wg_setup` (device.c:280-296) sets it: `ETH_DATA_LEN -
    overhead`, with `overhead = MESSAGE_MINIMUM_LENGTH + sizeof(struct udphdr)
    + max(sizeof(struct ipv6hdr), sizeof(struct iphdr))`. No operation in the
    domain changes it. -/
def DEVICE_MTU : Nat := 1500 - (32 + 8 + 40)

/-- wg_packet_send_queued_handshake_initiation (send.c:55-83). The pending
    check comes first: once queued, `queue_work` and `last_sent_handshake`
    depend on the worker's timing. -/
def sendQueuedHandshakeInitiation (pid : PeerId) (isRetry : Bool) : M Unit := do
  requireNotPending pid "queueing a handshake"
  -- `peer->timer_handshake_attempts = 0` (timers are cut points)
  _ ← branch .queuedNotRetry !isRetry
  let p ← getPeer pid
  -- `!wg_birthdate_has_expired(last_sent_handshake, REKEY_TIMEOUT) || is_dead`
  if ← branch .queuedNotExpired !(← birthdateHasExpired p.lastSentHandshake REKEY_TIMEOUT) then return
  if ← branch .queuedDead p.isDead then return
  peerGet pid
  -- `!queue_work(...)`: false iff the work is still queued (queued earlier in
  -- this call; requireNotPending excludes every other pending case)
  if ← branch .queuedAlreadyQueued p.handshakePending then
    peerPut (some pid)
    return
  setPeer pid { (← getPeer pid) with handshakePending := true }
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue ++ [pid] }
  modify fun w => { w with queuedThisCall := pid :: w.queuedThisCall }

/-- wg_noise_keypair_get (noise.c:142-149) of a NULL keypair (the data
    receive path's `wg_noise_keypair_get(NULL)`, Receive.lean). -/
def keypairGetCurrent : M Unit := do
  -- `unlikely(!keypair || ...)`: `!keypair` decides
  _ ← branch .keypairGetNull true

/-- wg_cpumask_next_online (queueing.h:125-132) on this single-CPU kernel:
    `cpumask_next(n)` is `n + 1` and `nr_cpu_ids` is 1. The CPU chosen. -/
def cpumaskNextOnlineFrom (lastCpu : Int) : M Int := do
  let next := lastCpu + 1
  if ← branch .cpumaskWrap (next ≥ 1) then pure 0 else pure next

/-- wg_cpumask_choose_online (queueing.h:105-118) for a peer's
    `serial_work_cpu` (`none` is its initial `nr_cpumask_bits`) on this
    single-CPU kernel: `nr_cpu_ids` is 1 and CPU 0 is online. -/
def cpumaskChooseOnline (pid : PeerId) : M Nat := do
  let p ← getPeer pid
  -- `cpu >= nr_cpu_ids || !cpumask_test_cpu(cpu, cpu_online_mask)`
  let invalid ← do
    if ← branch .chooseCpuInvalid (p.serialWorkCpu.getD 1 ≥ 1) then pure true
    else branch .chooseCpuOffline false
  if !invalid then return p.serialWorkCpu.getD 0
  -- `cpu_index = id % cpumask_weight(cpu_online_mask)`: the weight is 1
  let cpuIndex := p.internalId % 1
  -- cpu = cpumask_first(cpu_online_mask), then cpu_index steps of cpumask_next
  for _ in [0:cpuIndex] do _ ← branch .chooseCpuIndexIterate true
  _ ← branch .chooseCpuIndexIterate false
  setPeer pid { (← getPeer pid) with serialWorkCpu := some 0 }
  return 0

/-- wg_queue_enqueue_per_peer_tx (queueing.h:180-191): a reference to the
    packet's peer (`PACKET_PEER`, the keypair's peer) for the duration, the
    packet's state, and the peer's `transmit_packet_work` queued on its
    serial CPU. -/
def enqueuePerPeerTx (pkt : DataPacket) (state : PacketState) : M Unit := do
  let pid := (← getKeypair pkt.keypair).peer
  peerGet pid
  -- atomic_set_release(&PACKET_CB(skb)->state, state): the same skb is on
  -- the peer's tx_queue
  let p ← getPeer pid
  if !p.txQueue.any (fun q => q.keypair == pkt.keypair && q.nonce == pkt.nonce) then
    invariant "a packet for the tx worker that is not on its peer's tx_queue"
  setPeer pid { p with txQueue := p.txQueue.map fun q =>
    if q.keypair == pkt.keypair && q.nonce == pkt.nonce then { pkt with state } else q }
  _ ← cpumaskChooseOnline pid
  -- queue_work_on(cpu, packet_crypt_wq, &peer->transmit_packet_work): a no-op
  -- while the work is pending
  if !(← getDev).txWorkQueue.contains pid then
    modifyDev fun d => { d with txWorkQueue := d.txWorkQueue ++ [pid] }
  peerPut (some pid)

/-- wg_queue_enqueue_per_device_and_peer (queueing.h:157-178): 0, `-ENOSPC`
    or `-EPIPE`. -/
def enqueuePerDeviceAndPeer (pid : PeerId) (pkt : DataPacket) : M Int := do
  -- atomic_set_release(&PACKET_CB(skb)->state, PACKET_STATE_UNCRYPTED)
  let pkt := { pkt with state := .uncrypted }
  -- `!wg_prev_queue_enqueue(peer_queue, skb)`: `atomic_add_unless(&count, 1,
  -- MAX_QUEUED_PACKETS)` (queueing.c, mirrored as its result)
  let p ← getPeer pid
  if ← branch .enqueuePeerQueueFull (p.txQueue.length ≥ MAX_QUEUED_PACKETS) then return -ENOSPC
  if !p.txQueue.isEmpty then unsupported "more than one packet on a peer's tx_queue"
  setPeer pid { p with txQueue := p.txQueue ++ [pkt] }
  let d ← getDev
  let cpu ← cpumaskNextOnlineFrom d.encryptLastCpu
  modifyDev fun d => { d with encryptLastCpu := cpu }
  -- `ptr_ring_produce_bh(&device_queue->ring, skb)` fails on a full ring
  if ← branch .enqueueRingFull (d.encryptQueue.length ≥ MAX_QUEUED_PACKETS) then return -EPIPE
  if !d.encryptQueue.isEmpty then unsupported "more than one item in the encrypt queue"
  -- queue_work_on(cpu, wq, &per_cpu_ptr(device_queue->worker, cpu)->work):
  -- the environment runs the encrypt worker while its ring holds packets
  modifyDev fun d => { d with encryptQueue := d.encryptQueue ++ [pkt] }
  return 0

/-- wg_packet_create_data (send.c:311-331). The packet holds a keypair
    reference and a peer reference, which the tx worker drops (or this
    function, on failure). -/
def createData (pid : PeerId) (pkt : DataPacket) : M Unit := do
  let ret ← do
    if ← branch .createDataDead (← getPeer pid).isDead then pure (-EINVAL)
    else
      let ret ← enqueuePerDeviceAndPeer pid pkt
      if ← branch .createDataEpipe (ret == -EPIPE) then enqueuePerPeerTx pkt .dead
      pure ret
  -- `likely(!ret || ret == -EPIPE)`
  if ← branch .createDataOk (ret == 0) then return
  if ← branch .createDataOkEpipe (ret == -EPIPE) then return
  keypairPut (some pkt.keypair) false
  peerPut (some pid)
  -- kfree_skb_list(first)

/-- wg_packet_send_staged_packets (send.c:342-414). -/
def sendStagedPackets (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  -- skb_queue_splice_init onto the local list, then
  if ← branch .stagedEmpty p.staged.isEmpty then return
  let packets := p.staged
  setPeer pid { p with staged := [] }
  -- wg_noise_keypair_get(rcu_dereference_bh(peer->keypairs.current_keypair))
  let keypair ← keypairGet p.keypairCurrent
  -- out_invalid: `keypair->sending.is_valid = false`; out_nokey: the put, the
  -- orphan walk, the packets back on the staged queue, and a handshake
  let outNokey (invalid : Bool) : M Unit := do
    if invalid then
      let some id := keypair | invariant "unreachable"
      let k ← getKeypair id
      setKeypair id { k with sending := { k.sending with isValid := false } }
    keypairPut keypair false
    for _ in packets do _ ← branch .stagedOrphanWalk true   -- skb_orphan
    _ ← branch .stagedOrphanWalk false
    -- skb_queue_splice: the packets go back at the head of the staged queue
    setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }
    sendQueuedHandshakeInitiation pid false
  if ← branch .stagedNoKeypair keypair.isNone then return ← outNokey false
  let some id := keypair | invariant "unreachable"
  let k ← getKeypair id
  if ← branch .stagedKeyInvalid !k.sending.isValid then return ← outNokey false
  if ← branch .stagedBirthdateExpired (← birthdateHasExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← outNokey true
  -- the nonces, in queue order
  let mut nonces : List Nat := []
  for pkt in packets do
    _ ← branch .stagedNonceIterate true
    -- `PACKET_CB(skb)->ds = ip_tunnel_ecn_encap(0, ip_hdr(skb), skb)` reads
    -- the inner IP header: a keepalive has none (protocol 0, ds 0)
    if pkt.bytes.length != 0 then unsupported "a staged payload packet meeting a session"
    let k ← getKeypair id
    let nonce := k.sendingCounter   -- atomic64_inc_return(&sending_counter) - 1
    setKeypair id { k with sendingCounter := k.sendingCounter + 1 }
    if ← branch .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) then return ← outNokey true
    nonces := nonces ++ [nonce]
  _ ← branch .stagedNonceIterate false
  -- the walk admitted only keepalives, and a keepalive is staged only on an
  -- empty queue: one packet
  let [nonce] := nonces | invariant "more than one keepalive staged"
  -- wg_peer_get(keypair->entry.peer); PACKET_CB(first)->keypair = keypair
  peerGet (← getKeypair id).peer
  createData pid { peer := pid, keypair := id, nonce, plaintext := {} }

/-- wg_packet_send_keepalive (send.c:221-240): a keepalive is staged only
    when nothing else is. -/
def sendKeepalive (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  if ← branch .keepaliveStagedEmpty p.staged.isEmpty then
    if ← branch .keepaliveNoMem !(← envOk .allocSkb) then return
    -- `PACKET_CB(skb)->mtu = skb->dev->mtu` (DEVICE_MTU; Data.lean pads with it)
    setPeer pid { p with staged := p.staged ++ [{ mtu := DEVICE_MTU }] }
  sendStagedPackets pid

end Leanux.WG
