import Leanux.WG.Device
import Leanux.WG.Receive
import Leanux.WG.Data

/-!
# drivers/net/wireguard/receive.c — data messages: the decrypt worker and the NAPI poll

`wg_packet_consume_data` (Receive.lean) puts a data message on the device's
decrypt queue and on its peer's `rx_queue`. The environment
(`Leanux/Env.lean`) runs the decrypt worker after the injecting operation's
NET_RX section, and the NAPI poll (`wg_packet_rx_poll`) in the NET_RX
section the decrypt worker's `napi_schedule` raised, wherever the records
place it (docs/2026-10-04-d2-data-plane.md, section 5).

`decrypt_packet` is mirrored with every value: ChaCha20-Poly1305 under the
keypair's receiving key and the message's counter (the NoiseCrypto
reference). `counter_validate` is the full RFC 6479 bitmap over
`Keypair.receivingCounter`. `wg_packet_consume_data_done` mirrors every
branch; the inner packet it hands to `napi_gro_receive` is delivered at
`napi_complete_done` by the environment's delivery cut.

Cut points:
- `skb_cow_data` and `skb_to_sgvec`, whose failures are environment
  outcomes (`envOk`);
- `wg_reset_packet`, `dev_kfree_skb`, `napi_schedule` (the NAPI state is
  `Peer.napiScheduled`), `net_rx_action`, `napi_gro_receive` and
  `napi_complete_done` (the environment delivers what GRO received);
- `ip_tunnel_parse_protocol` and `INET_ECN_decapsulate` (include/net), whose
  results are computed here;
- `dev_sw_netstats_rx_add` (wg0's own rx counters: nothing on the modeled
  paths reads them).
-/

namespace Leanux.WG
open Leanux

/-- `NAPI_POLL_WEIGHT`: the weight `netif_napi_add` gives the peer's NAPI
    context (peer.c:54), which `napi_poll` passes as the budget. -/
def NAPI_POLL_WEIGHT : Nat := 64

/-- `COUNTER_BITS_TOTAL` (noise.h): the replay bitmap's bits. -/
def COUNTER_BITS_TOTAL : Nat := 8192

/-- The big-endian integer of `n` bytes at `off`. -/
def beAt (bs : List UInt8) (off n : Nat) : Nat :=
  ((bs.drop off).take n).foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The little-endian 64-bit word at `off`. -/
def u64le (bs : List UInt8) (off : Nat) : Nat :=
  ((bs.drop off).take 8).foldr (fun b acc => acc * 256 + b.toNat) 0

/-- update_rx_stats (receive.c:19-23): `peer->rx_bytes`; the device's
    `dev_sw_netstats_rx_add` is a cut point. -/
def updateRxStats (pid : PeerId) (len : Nat) : M Unit := do
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + len }

/-- decrypt_packet (receive.c:242-292): the packet with its counter
    (`PACKET_CB(skb)->nonce`) and its plaintext (the tag trimmed), or `none`. -/
def decryptPacket (pkt : RxPacket) : M (Option RxPacket) := do
  -- `unlikely(!keypair)`: consume_data enqueues only with a keypair
  if ← branch .decNoKeypair false then return none
  let k ← getKeypair pkt.keypair
  -- `!is_valid || wg_birthdate_has_expired(birthdate, REJECT_AFTER_TIME) ||
  -- receiving_counter.counter >= REJECT_AFTER_MESSAGES`
  let reject ← orM (branch .decKeyInvalid !k.receiving.isValid) do
    orM (do branch .decKeyExpired (← birthdateHasExpired k.receiving.birthdate REJECT_AFTER_TIME))
      (branch .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES))
  if reject then
    let k ← getKeypair pkt.keypair
    setKeypair pkt.keypair { k with receiving := { k.receiving with isValid := false } }
    return none
  let nonce := u64le pkt.bytes 8   -- le64_to_cpu(((struct message_data *)skb->data)->counter)
  -- `num_frags = skb_cow_data(skb, 0, &trailer)`; `num_frags < 0 || num_frags > ARRAY_SIZE(sg)`
  let cowOk ← envOk .skbCowData
  if ← orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false) then return none
  if ← branch .decSgvecFailed !(← envOk .skbToSgvec) then return none
  -- chacha20poly1305_decrypt_sg_inplace(sg, skb->len, NULL, 0, nonce, receiving.key)
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← branch .decDecryptFailed plain.isNone then return none
  let some bytes := plain | invariant "unreachable"
  -- `pskb_trim(skb, skb->len - noise_encrypted_len(0))` of a linear skb
  if ← branch .decTrimFailed false then return none
  return some { pkt with nonce, bytes }

/-- wg_queue_enqueue_per_peer_rx (queueing.h:193-203): a reference to the
    packet's peer for the duration, the packet's state (the same skb is on
    the peer's `rx_queue`), and `napi_schedule`. -/
def enqueuePerPeerRx (pkt : RxPacket) (state : PacketState) : M Unit := do
  let pid := (← getKeypair pkt.keypair).peer   -- PACKET_PEER(skb)
  peerGet pid
  let p ← getPeer pid
  -- atomic_set_release(&PACKET_CB(skb)->state, state)
  let some i := p.rxQueue.findIdx? (fun q => q.keypair == pkt.keypair && q.state == .uncrypted)
    | invariant "a decrypted packet that is not on its peer's rx_queue"
  -- napi_schedule: NAPI_STATE_SCHED, and NET_RX raised (a cut point)
  setPeer pid { p with rxQueue := p.rxQueue.set i { pkt with state }, napiScheduled := true }
  peerPut (some pid)

/-- wg_packet_decrypt_worker (receive.c:493-507): drains the decrypt queue.
    `softirq` is the environment's NET_RX placement (the NAPI poll the
    worker's `napi_schedule` raised, where the records put it);
    `needResched` its scheduler, as for the encrypt worker. -/
def decryptWorker (softirq : M Unit) (needResched : M Bool) : M Unit := do
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- ptr_ring_consume_bh: its spin_unlock_bh runs a pending softirq
    softirq
    match (← getDev).decryptQueue with
    | [] =>
      _ ← branch .decWorkerConsumed false
      return
    | pkt :: rest =>
      _ ← branch .decWorkerConsumed true
      modifyDev fun d => { d with decryptQueue := rest }
      let decrypted ← decryptPacket pkt
      -- `likely(decrypt_packet(...)) ? PACKET_STATE_CRYPTED : PACKET_STATE_DEAD`
      if ← branch .decWorkerDecrypted decrypted.isSome then
        let some d := decrypted | invariant "unreachable"
        enqueuePerPeerRx d .crypted
      else enqueuePerPeerRx pkt .dead
      -- an interrupt's exit may run the raised softirq before the test
      softirq
      _ ← branch .decWorkerNeedResched (← needResched)
  invariant "the decrypt queue did not drain"

/-- counter_validate (receive.c:295-331): RFC 6479 over the keypair's
    `receiving_counter` (`counter` is the highest counter seen plus one;
    `backtrack` the bitmap of 128 words). -/
def counterValidate (kp : KeypairId) (theirs : Nat) : M Bool := do
  let k ← getKeypair kp
  let c := k.receivingCounter
  -- `counter->counter >= REJECT_AFTER_MESSAGES + 1 || their_counter >= REJECT_AFTER_MESSAGES`
  if ← orM (branch .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1))
      (branch .ctrRejectTheirs (theirs ≥ REJECT_AFTER_MESSAGES)) then return false
  let theirs := theirs + 1   -- ++their_counter
  if ← branch .ctrTooOld (COUNTER_WINDOW_SIZE + theirs < c.counter) then return false
  let words := COUNTER_BITS_TOTAL / BITS_PER_LONG
  let index := theirs / BITS_PER_LONG   -- their_counter >> ilog2(BITS_PER_LONG)
  let mut backtrack := c.backtrack
  let mut counter := c.counter
  if ← branch .ctrAdvance (theirs > c.counter) then
    let indexCurrent := c.counter / BITS_PER_LONG
    let top := min (index - indexCurrent) words
    for i in [1:top + 1] do
      _ ← branch .ctrClearIter true
      backtrack := backtrack.set! ((i + indexCurrent) % words) 0
    _ ← branch .ctrClearIter false
    counter := theirs
  -- `!test_and_set_bit(their_counter & (BITS_PER_LONG - 1), &backtrack[index & (words - 1)])`
  let index := index % words
  let bit := theirs % BITS_PER_LONG
  let word := backtrack[index]!
  backtrack := backtrack.set! index (word ||| (1 <<< bit))
  setKeypair kp { k with receivingCounter := { counter, backtrack } }
  return (word >>> bit) % 2 == 0

/-- wg_allowedips_lookup_src (allowedips.c:367-375): `lookup` on the inner
    packet's source. (Mirrored here rather than in AllowedIps.lean because
    `lookup` is in Device.lean.) -/
def lookupSrc (protocol : Nat) (bytes : List UInt8) : M (Option PeerId) := do
  let t := (← getDev).peerAllowedips
  if ← branch .lookupSrcV4 (protocol == 4) then return ← lookup t.root4 32 (beAt bytes 12 4)
  if ← branch .lookupSrcV6 (protocol == 6) then return ← lookup t.root6 128 (beAt bytes 8 16)
  return none

/-- keep_key_fresh (receive.c:220-240), the receive side: once per
    handshake, an initiation when the current keypair wg0 initiated is
    close to `REJECT_AFTER_TIME`. -/
def keepKeyFreshRx (pid : PeerId) : M Unit := do
  if ← branch .rxFreshSentLastminute (← getPeer pid).sentLastminuteHandshake then return
  let current := (← getPeer pid).keypairCurrent
  -- `keypair && is_valid && i_am_the_initiator &&
  -- wg_birthdate_has_expired(birthdate, REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)`
  let send ← andM (branch .rxFreshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    andM (branch .rxFreshValid k.sending.isValid) do
      andM (branch .rxFreshInitiator k.iAmTheInitiator) do
        branch .rxFreshExpired
          (← birthdateHasExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT))
  if ← branch .rxFreshSend send then
    setPeer pid { (← getPeer pid) with sentLastminuteHandshake := true }
    sendQueuedHandshakeInitiation pid false

/-- ip_tunnel_parse_protocol (include/net/ip_tunnels.h) of a linear inner
    packet: 4 (ETH_P_IP), 6 (ETH_P_IPV6) or 0. -/
def ipTunnelParseProtocol (bytes : List UInt8) : Nat :=
  let version := (bytes.headD 0).toNat / 16
  if bytes.length ≥ 20 && version == 4 then 4
  else if bytes.length ≥ 40 && version == 6 then 6
  else 0

/-- INET_ECN_decapsulate (include/net/inet_ecn.h): with a not-ECT outer DS
    field it changes nothing, whatever the inner field. -/
def inetEcnDecapsulate (outer _inner : Nat) : M Unit := do
  if outer % 4 != 0 then unsupported "INET_ECN_decapsulate with an ECN-capable outer header"

/-- The device's error counters (`DEV_STATS_INC`). -/
inductive Dishonest where
  | peer | type | size

def dishonest (why : Dishonest) : M Unit :=
  modifyDev fun d => match why with
    | .peer | .type => { d with rxErrors := d.rxErrors + 1, rxFrameErrors := d.rxFrameErrors + 1 }
    | .size => { d with rxErrors := d.rxErrors + 1, rxLengthErrors := d.rxLengthErrors + 1 }

/-- wg_packet_consume_data_done (receive.c:335-436): the inner packet handed
    to `napi_gro_receive`, if any. -/
def consumeDataDone (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : M (Option (List UInt8)) := do
  setPeerEndpoint pid endpoint
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : M (Option (List UInt8)) := do
    dishonest why   -- then packet_processed: dev_kfree_skb
    return none
  -- a packet with length 0 is a keepalive
  if ← branch .doneRxKeepalive (len == 0) then
    updateRxStats pid MESSAGE_DATA_LEN_0   -- message_data_len(0)
    return none
  timersDataReceived pid
  -- `skb_network_header(skb) < skb->head`: the decrypted skb's network header is its data
  if ← branch .doneNetworkBelowHead false then return ← reject .size
  -- `!(pskb_network_may_pull(skb, sizeof(struct iphdr)) && (version == 4 ||
  -- (version == 6 && pskb_network_may_pull(skb, sizeof(struct ipv6hdr)))))`
  let version := (bytes.headD 0).toNat / 16
  let honest ← andM (branch .doneMayPullV4 (len ≥ 20)) do
    orM (branch .doneVersion4 (version == 4)) do
      andM (branch .doneVersion6 (version == 6)) (branch .doneMayPullV6 (len ≥ 40))
  if !honest then return ← reject .type
  -- skb->ip_summed = CHECKSUM_UNNECESSARY; csum_level = ~0
  let protocol := ipTunnelParseProtocol bytes
  -- PACKET_CB(skb)->ds: the outer DS field wg_packet_receive read
  let ds := pkt.source.tos
  let mut ipLen := 0
  if ← branch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← branch .doneV4TooShort (ipLen < 20) then return ← reject .size
    inetEcnDecapsulate ds (beAt bytes 1 1)
  else if ← branch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    inetEcnDecapsulate ds (beAt bytes 0 2 / 16 % 256)   -- ipv6_get_dsfield
  else return ← reject .type
  if ← branch .doneLenBeyond (ipLen > len) then return ← reject .size
  let lenBeforeTrim := len
  -- pskb_trim(skb, len) of a linear skb
  if ← branch .doneTrimFailed false then return none
  let routed ← lookupSrc protocol bytes
  peerPut routed   -- we don't need the extra reference
  if ← branch .doneDishonestPeer (routed != some pid) then return ← reject .peer
  -- napi_gro_receive(&peer->napi, skb) (a cut point)
  updateRxStats pid (lenBeforeTrim + MESSAGE_DATA_LEN_0)   -- message_data_len(len_before_trim)
  return some (bytes.take ipLen)

/-- wg_packet_rx_poll (receive.c:438-491), the peer's NAPI poll, with the
    budget `napi_poll` passes. `napiCompleteDone` is the environment's cut
    at `napi_complete_done`: GRO's flush delivers the packets
    `napi_gro_receive` received. -/
def rxPoll (pid : PeerId) (budget : Nat) (napiCompleteDone : List (List UInt8) → M Unit) : M Nat := do
  if ← branch .rxPollNoBudget (budget == 0) then return 0
  let mut workDone := 0
  let mut gro : List (List UInt8) := []
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- wg_prev_queue_peek: `queue->peeked` is NULL (dropped after every packet)
    _ ← branch .prevQueuePeeked false
    let first := (← getPeer pid).rxQueue.head?
    -- `(skb = peek) != NULL && (state = ...) != PACKET_STATE_UNCRYPTED`
    let go ← andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      if f.state == .uncrypted then unsupported "the NAPI poll meets an uncrypted packet (it stays peeked)"
      branch .rxPollNotUncrypted true
    if !go then
      drained := true
      break
    let some pkt := first | invariant "unreachable"
    if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
    -- wg_prev_queue_drop_peeked
    setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.drop 1 }
    let mut free := true
    if !(← branch .rxPollNotCrypted (pkt.state != .crypted)) then
      if !(← branch .rxPollCounterInvalid !(← counterValidate pkt.keypair pkt.nonce)) then
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
    workDone := workDone + 1
    if ← branch .rxPollBudgetDone (workDone ≥ budget) then break
  if !drained && workDone < budget then invariant "the rx_queue did not drain"
  if ← branch .rxPollComplete (workDone < budget) then
    -- napi_complete_done: NAPI_STATE_SCHED cleared, GRO flushed
    setPeer pid { (← getPeer pid) with napiScheduled := false }
    napiCompleteDone gro
  else unsupported "a NAPI poll that used its whole budget (a repoll)"
  return workDone

end Leanux.WG
