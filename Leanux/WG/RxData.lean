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
- `skb_cow_data`, whose failure is an allocation outcome (`hiddenAlloc`;
  lax, count 0 on this fixture), and `skb_to_sgvec`, which cannot fail for
  a linear skb;
- `wg_reset_packet`, `dev_kfree_skb`, `napi_schedule` (the NAPI state is
  `Peer.napiScheduled`), `net_rx_action`, `napi_gro_receive` and
  `napi_complete_done` (the environment delivers what GRO received);
- `ip_tunnel_parse_protocol` (out of line in net/ipv4), whose result is
  computed here;
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
  -- dev_sw_netstats_rx_add(peer->device->dev, len): the device tstats (W5, 2.6)
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len }
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
    orM (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
      (branchCmp .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
        k.receivingCounter.counter REJECT_AFTER_MESSAGES)
  if reject then
    let k ← getKeypair pkt.keypair
    setKeypair pkt.keypair { k with receiving := { k.receiving with isValid := false } }
    return none
  let nonce := u64le pkt.bytes 8   -- le64_to_cpu(((struct message_data *)skb->data)->counter)
  -- `num_frags = skb_cow_data(skb, 0, &trailer)`; `num_frags < 0 || num_frags > ARRAY_SIZE(sg)`
  let cowOk ← hiddenAlloc .skbCowDataRx
  if ← orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false) then return none
  -- `skb_to_sgvec` < 0: not an allocation (docs/2026-10-05-a-alloc.md 6.4);
  -- a linear skb: `__skb_to_sgvec` returns 1
  if ← branch .decSgvecFailed false then return none
  -- chacha20poly1305_decrypt_sg_inplace(sg, skb->len, NULL, 0, nonce, receiving.key)
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← branch .decDecryptFailed plain.isNone then return none
  let some bytes := plain | invariant "unreachable"
  -- `pskb_trim(skb, skb->len - noise_encrypted_len(0))` of a linear skb
  if ← branch .decTrimFailed false then return none
  return some { pkt with nonce, bytes }

/-- wg_packet_decrypt_worker (receive.c:493-507): drains the decrypt queue.
    `softirq` is the environment's NET_RX placement (the NAPI poll the
    worker's `napi_schedule` raised, where the records put it), and
    `irqExit` its placement inside `wg_queue_enqueue_per_peer_rx`;
    `needResched` its scheduler, as for the encrypt worker. -/
def decryptStep [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (softirq irqExit : m Unit) : m Bool := do
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
      enqueuePerPeerRx irqExit id .crypted
    else enqueuePerPeerRx irqExit id .dead
    -- an interrupt's exit may run the raised softirq before the test
    softirq
    return true

/-- One iteration of the loop: `decryptStep`, then `cond_resched()` and its
    decision (W7 phase 2: the environment's scheduler drives the iterations,
    `workerIter`). -/
def decryptIter [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (softirq irqExit : m Unit) (needResched : m Bool) : m IterResult :=
  workerIter .decryptWorker none (decryptStep softirq irqExit)
    (do branch .decWorkerNeedResched (← needResched))

/-- counter_validate (receive.c:295-331): RFC 6479 over the keypair's
    `receiving_counter` (`counter` is the highest counter seen plus one;
    `backtrack` the bitmap of 128 words). -/
def counterValidate (kp : KeypairId) (theirs : Nat) : M Bool := do
  let k ← getKeypair kp
  let c := k.receivingCounter
  -- `counter->counter >= REJECT_AFTER_MESSAGES + 1 || their_counter >= REJECT_AFTER_MESSAGES`
  if ← orM (branchCmp .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1) c.counter (REJECT_AFTER_MESSAGES + 1))
      (branchCmp .ctrRejectTheirs (theirs ≥ REJECT_AFTER_MESSAGES) theirs REJECT_AFTER_MESSAGES) then return false
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
      let j := (i + indexCurrent) % words
      if j ≥ backtrack.size then invariant s!"backtrack[{j}] beyond the bitmap"
      backtrack := backtrack.set! j 0
    _ ← branch .ctrClearIter false
    counter := theirs
  -- `!test_and_set_bit(their_counter & (BITS_PER_LONG - 1), &backtrack[index & (words - 1)])`
  let index := index % words
  let bit := theirs % BITS_PER_LONG
  let some word := backtrack[index]? | invariant s!"backtrack[{index}] beyond the bitmap"
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
        branchExpired .rxFreshExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)
  if ← branch .rxFreshSend send then
    setPeer pid { (← getPeer pid) with sentLastminuteHandshake := true }
    sendQueuedHandshakeInitiation pid false

/-- ip_tunnel_parse_protocol (net/ipv4/ip_tunnel_core.c, a cut point) of a
    linear inner packet: 4 (ETH_P_IP), 6 (ETH_P_IPV6) or 0. -/
def ipTunnelParseProtocol (bytes : List UInt8) : Nat :=
  let version := (bytes.headD 0).toNat / 16
  if bytes.length ≥ 20 && version == 4 then 4
  else if bytes.length ≥ 40 && version == 6 then 6
  else 0

/-- `csum16_add` on the IPv4 header's check field (W5; the environment's
    helper, `Leanux/Env/Stack.lean` has the same arithmetic): the `__sum16`
    is added in memory order on x86 with the carry folded back. `check` is
    the field's big-endian value, `addLe` the addend as the kernel's u16. -/
def csum16Add (check addLe : Nat) : Nat :=
  let le := check % 256 * 256 + check / 256
  let res := (le + addLe) % 65536
  let res := if res < le then (res + 1) % 65536 else res
  res % 256 * 256 + res / 256

/-- `IP_ECN_set_ce` (inet_ecn.h:77-103): `ecn = (tos + 1) & 3`; nothing for
    not-ECT (01) and CE (00); ECT(1) adds `htons(0xFFFD)`, ECT(0)
    `htons(0xFFFE)` to the check field (`csum16_add`), then `tos |= CE`. -/
def ipEcnSetCe (bytes : List UInt8) : M (List UInt8) := do
  let tos := (bytes.getD 1 0).toNat
  let ecn := (tos + 1) % 4
  if ← branch .ipEcnSetCeNotCapable (ecn / 2 == 0) then return bytes
  -- `htons(0xFFFB) + htons(ecn)` as the kernel's u16: 0xFBFF + ecn << 8
  let check := csum16Add (beAt bytes 10 2) (0xfbff + ecn * 256)
  return bytes.take 1 ++ [UInt8.ofNat (tos / 4 * 4 + 3)] ++ (bytes.drop 2).take 8
    ++ [UInt8.ofNat (check / 256), UInt8.ofNat (check % 256)] ++ bytes.drop 12

/-- `IP_ECN_set_ect1` (inet_ecn.h:105-113): only ECT(0) changes, `check +=
    htons(1)`, `tos ^= INET_ECN_MASK`. -/
def ipEcnSetEct1 (bytes : List UInt8) : M (List UInt8) := do
  let tos := (bytes.getD 1 0).toNat
  if ← branch .ipEcnSetEct1NotEct0 (tos % 4 != 2) then return bytes
  let check := csum16Add (beAt bytes 10 2) 0x0100
  return bytes.take 1 ++ [UInt8.ofNat (tos / 4 * 4 + 1)] ++ (bytes.drop 2).take 8
    ++ [UInt8.ofNat (check / 256), UInt8.ofNat (check % 256)] ++ bytes.drop 12

/-- `IP6_ECN_set_ce` (inet_ecn.h:134-148): nothing for a not-ECT traffic
    class; else the first word `|= htonl(INET_ECN_CE << 20)` (no checksum
    in the header; the skb is not `CHECKSUM_COMPLETE`). -/
def ip6EcnSetCe (bytes : List UInt8) : M (List UInt8) := do
  let b1 := (bytes.getD 1 0).toNat
  if ← branch .ip6EcnSetCeNotEct (b1 / 16 % 4 == 0) then return bytes
  return bytes.take 1 ++ [UInt8.ofNat (b1 ||| 0x30)] ++ bytes.drop 2

/-- `IP6_ECN_set_ect1` (inet_ecn.h:150-164): only ECT(0) changes, the word
    `^= htonl(INET_ECN_MASK << 20)`. -/
def ip6EcnSetEct1 (bytes : List UInt8) : M (List UInt8) := do
  let b1 := (bytes.getD 1 0).toNat
  if ← branch .ip6EcnSetEct1NotEct0 (b1 / 16 % 4 != 2) then return bytes
  return bytes.take 1 ++ [UInt8.ofNat (b1 ^^^ 0x30)] ++ bytes.drop 2

/-- `INET_ECN_set_ce` / `INET_ECN_set_ect1` (inet_ecn.h:172-189, 208-225):
    the protocol switch on `skb_protocol(skb, true)` (the inner header is
    long enough: `consume_data_done` pulled it). -/
def inetEcnSet (ce : Bool) (protocol : Nat) (bytes : List UInt8) : M (List UInt8) := do
  -- `skb_network_header(skb) + sizeof(hdr) <= skb_tail_pointer(skb)`
  -- (inet_ecn.h:176-177, 182-183, 212-213, 218-219): implied by the honest
  -- test before every call (receive.c:369-372 pulls the whole inner header),
  -- so it is no decision of its own; the implication is checked here,
  -- fail-closed (the receive audit's F8)
  if protocol == 4 && bytes.length < 20 then invariant "an ECN rewrite of a short IPv4 header (the honest test admitted it)"
  if protocol == 6 && bytes.length < 40 then invariant "an ECN rewrite of a short IPv6 header (the honest test admitted it)"
  if ce then
    if ← branch .inetSetCeIp (protocol == 4) then return ← ipEcnSetCe bytes
    if ← branch .inetSetCeIpv6 (protocol == 6) then return ← ip6EcnSetCe bytes
    return bytes
  else
    if ← branch .inetSetEct1Ip (protocol == 4) then return ← ipEcnSetEct1 bytes
    if ← branch .inetSetEct1Ipv6 (protocol == 6) then return ← ip6EcnSetEct1 bytes
    return bytes

/-- INET_ECN_decapsulate (inet_ecn.h:269-284) with __INET_ECN_decapsulate
    (251-267): the outer DS field's ECN bits against the inner's; the
    rewrite of the inner header (`INET_ECN_set_ce`, `INET_ECN_set_ect1`:
    W5, design 2.1) is returned; wg ignores the result code (a "drop"
    verdict still delivers). -/
def inetEcnDecapsulate (protocol outer : Nat) (bytes : List UInt8) : M (List UInt8) := do
  let inner := if protocol == 4 then (bytes.getD 1 0).toNat else beAt bytes 0 2 / 16 % 256
  let mut rc := 0
  let mut setCe := false
  if ← branch .ecnDecapInnerNotEct (inner % 4 == 0) then
    -- switch (outer & INET_ECN_MASK): case INET_ECN_NOT_ECT returns 0
    if !(← branch .ecnDecapOuterNotEct (outer % 4 == 0)) then
      rc := if outer % 4 == 3 then 2 else 1
  else setCe := outer % 4 == 3   -- INET_ECN_is_ce(outer)
  if ← branch .ecnDecapRcZero (rc == 0) then
    if ← branch .ecnDecapSetCe setCe then return ← inetEcnSet true protocol bytes
    if ← branch .ecnDecapOuterEct1 (outer % 4 == 1) then return ← inetEcnSet false protocol bytes
  return bytes

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
  let ds := pkt.ds   -- PACKET_CB(skb)->ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← branch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← branch .doneV4TooShort (ipLen < 20) then return ← reject .size
    bytes ← inetEcnDecapsulate 4 ds bytes   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← branch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← inetEcnDecapsulate 6 ds bytes   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
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

/-! ### GRO on `peer->napi` (include/net/gro.h, net/core/gro.c, net/ipv4/tcp_offload.c)

`napi_gro_receive` (receive.c:411) hands each inner packet to GRO, which
either takes it to the stack's input list at once (`GRO_NORMAL`:
`gro_normal_one`, gro.h: `list_add_tail(&napi->rx_list)`, `rx_count +=
segs`, and `gro_normal_list` to the stack once `rx_count >=
gro_normal_batch`, 8 on this kernel, net/core/hotdata.c:11) or holds it in
a `gro_hash` chain (`GRO_HELD`) until `napi_complete_done`, which flushes
the chains (`napi_gro_flush` → `napi_gro_complete` → `gro_normal_one`,
dev.c:6385) and then the list (`gro_normal_list`, dev.c:6388). UDP is taken
at once (`udp_gro_receive` flushes without a GRO socket, udp_offload.c); a
lone TCP segment is taken at once iff its payload is empty (`len < mss`
with mss 1 for a lone segment, tcp_offload.c:318, :379) or one of URG,
PSH, RST, SYN or FIN is set (:381-383), else held; every other protocol
has no holding `gro_receive` and is taken at once (`inet_gro_receive`'s
initial `flush = 1`). A second segment of the held one's flow is either
merged (coalescing, outside the domain, fail-noisy) or refused, in which
case the held one is completed to the normal list before the new one is
judged on its own (tcp_offload.c:385-386, gro.c:546-556); a second held
segment of another flow would flush in hash-bucket order: outside the
domain, fail-noisy. These rules follow the C by reading: on this fixture a
poll sees one packet (the W5+W6 design's P9), so the differential check
cannot reach the paths that distinguish them (the traces
w6_gro_pure_ack_batch and w6_gro_same_flow_flush, 2026-10-17). The state lives on the NAPI struct but is
empty between polls: `napi_complete_done` flushes all of it, and the
repoll arm that would carry it over is `unsupported`. None of these files
is anchored, so this is plain mirror control flow. (The receive
correspondence audit's F6b: the mirror delivered everything at
completion.) -/
structure GroState where
  /-- `napi->rx_list`, in order. -/
  rxList : List (List UInt8) := []
  /-- `napi->rx_count` (segments; one per packet here). -/
  rxCount : Nat := 0
  /-- The `gro_hash` chains' packets (`GRO_HELD`), at most one in the domain. -/
  held : List (List UInt8) := []

/-- `net_hotdata.gro_normal_batch` (net/core/hotdata.c:11). -/
def GRO_NORMAL_BATCH : Nat := 8

/-- gro_normal_list (gro.h): the list to the stack, if it holds anything. -/
def groNormalList [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (toStack : List (List UInt8) → m Unit) (gro : GroState) : m GroState := do
  if gro.rxCount == 0 then return gro   -- `if (!napi->rx_count) return;`
  toStack gro.rxList
  return { gro with rxList := [], rxCount := 0 }

/-- gro_normal_one (gro.h): to the list, and the list to the stack at the batch. -/
def groNormalOne [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (toStack : List (List UInt8) → m Unit) (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    m GroState := do
  let gro := { gro with rxList := gro.rxList ++ [pkt], rxCount := gro.rxCount + segs }
  if gro.rxCount ≥ GRO_NORMAL_BATCH then groNormalList toStack gro else return gro

/-- The IPv4 header checksum over its 20 bytes (ip_fast_csum, af_inet.c:1506):
    the ones' complement sum folds to 0xffff when the header is intact. -/
def ipv4HeaderChecksumOk (pkt : List UInt8) : Bool :=
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let sum := (List.range 10).foldl (fun acc k => acc + byte (2 * k) * 256 + byte (2 * k + 1)) 0
  let fold := (sum &&& 0xffff) + (sum >>> 16)
  let fold := (fold &&& 0xffff) + (fold >>> 16)
  fold == 0xffff

/-- The network layer's GRO receive on an inner packet (inet_gro_receive,
    af_inet.c:1494-1510; ipv6_gro_receive, ip6_offload.c:243-257): `none`
    when it takes the packet at once (`goto out` with `flush` 1: a protocol
    without a holding `gro_receive`, UDP's flushing without a GRO socket,
    udp_offload.c; an IPv4 header that is not a plain `0x45`, :1500; a
    fragment, :1503; a bad header checksum, :1506; an IPv6 next header that
    is not TCP, the extension-header pull being beyond the domain), else
    `some (off, lengthFlush)`: the transport offset tcp_gro_receive runs at,
    and the layer's own flush bit, the IPv4 total length against the packet
    (:1510) or the IPv6 payload length against it (ip6_offload.c:243),
    OR-ed into the packet's flush at :1532 and :297. -/
def groNetwork (pkt : List UInt8) : Option (Nat × Bool) :=
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let word16 (i : Nat) : Nat := byte i * 256 + byte (i + 1)
  if byte 0 == 0x45 then
    if (word16 6 &&& 0x3fff) != 0 then none                 -- :1503 ip_is_fragment
    else if !ipv4HeaderChecksumOk pkt then none             -- :1506
    else if byte 9 != 6 then none                           -- :1496-1498, TCP is the holding protocol
    else some (20, word16 2 != pkt.length)                  -- :1510
  else if byte 0 / 16 == 6 then
    if byte 6 != 6 then none                                -- :247-252 (an extension header: beyond the domain)
    else some (40, word16 4 != pkt.length - 40)             -- :243
  else none

/-- The TCP header GRO pulls (tcp_gro_pull_header, tcp_offload.c:282-306):
    `some (thlen, len)`, the header length and the payload length
    `skb_gro_len` leaves after the pull, or `none` when the header is short
    (:294-295) or the packet shorter than it (:289-291): tcp4_gro_receive
    then flushes the packet (`goto flush`), taken at once. -/
def groTcpHeader (pkt : List UInt8) (off : Nat) : Option (Nat × Nat) :=
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let thlen := (byte (off + 12) / 16) * 4
  if thlen < 20 || pkt.length < off + thlen then none
  else some (thlen, pkt.length - off - thlen)

/-- The 32-bit word at `i` (big-endian). -/
def groWord32 (pkt : List UInt8) (i : Nat) : Nat :=
  let byte (j : Nat) : Nat := (pkt.getD j 0).toNat
  ((byte i * 256 + byte (i + 1)) * 256 + byte (i + 2)) * 256 + byte (i + 3)

/-- tcp_gro_receive's final flush for a segment GRO did not merge
    (`out_check_final`, tcp_offload.c:374-383, with `mss` 1: the lone
    segment's initial value at :318, or the reset at :362/:368 after a
    refused merge): `len < mss`, so a zero-payload segment flushes (:379),
    and any of URG, PSH, RST, SYN or FIN (:381-383: FIN 1, SYN 2, RST 4,
    PSH 8, URG 32 in the flag byte). -/
def groFinalFlush (flags : Nat) (len : Nat) : Bool :=
  len < 1 || (flags &&& 0x2f) != 0

/-- Whether a held segment and a new one are one flow for GRO: every held
    packet passes gro_list_prepare's tests here (gro.c:362-402: the same
    device, no VLAN, no MAC header on wg0, the raw hash the outer datagram
    gave both), so the flow is decided by the network layer (af_inet.c:
    1524-1528: protocol, source and destination; ip6_offload.c:282-289: the
    first word less the traffic class, source, destination, next header)
    and by tcp_gro_lookup's port word (tcp_offload.c:271). -/
def groSameFlow (held new : List UInt8) (off : Nat) : Bool :=
  let hb (i : Nat) : Nat := (held.getD i 0).toNat
  let nb (i : Nat) : Nat := (new.getD i 0).toNat
  let same (lo hi : Nat) : Bool := (List.range (hi - lo)).all fun k => hb (lo + k) == nb (lo + k)
  let network :=
    if off == 20 then hb 9 == nb 9 && same 12 20
    else (groWord32 held 0 &&& 0xF00FFFFF) == (groWord32 new 0 &&& 0xF00FFFFF) && same 8 40 && hb 6 == nb 6
  network && same off (off + 4)

/-- gro_receive_network_flush on the two headers (include/net/gro.h:496-508,
    447-481): IPv4's inet_gro_flush, every field but length and checksum
    equal (:458: TTL, TOS, DF) and the id rule with the held packet's count 1
    (:467-470: a fixed id under DF, else an id advancing by one); IPv6's
    ipv6_gro_flush (:473-481): the traffic class and the hop limit. -/
def groNetworkFlush (held new : List UInt8) (off : Nat) : Bool :=
  let hb (i : Nat) : Nat := (held.getD i 0).toNat
  let nb (i : Nat) : Nat := (new.getD i 0).toNat
  let w16 (p : List UInt8) (i : Nat) : Nat := (p.getD i 0).toNat * 256 + (p.getD (i + 1) 0).toNat
  if off == 20 then
    let df := w16 new 6 &&& 0x4000
    let df2 := w16 held 6 &&& 0x4000
    if hb 8 != nb 8 || hb 1 != nb 1 || df != df2 then true
    else
      let ipidOffset := (w16 new 4 + 65536 - w16 held 4) % 65536
      let fixedId := df != 0 && ipidOffset == 0
      (ipidOffset ^^^ (if fixedId then 0 else 1)) != 0
  else
    ((groWord32 held 0 ^^^ groWord32 new 0) &&& 0x0FF00000) != 0 || hb 7 != nb 7

/-- tcp_gro_receive's merge test for a new segment against a held one of
    its flow (tcp_offload.c:330-352): `true` when the C refuses the merge
    (`flush`), so the held segment is completed and the new one judged on
    its own; `false` when skb_gro_receive would coalesce them. CWR set
    (:330); the flag word differing beyond CWR, FIN and PSH (:331-332, the
    word at offset 12: data offset, reserved bits, flags and window); the
    acknowledgement number (:333); the options (:334-336); the network
    headers (:338); the held segment's `gso_size`, its payload length
    (gro.c:568), against `len - 1` (:349); the sequence continuity (:351).
    `skb_cmp_decrypted` (:352) is 0 here. -/
def groMergeRefused (held new : List UInt8) (off thlen len : Nat) : Bool :=
  let hb (i : Nat) : Nat := (held.getD i 0).toNat
  let nb (i : Nat) : Nat := (new.getD i 0).toNat
  let flagsNew := groWord32 new (off + 12)
  let flagsHeld := groWord32 held (off + 12)
  let mask : Nat := 0xffffffff ^^^ ((0x80 ||| 0x01 ||| 0x08) <<< 16)   -- ~(CWR | FIN | PSH) on the big-endian word
  let heldThlen := (hb (off + 12) / 16) * 4
  let heldLen := held.length - off - heldThlen
  let options := (List.range (thlen - 20)).any fun k => nb (off + 20 + k) != hb (off + 20 + k)
  (nb (off + 13) &&& 0x80) != 0                                   -- :330 CWR
  || ((flagsNew ^^^ flagsHeld) &&& mask) != 0                      -- :331-332
  || groWord32 new (off + 8) != groWord32 held (off + 8)           -- :333 ack_seq
  || options                                                       -- :334-336
  || groNetworkFlush held new off                                  -- :338
  || (len == 0 || len - 1 >= heldLen)                              -- :349 (len - 1 unsigned)
  || (groWord32 held (off + 4) + heldLen) % 4294967296 != groWord32 new (off + 4)   -- :351

/-- napi_gro_receive (gro.c, dev_gro_receive:480-585): the packet goes to
    `normal` at once, is held, or completes a held segment of its flow
    first. The network layer takes it at once or hands it to
    tcp_gro_receive (`groNetwork`); a short TCP header flushes it
    (`groTcpHeader`). With no held segment of its flow (tcp_gro_lookup,
    :325-327), the final flush decides (`groFinalFlush`: a zero-payload
    segment or a flag). With a held segment of its flow: a refused merge
    (`groMergeRefused`) makes `pp = p` (:385-386, `same_flow` stays 0 since
    skb_gro_receive did not run), so dev_gro_receive completes the held
    segment to the normal list first (:546-550, napi_gro_complete →
    gro_normal_one) and the new segment then goes to `normal` on its own
    final flush (:555) or is held in its place (:558-570); a merge would
    coalesce the two (skb_gro_receive), outside the domain, fail-noisy. A
    second held segment of another flow would be flushed in hash-bucket
    order at completion: outside the domain, fail-noisy, as before. -/
def napiGroReceive [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (toStack : List (List UInt8) → m Unit) (gro : GroState) (pkt : List UInt8) : m GroState := do
  match groNetwork pkt with
  | none => groNormalOne toStack gro pkt 1
  | some (off, lengthFlush) =>
    match groTcpHeader pkt off with
    | none => groNormalOne toStack gro pkt 1   -- tcp4_gro_receive's `goto flush`
    | some (thlen, len) =>
      let flags := (pkt.getD (off + 13) 0).toNat
      match gro.held with
      | [held] =>
        if groSameFlow held pkt off then
          if !groMergeRefused held pkt off thlen len then
            unsupported "GRO coalesces two segments of one flow in one poll (skb_gro_receive)"
          -- `pp = p`: the held segment completed first (gro.c:546-550)
          let gro ← groNormalOne toStack { gro with held := [] } held 1
          if lengthFlush || groFinalFlush flags len then groNormalOne toStack gro pkt 1
          else return { gro with held := [pkt] }
        else
          if lengthFlush || groFinalFlush flags len then groNormalOne toStack gro pkt 1
          else unsupported "GRO holds a second TCP segment in one poll (the hash buckets' flush order)"
      | _ =>
        if lengthFlush || groFinalFlush flags len then groNormalOne toStack gro pkt 1
        else return { gro with held := gro.held ++ [pkt] }

/-- napi_complete_done's flushes (dev.c:6385-6388): the held chains through
    `napi_gro_complete` (`gro_normal_one` with the segment count, 1), then
    the list. -/
def napiGroFlushAll [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (toStack : List (List UInt8) → m Unit) (gro : GroState) : m Unit := do
  let mut g := gro
  for pkt in gro.held do g ← groNormalOne toStack g pkt 1
  g := { g with held := [] }
  _ ← groNormalList toStack g

/-- wg_packet_rx_poll (receive.c:438-491), the peer's NAPI poll, with the
    budget `napi_poll` passes. `toStack` is the environment's cut where
    GRO's `gro_normal_list` hands a flushed list to the stack: at the batch
    of 8 inside the poll, and at `napi_complete_done`. -/
def rxPoll [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → m Unit) : m Nat := do
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
    let go ← andM (branch .rxPollPacket first.isSome) do
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
      if !(← branch .rxPollCounterInvalid !(← counterValidate pkt.keypair pkt.nonce)) then
        let endpoint ← endpointFromSkb pkt.source
        if !(← branch .rxPollEndpointFailed endpoint.isNone) then
          let some e := endpoint | invariant "unreachable"
          -- wg_reset_packet(skb, false) (a cut point)
          for inner in (← consumeDataDone pid pkt e).toList do
            gro ← napiGroReceive toStack gro inner   -- napi_gro_receive(&peer->napi, skb)
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
    napiGroFlushAll toStack gro
  else unsupported "a NAPI poll that used its whole budget (a repoll)"
  return workDone

end Leanux.WG
