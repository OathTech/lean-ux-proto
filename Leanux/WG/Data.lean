import Leanux.WG.Handshake

/-!
# drivers/net/wireguard/send.c — the encrypt and tx workers

`wg_packet_create_data` (Send.lean) puts a packet on the device's encrypt
queue and on its peer's `tx_queue`. The environment (`Leanux/Env.lean`) runs
the encrypt worker, then the tx worker, as the kernel runs them on its one
CPU after the work that queued them.

`encrypt_packet` is mirrored with every value: the padding, the
`message_data` header and ChaCha20-Poly1305 of the padded plaintext under the
keypair's sending key (the NoiseCrypto reference). Cut points:
- `skb_get_hash` (flow dissection; it may draw the flow-hash secret once);
- the skb surgery `skb_cow_head`, `skb_checksum_help` and `skb_cow_data`,
  whose failures are allocation outcomes (`hiddenAlloc`; lax, count 0 on
  this fixture), and `skb_to_sgvec`, which cannot fail for a linear skb;
- `wg_reset_packet` (header resets; its `encapsulating` is the constant true);
- routing and the UDP tunnel transmit below `wg_socket_send_skb_to_peer`, as
  in `sendBufferToPeer` (Handshake.lean);
- `need_resched()`, a scheduler flag: the environment's scheduler decides it
  from the section records (`Env.condResched`), and runs what the kernel
  switched to at the `cond_resched()`.

A ring item is a staged list (Send.lean): keepalives, whose
`PACKET_CB(skb)->mtu` is the device's, and the IP packets `wg_xmit` staged,
whose MTU, bytes and `CHECKSUM_PARTIAL` state come from the environment
(`Env.xmitPacket`). `skb_checksum_help` is a cut whose output the
environment computes (`Env.checksumHelp`, passed in as `checksumHelp`).
-/

namespace Leanux.WG
open Leanux

def MESSAGE_DATA_TYPE : Nat := 4
def MESSAGE_PADDING_MULTIPLE : Nat := 16
/-- `message_data_len(0)`: the header and the authentication tag. -/
def MESSAGE_DATA_LEN_0 : Nat := 16 + 16

/-- `cpu_to_le64`. -/
def le64 (n : Nat) : List UInt8 := (List.range 8).map fun k => UInt8.ofNat (n / 256 ^ k % 256)

/-- The ChaCha20-Poly1305 nonce `chacha20poly1305_encrypt_sg_inplace` builds
    from a 64-bit counter: 4 zero bytes, then the counter little-endian. -/
def counterNonce (counter : Nat) : List UInt8 := List.replicate 4 0 ++ le64 counter

/-- `ALIGN(n, MESSAGE_PADDING_MULTIPLE)`. -/
def alignPadding (n : Nat) : Nat :=
  (n + MESSAGE_PADDING_MULTIPLE - 1) / MESSAGE_PADDING_MULTIPLE * MESSAGE_PADDING_MULTIPLE

/-- calculate_skb_padding (send.c:141-160). -/
def calculateSkbPadding (len mtu : Nat) : M Nat := do
  if ← branch .padNoMtu (mtu == 0) then return alignPadding len - len
  let lastUnit ← do
    if ← branch .padOverMtu (len > mtu) then pure (len % mtu) else pure len
  -- min(mtu, ALIGN(last_unit, MESSAGE_PADDING_MULTIPLE))
  let paddedSize ← do
    if ← branch .padClamped (mtu < alignPadding lastUnit) then pure mtu else pure (alignPadding lastUnit)
  return paddedSize - lastUnit

/-- The pure part of `encrypt_packet`: the `message_data` message for a
    packet's plaintext (already padded) under a keypair's remote index and
    sending key. -/
def dataMessage (remoteIndex nonce : Nat) (key plaintext : List UInt8) : List UInt8 :=
  le32 MESSAGE_DATA_TYPE ++ le32 remoteIndex ++ le64 nonce ++ aeadEncrypt key (counterNonce nonce) plaintext []

/-- encrypt_packet (send.c:162-219) of a packet under its item's keypair:
    the message bytes, or `none` when it fails. `checksumHelp` is
    `skb_checksum_help`'s output (a cut). -/
def encryptPacket (checksumHelp : Packet → M Packet) (keypair : KeypairId) (pkt : DataPacket) :
    M (Option (List UInt8)) := do
  -- skb_get_hash (a cut point)
  skipCut [.flowHashSecret]
  let len := pkt.plaintext.bytes.length
  let paddingLen ← calculateSkbPadding len pkt.plaintext.mtu
  -- plaintext_len = skb->len + padding_len (the AEAD below covers it)
  -- `skb_cow_head(skb, DATA_PACKET_HEAD_ROOM) < 0`
  if ← branch .encCowHeadFailed !(← hiddenAlloc .skbCowHead) then return none
  -- `skb->ip_summed == CHECKSUM_PARTIAL && skb_checksum_help(skb)`: a
  -- keepalive's `ip_summed` is CHECKSUM_NONE
  let mut inner := pkt.plaintext
  if ← branch .encChecksumPartial inner.csum.isSome then
    if ← branch .encChecksumHelpFailed !(← hiddenAlloc .skbChecksumHelp) then return none
    inner ← checksumHelp inner
  -- `num_frags = skb_cow_data(...)`: 1 (the skb is linear), or negative
  let cowOk ← hiddenAlloc .skbCowDataTx
  if ← branch .encCowDataFailed !cowOk then return none
  if ← branch .encTooManyFrags false then return none   -- num_frags > ARRAY_SIZE(sg)
  -- the zero padding, the header (`key_idx = keypair->remote_index`,
  -- `counter = cpu_to_le64(nonce)`) and room for the tag
  let k ← getKeypair keypair
  -- `skb_to_sgvec` < 0: not an allocation (docs/2026-10-05-a-alloc.md 6.4);
  -- a linear skb: `__skb_to_sgvec` returns 1
  if ← branch .encSgvecFailed false then return none
  -- chacha20poly1305_encrypt_sg_inplace over the packet and its padding
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key (inner.bytes ++ List.replicate paddingLen 0))

/-- One iteration of wg_packet_encrypt_worker (send.c:287-309): the ring
    poll (`ptr_ring_consume_bh`; `false` when empty: the loop ends) and the
    item's packets encrypted under `PACKET_CB(first)->keypair` until one
    fails (`DEAD`: the walk breaks, and the tx worker frees the whole list).
    W7 phase 2: the iteration is the unit the environment interleaves
    (`workerIter`). -/
def encryptStep (checksumHelp : Packet → M Packet) : M Bool := do
  -- ptr_ring_consume_bh: the head's slot, discarded by the batch rule
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

/-- One iteration of wg_packet_encrypt_worker's loop (send.c:287-309):
    `encryptStep`, then `cond_resched()` and its decision. `needResched` is
    the environment's scheduler: whether `need_resched()` holds, which
    suspends the worker's activation (W7 phase 2, `workerIter`; the loop and
    its bound are the activation's, `Env.Activation.run`). -/
def encryptIter (checksumHelp : Packet → M Packet) (needResched : M Bool) : M IterResult :=
  workerIter .encryptWorker none (encryptStep checksumHelp)
    (do branch .encWorkerNeedResched (← needResched))

/-- wg_socket_send_skb_to_peer (socket.c:168-187) of an encrypted packet:
    whether it returned 0. `send4`/`send6` are a cut point, as in
    `sendBufferToPeer`: the datagram is recorded in `World.sent`. Delivery
    over loopback runs the NET_RX softirq inside this worker's section. -/
def sendSkbToPeer (pid : PeerId) (bytes : List UInt8) (ds : Nat) : M Bool := do
  let p ← getPeer pid
  let family := (p.endpoint.map (·.family)).getD 0
  -- W9: send4/send6 are mirrored (Socket.lean), with the peer's endpoint cache
  let e := p.endpoint.getD { family := 0, addr := 0, port := 0 }
  let ret ← do
    if ← branch .sendSkbInet (family == AF_INET) then send4 e (some pid) bytes ds true
    else if ← branch .sendSkbInet6 (family == AF_INET6) then send6 e (some pid) bytes ds true
    else pure (-EAFNOSUPPORT)   -- dev_kfree_skb
  let sent := ret == 0
  if ← branch .sendSkbOk sent then
    let p ← getPeer pid
    setPeer pid { p with txBytes := p.txBytes + bytes.length }
  return sent

/-- keep_key_fresh (send.c:124-139). -/
def keepKeyFresh (pid : PeerId) : M Unit := do
  let current := (← getPeer pid).keypairCurrent
  -- `keypair && is_valid && (sending_counter > REKEY_AFTER_MESSAGES ||
  -- (i_am_the_initiator && wg_birthdate_has_expired(birthdate, REKEY_AFTER_TIME)))`
  let send ← andM (branch .freshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    andM (branch .freshValid k.sending.isValid) do
      orM (branch .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES)) do
        andM (branch .freshInitiator k.iAmTheInitiator) do
          branch .freshExpired (← birthdateHasExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← branch .freshSend send then sendQueuedHandshakeInitiation pid false

/-- wg_packet_create_data_done (send.c:242-260) for an encrypted item. -/
def createDataDone (pid : PeerId) (item : List SkbId) : M Unit := do
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let mut dataSent := false
  -- skb_list_walk_safe(first, skb, next)
  for id in item do
    let skb ← getTxSkb id
    _ ← branch .doneSkbIterate true
    let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← sendSkbToPeer pid skb.bytes skb.ds   -- wg_socket_send_skb_to_peer(peer, skb, PACKET_CB(skb)->ds)
    -- `likely(!wg_socket_send_skb_to_peer(...) && !is_keepalive)`
    if ← andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive) then dataSent := true
  _ ← branch .doneSkbIterate false
  if ← branch .doneDataSent dataSent then timersDataSent pid
  keepKeyFresh pid

/-- One iteration of wg_packet_tx_worker (send.c:262-285) for a peer: the
    peek (`false` when the queue is empty or its head UNCRYPTED: the run
    ends with the item peeked) and the item sent, dropping the references
    `wg_packet_send_staged_packets` took. W7 phase 2: the unit the
    environment interleaves (`workerIter`). -/
def txStep (pid : PeerId) : M Bool := do
  -- `(first = wg_prev_queue_peek(&peer->tx_queue)) != NULL` (W7: the queue
  -- as data; the peeked item stays across runs)
  let (first, q) ← (← getPeer pid).txQueue.peek
  setPeer pid { (← getPeer pid) with txQueue := q }
  -- `&& (state = atomic_read_acquire(&PACKET_CB(first)->state)) != PACKET_STATE_UNCRYPTED`:
  -- an UNCRYPTED head ends the run with the item peeked (send.c:269-272)
  let go ← andM (branch .txPacket first.isSome) do
    let some f := first | invariant "unreachable"
    let some h := f.head? | invariant "an empty ring item"
    branch .txNotUncrypted ((← getTxSkb h).state != .uncrypted)
  if !go then return false
  let some item := first | invariant "unreachable"
  let some headId := item.head? | invariant "an empty ring item"
  let head ← getTxSkb headId
  -- wg_prev_queue_drop_peeked
  setPeer pid { (← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked }
  if ← branch .txCrypted (head.state == .crypted) then createDataDone pid item
  -- else kfree_skb_list(first); either way the skbs leave the store (sent
  -- ones are the stack's, review 4.2)
  for id in item do freeTxSkb id
  keypairPut (some head.keypair) false
  peerPut (some pid)
  return true

/-- One iteration of wg_packet_tx_worker's loop (send.c:262-285) for a
    peer: `txStep`, then `cond_resched()` and its decision. `needResched` as
    for `encryptIter`. -/
def txIter (pid : PeerId) (needResched : M Bool) : M IterResult :=
  workerIter .txWorker (some pid) (txStep pid)
    (do branch .txNeedResched (← needResched))

private def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

-- Keepalive messages for a known key (bytes 0..31) and remote index
-- 0x04030201, at three counters; harness/test_d1_keepalive.py computes the
-- same with harness/noise.py's independent aead_encrypt.
#guard hexOf (dataMessage 0x04030201 0 ((List.range 32).map UInt8.ofNat) []) ==
  "0400000001020304000000000000000010324f800a160bd9a1794255be7ec29d"
#guard hexOf (dataMessage 0x04030201 5 ((List.range 32).map UInt8.ofNat) []) ==
  "040000000102030405000000000000003e2fdcfe114117a96d0d40c0777d9d17"
#guard hexOf (dataMessage 0x04030201 (2 ^ 40 + 3) ((List.range 32).map UInt8.ofNat) []) ==
  "0400000001020304030000000001000082b9adec90da2dfe162521e79d637c95"

end Leanux.WG
