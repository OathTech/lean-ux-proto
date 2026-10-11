"""WireGuard mutants (stage A report, section 2; stages B1, B2, C, D1, D2, E arm 4,
E-B under load, D3 and workstream L), and the allocation-outcome mutants of A
(docs/2026-10-05-a-alloc.md, section 7).

Each mutant is applied to a clean committed tree, verified as applied, checked
on the wireguard suite, then reverted. Run from the repository root:

    scripts/in-bundle python3 scripts/wg-mutants.py [NAME ...]

Every mutant must be rejected: its run must end in a mirror-side verdict
(`MISMATCH_OUTCOMES`). A run that fails only on the infrastructure (an
environment failure, a timeout, a busy QEMU slot, an aborted run, no report,
or any other outcome) is "no_verdict", never a rejection, and the script then
exits 1. D2 and D3 entries without patterns are reported as pending; the
entries of `EQUIVALENT` are not run and are reported as equivalent. W5 also
aborts on a mirror invariant; run `--trace wg_trie_v6` by hand to see A2
alone reject it.
"""
import glob
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from evaluator.napi_orders import napi_orders  # noqa: E402
MUTANTS = [
  ('W1-unmasked-read-node', 'A1: dump shows unmasked prefixes', 'Leanux/WG/AllowedIps.lean',
   "  let masked := if hasCidr then n.bits / 2 ^ (n.bitlen - n.cidr) * 2 ^ (n.bitlen - n.cidr) else 0\n",
   "  let masked := if hasCidr then n.bits else 0\n"),
  ('W2-collapsed-endpoint-eq', 'behavior-preserving: always rewrite the endpoint', 'Leanux/WG/Netlink.lean',
   "  if ← branch .setEndpointEq (← endpointEq e (← getPeer pid).endpoint) then return\n",
   "  _ ← endpointEq e (← getPeer pid).endpoint\n  if ← branch .setEndpointEq false then return\n"),
  ('W3-no-put-before-remove', 'behavior-preserving: the displaced peer is never released', 'Leanux/WG/Netlink.lean',
   "        if ← branch .setDevOldPeer peer.isSome then\n          peerPut peer\n          peerRemove peer\n",
   "        if ← branch .setDevOldPeer peer.isSome then\n          peerRemove peer\n"),
  ('W4-fwmark-after-port', 'behavior-preserving: fwmark block moved after the listen-port block', 'Leanux/WG/Netlink.lean',
   None, None),
  ('W5-trie-bit-off-by-one', 'dump-invisible: trie built on the wrong bit', 'Leanux/WG/AllowedIps.lean',
   "  return key / 2 ^ (node.bitlen - 1 - node.cidr) % 2\n",
   "  return key / 2 ^ (node.bitlen - node.cidr) % 2\n"),
  # Stage B1 (transmit and routing)
  ('B1-M1-first-match', 'routing: find_node stops at the first matching peer', 'Leanux/WG/AllowedIps.lean',
   "    if ← branch .findNodeHasPeer n.peer.isSome then found := some id\n",
   "    if ← branch .findNodeHasPeer n.peer.isSome then\n      if found.isNone then found := some id\n"),
  ('B1-M2-no-keypair-get', 'behavior-preserving: wg_noise_keypair_get omitted', 'Leanux/WG/Send.lean',
   '  let keypair ← keypairGet p.keypairCurrent\n',
   '  let keypair : Option KeypairId := p.keypairCurrent\n'),
  ('B1-M3-xmit-keeps-reference', 'behavior-preserving: wg_xmit never drops its peer reference', 'Leanux/WG/Device.lean',
   "  sendStagedPackets pid\n  peerPut peer\n  return 0   -- NETDEV_TX_OK",
   "  sendStagedPackets pid\n  return 0   -- NETDEV_TX_OK"),
  ('B1-M4-low-order-emits', 'behavior: the initiation ignores a null ephemeral-static DH (now the mirrored worker)',
   'Leanux/WG/Handshake.lean',
   "  if ← branch .initEsFailed es.isNone then return none\n",
   "  if ← branch .initEsFailed false then return none\n"),
  ('B1-M5-dead-before-expired', 'behavior-preserving: is_dead tested before the expiry', 'Leanux/WG/Send.lean',
   "  if ← branch .queuedNotExpired !(← birthdateHasExpired p.lastSentHandshake REKEY_TIMEOUT) then return\n  if ← branch .queuedDead p.isDead then return\n",
   "  if ← branch .queuedDead p.isDead then return\n  if ← branch .queuedNotExpired !(← birthdateHasExpired p.lastSentHandshake REKEY_TIMEOUT) then return\n"),
  # Stage B2 (receive)
  ('B2-M1-no-header-pull', 'parsing: a message shorter than its header passes the pull', 'Leanux/WG/Receive.lean',
   "  if ← orM (branch .prepPullFailed (msg.length < 4)) (branch .prepTrimFailed false) then return false\n",
   "  if ← orM (branch .prepPullFailed false) (branch .prepTrimFailed false) then return false\n"),
  ('B2-M2-cpu-never-wraps', 'state: last_cpu never wraps', 'Leanux/WG/Receive.lean',
   "    if ← branch .cpumaskWrap (next ≥ 1) then pure (0 : Int) else pure next\n",
   "    if ← branch .cpumaskWrap false then pure (0 : Int) else pure next\n"),
  ('B2-M3-length-before-type', 'order: validate_header_len tests the length first', 'Leanux/WG/Receive.lean',
   "  if ← andM (branch .hdrInit (t == MESSAGE_HANDSHAKE_INITIATION))\n      (branch .hdrInitLen (len == 148)) then\n",
   "  if ← andM (branch .hdrInitLen (len == 148))\n      (branch .hdrInit (t == MESSAGE_HANDSHAKE_INITIATION)) then\n"),
  ('B2-M4-response-off-by-one', 'parsing: a 91-byte response is accepted', 'Leanux/WG/Receive.lean',
   "      (branch .hdrRespLen (len == 92)) then\n",
   "      (branch .hdrRespLen (len == 92 || len == 91)) then\n"),
  # Stage C (Noise responder)
  ('C-M1-replay-inclusive', 'state: an equal timestamp is not a replay', 'Leanux/WG/Handshake.lean',
   "  let replay := memcmp t p.latestTimestamp != .gt\n",
   "  let replay := memcmp t p.latestTimestamp == .lt\n"),
  ('C-M2-receiver-is-sender', 'data: the response names its own index as the receiver', 'Leanux/WG/Handshake.lean',
   "  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)\n",
   "  return some (le32 2 ++ le32 index ++ le32 index ++ e ++ encNothing ++ List.replicate 32 0)\n"),
  # C-M3, the known survivor before D3: rejected once the mirror consumes
  # the kind-303 arm records (ARM_RECORDS on): the receive path's
  # traversal re-arm (persistent keepalive 25 s) leaves its record unconsumed
  # (docs/2026-10-05-d3-timers.md, sections 3.3 and 8).
  ('C-M3-no-rx-traversal', 'arm record: no traversal timer after receiving (its kind-303 record is unconsumed)',
   'Leanux/WG/Receive.lean',
   "  timersAnyAuthenticatedPacketReceived pid\n  timersTraversal pid\n  peerPut peer\n",
   "  timersAnyAuthenticatedPacketReceived pid\n  peerPut peer\n"),
  ('C-M4-keypair-kept-indexed', 'behavior-preserving: the old next keypair stays in the index', 'Leanux/WG/Keypair.lean',
   '    keypairPut next true\n',
   '    keypairPut next false\n'),
  ('C-M5-endpoint-family-swapped', 'data: the learned endpoint tests IPv6 first', 'Leanux/WG/Handshake.lean',
   "  if ← branch .epFromSkbInet (src.family == 4) then\n",
   "  if ← branch .epFromSkbInet (src.family == 6) then\n"),
  # Hidden inputs: the send worker and the response with every value
  ('H-M1-tai64n-unrounded', 'data: the timestamp keeps its nanoseconds', 'Leanux/WG/Handshake.lean',
   "  be ((0x400000000000000a + sec) % 2 ^ 64) 8 ++ be (nsec - nsec % 2 ^ 24) 4\n",
   "  be ((0x400000000000000a + sec) % 2 ^ 64) 8 ++ be nsec 4\n"),
  ('H-M2-mac1-range', 'data: MAC1 also covers the MAC1 field', 'Leanux/WG/Handshake.lean',
   "  let mac1 := blake2s 16 p.cookieMac1Key body   -- compute_mac1\n",
   "  let mac1 := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 16))   -- compute_mac1\n"),
  ('H-M3-index-big-endian', 'data: the sender index is big-endian', 'Leanux/WG/Handshake.lean',
   "  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)\n",
   "  return some (le32 1 ++ (le32 index).reverse ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)\n"),
  ('H-M4-psk-not-hashed', 'data: the response hash skips the PSK step', 'Leanux/WG/Handshake.lean',
   '  let (ck, tempHash, key) := (outs.head!, outs.getD 1 [], outs.getD 2 [])\n  let h := noiseHash (h ++ tempHash)\n',
   '  let (ck, tempHash, key) := (outs.head!, outs.getD 1 [], outs.getD 2 [])\n  let h := h\n'),
  ('H-M5-no-initiation-traversal', 'behavior-preserving: no traversal timer before sending an initiation',
   'Leanux/WG/Handshake.lean',
   "    timersTraversal pid\n    timersAnyAuthenticatedPacketSent pid\n    let now ← hiddenClock .initLastSentAgain\n",
   "    timersAnyAuthenticatedPacketSent pid\n    let now ← hiddenClock .initLastSentAgain\n"),
  ('H-M6-clock-before-ephemeral', 'negative control: the clock is read before the ephemeral key',
   'Leanux/WG/Handshake.lean',
   "  let secret := clamp (← hidden .initEphemeral)\n",
   "  let _ ← hidden .tai64nNow\n  let secret := clamp (← hidden .initEphemeral)\n"),
  # Choice stream, step 1: generic capture of random draws and clock reads
  ('H-M7-flood-threshold', 'decision-preserving: the flood window is 200 ms (5 initiations a second)',
   'Leanux/WG/Handshake.lean',
   "  let floodLhs := p.lastInitiationConsumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND\n",
   "  let floodLhs := p.lastInitiationConsumption + NSEC_PER_SEC / 5\n"),
  ('H-M8-response-unclamped', 'data: the response ephemeral is not clamped', 'Leanux/WG/Handshake.lean',
   "  let secret := clamp (← hidden .respEphemeral)   -- curve25519_generate_secret\n",
   "  let secret ← hidden .respEphemeral   -- curve25519_generate_secret\n"),
  ('H-M9-last-sent-not-reset-back', 'state: the reset last_sent_handshake is now, not REKEY_TIMEOUT + 1 s back',
   'Leanux/WG/Peer.lean',
   "  setPeer pid { (← getPeer pid) with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat) * NSEC_PER_SEC }\n",
   "  setPeer pid { (← getPeer pid) with lastSentHandshake := now }\n"),
  ('H-M10-undeclared-cut', 'negative control: the ICMP rate limiter is not a declared cut consumer',
   'Leanux/Kernel/Defs.lean',
   '  | .icmpCredit => ⟨22, "icmp_global_consume", "random", "net/ipv4/icmp.c", 268, 1, .cut⟩\n',
   '  | .icmpCredit => ⟨22, "icmp_global_consume", "random", "net/ipv4/icmp.c", 269, 1, .cut⟩\n'),
  # H-M11 (no fixture cut in wg_xmit) retired [USER 2026-10-05]: since D2's
  # IP_PMTUDISC_DO the xmit path draws no IP ident, so the cut consumes nothing
  # and the control is equivalent.
  # Choice stream, step 2: paths only steering reaches
  ('S2-M1-lookup-ignores-type', 'state: the index lookup ignores its type mask', 'Leanux/WG/Peer.lean',
   "      if ← branch .idxTypeMatch (kinds.contains e.kind) then entry := some e\n",
   "      if ← branch .idxTypeMatch true then entry := some e\n"),
  ('S2-M2-insert-keeps-collision', 'state: the insert does not redraw after an unlocked collision',
   'Leanux/WG/Peer.lean',
   "    if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then continue\n",
   "    let _ ← bucketHas .idxInsWalk1 .idxInsCollide1 index\n"),
]

# Stage D1 (wg0 initiates the handshake, the session, the keepalive data
# path, the worker scheduler). Entries: (name, description, file, old, new),
# appended to MUTANTS below.
D1_MUTANTS = [
  ('D1-M1-keys-responder-order', 'data: begin_session derives the initiator\'s keys in responder order',
   'Leanux/WG/Handshake.lean',
   "  setKeypair kp (if initiator then { k with sending := first, receiving := second }\n",
   "  setKeypair kp (if initiator then { k with sending := second, receiving := first }\n"),
  ('D1-M2-key-idx-internal', 'data: encrypt_packet writes the keypair\'s internal id as key_idx (send.c:207)',
   'Leanux/WG/Data.lean',
   "  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key (inner.bytes ++ List.replicate paddingLen 0))\n",
   "  return some (dataMessage k.internalId pkt.nonce k.sending.key (inner.bytes ++ List.replicate paddingLen 0))\n"),
  ('D1-M3-remote-index-not-updated', 'state: consume_response keeps the old remote_index (noise.c:797)',
   'Leanux/WG/Handshake.lean',
   "                                     remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE }\n",
   "                                     handshakeState := HANDSHAKE_CONSUMED_RESPONSE }\n"),
  ('D1-M4-no-next-demotion', 'state: add_new_keypair\'s initiator arm ignores a pending next keypair (noise.c:211-222)',
   'Leanux/WG/Keypair.lean',
   "    if ← branch .addKeypairHasNext next.isSome then\n",
   "    if ← branch .addKeypairHasNext false then\n"),
  ('D1-M5-psk-not-mixed', 'data: consume_response mixes a zero PSK (noise.c:778)', 'Leanux/WG/Handshake.lean',
   "  -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)\n  let outs ← kdf true true ck p.presharedKey\n  let (ck, tempHash, key) := (outs.getD 0 [], outs.getD 1 [], outs.getD 2 [])\n  let h := noiseHash (h ++ tempHash)\n  -- {}\n  let dec",
   "  -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)\n  let outs ← kdf true true ck (List.replicate 32 0)\n  let (ck, tempHash, key) := (outs.getD 0 [], outs.getD 1 [], outs.getD 2 [])\n  let h := noiseHash (h ++ tempHash)\n  -- {}\n  let dec"),
  ('D1-M6-nothing-unchecked', 'control: encrypted_nothing\'s decryption is not checked (noise.c:781-783)',
   'Leanux/WG/Handshake.lean',
   "  if ← branch .crespDecryptFailed dec.isNone then return ← fail\n  let some (_, h) := dec | invariant \"unreachable\"\n",
   "  if ← branch .crespDecryptFailed false then return ← fail\n  let h := (dec.map (·.2)).getD h\n"),
  ('D1-M7-ee-with-static', 'data: the ee DH uses wg0\'s static key instead of its ephemeral (noise.c:770)',
   'Leanux/WG/Handshake.lean',
   "  let ee ← mixDh false ck p.ephemeralPrivate eph\n",
   "  let ee ← mixDh false ck identity.staticPrivate eph\n"),
  ('D1-M8-initiator-flag-inverted', 'state: i_am_the_initiator inverted (noise.c:830)', 'Leanux/WG/Handshake.lean',
   "  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }\n",
   "  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := !initiator, remoteIndex := p.remoteIndex }\n"),
  ('D1-M9-endpoint-not-learned', 'data: the response arm does not learn the endpoint (receive.c:172)',
   'Leanux/WG/Receive.lean',
   "      let some pid := peer | invariant \"unreachable\"\n      setPeerEndpointFromSkb pid src\n      if ← branch .hsRespSessionBegun",
   "      let some pid := peer | invariant \"unreachable\"\n      if ← branch .hsRespSessionBegun"),
  ('D1-M10-nonce-from-one', 'data: the nonce is the counter after the increment (send.c:380)', 'Leanux/WG/Send.lean',
   "    let nonce := k.sendingCounter   -- atomic64_inc_return(&sending_counter) - 1\n",
   "    let nonce := k.sendingCounter + 1\n"),
  ('D1-M11-keepalive-padded', 'data: a zero-length payload is padded to 16 bytes (send.c:141-160)',
   'Leanux/WG/Data.lean',
   "  let paddingLen ← calculateSkbPadding len pkt.plaintext.mtu\n",
   "  let paddingLen ← (do let _ ← calculateSkbPadding len pkt.plaintext.mtu; pure 16)\n"),
  ('D1-M12-no-walltime', 'data: walltime_last_handshake is consumed but not stored (timers.c:197)',
   'Leanux/WG/Handshake.lean',
   "  let now ← hidden site\n  setPeer pid { (← getPeer pid) with walltimeLastHandshake := now }\n",
   "  let _ ← hidden site\n"),
  ('D1-M13-no-keep-key-fresh', 'control, behavior-preserving: the tx worker skips keep_key_fresh (send.c:259)',
   'Leanux/WG/Data.lean',
   "  if ← branch .doneDataSent dataSent then timersDataSent pid\n  keepKeyFresh pid\n",
   "  if ← branch .doneDataSent dataSent then timersDataSent pid\n"),
  ('D1-M14-no-keypair-put-tx', 'control, behavior-preserving: the tx worker keeps its keypair reference (send.c:280)',
   'Leanux/WG/Data.lean',
   "    keypairPut (some head.keypair) false\n    peerPut (some pid)\n    _ ← branch .txNeedResched (← needResched)\n",
   "    peerPut (some pid)\n    _ ← branch .txNeedResched (← needResched)\n"),
  ('D1-M15-ignore-resched', 'scheduling: cond_resched never switches, ignoring the resched records (kind 302); the corpus has receive-worker reschedules, though whether one occurs is timing-dependent',
   'Leanux/Env.lean',
   "    if (← peekHiddenSite) != some site.info.id then return false\n",
   "    if true then return false\n"),
]

# Stage D2 (the data plane; design docs/2026-10-04-d2-data-plane.md, section
# 7). A DRAFT list, written by stream C before the mirror code exists: an
# entry whose patterns are None is pending, reported as such and not run,
# until integration fills it against the merged mirror. Entries with patterns
# match the code at the time of writing; streams A and B may rewrite those
# lines, in which case integration refreshes them (the runner fails on a
# pattern that is not present exactly once). The files named for pending
# entries are where the code is expected (stream B may use RxData.lean).
D2_MUTANTS = [
  ('D2-M1-window-off-by-one', 'state: counter_validate\'s window test is off by one (receive.c:308-309: '
   'COUNTER_WINDOW_SIZE + their_counter < counter); the window boundary pair', 'Leanux/WG/RxData.lean',
   "  if ← branch .ctrTooOld (COUNTER_WINDOW_SIZE + theirs < c.counter) then return false\n",
   "  if ← branch .ctrTooOld (COUNTER_WINDOW_SIZE + theirs ≤ c.counter) then return false\n"),
  ('D2-M2-bitmap-index-unmasked', 'state: the backtrack word index is not masked with '
   '(COUNTER_BITS_TOTAL / BITS_PER_LONG) - 1 (receive.c:324)', 'Leanux/WG/RxData.lean',
   "  let index := index % words\n", "  let index := index\n"),
  ('D2-M3-their-counter-not-incremented', 'state: counter_validate drops ++their_counter (receive.c:306)',
   'Leanux/WG/RxData.lean', "  let theirs := theirs + 1   -- ++their_counter\n", ""),
  ('D2-M4-padding-ignores-mtu', 'data: calculate_skb_padding pads to ALIGN(len, 16) without the MTU clamp '
   '(send.c:157); d2_padding_mtu pads to 1424', 'Leanux/WG/Data.lean',
   "    if ← branch .padClamped (mtu < alignPadding lastUnit) then pure mtu else pure (alignPadding lastUnit)\n",
   "    if ← branch .padClamped (mtu < alignPadding lastUnit) then pure (alignPadding lastUnit) else pure (alignPadding lastUnit)\n"),
  ('D2-M5-checksum-not-completed', 'data: encrypt_packet skips skb_checksum_help\'s result (send.c:187-189); '
   'the inner UDP checksum stays the pseudo-header sum', 'Leanux/WG/Data.lean',
   "    inner ← checksumHelp inner\n", "    inner := inner\n"),
  ('D2-M6-lookup-src-uses-destination', 'routing: wg_allowedips_lookup_src walks the inner destination',
   'Leanux/WG/RxData.lean',
   "  if ← branch .lookupSrcV4 (protocol == 4) then return ← lookup t.root4 32 (beAt bytes 12 4)\n"
   "  if ← branch .lookupSrcV6 (protocol == 6) then return ← lookup t.root6 128 (beAt bytes 8 16)\n",
   "  if ← branch .lookupSrcV4 (protocol == 4) then return ← lookup t.root4 32 (beAt bytes 16 4)\n"
   "  if ← branch .lookupSrcV6 (protocol == 6) then return ← lookup t.root6 128 (beAt bytes 24 16)\n"),
  ('D2-M7-received-with-keypair-no-promotion', 'state: wg_noise_received_with_keypair does not promote next '
   'to current (noise.c); the respond-then-data traces', 'Leanux/WG/Keypair.lean',
   "  if ← branch .receivedNotNew ((← getPeer pid).keypairNext != some received) then return false\n",
   "  if ← branch .receivedNotNew true then return false\n"),
  ('D2-M8-rx-bytes-trimmed', 'data: update_rx_stats counts the trimmed length, not len_before_trim '
   '(receive.c:409); rx_bytes in the dump', 'Leanux/WG/RxData.lean',
   "  updateRxStats pid (lenBeforeTrim + MESSAGE_DATA_LEN_0)", "  updateRxStats pid (ipLen + MESSAGE_DATA_LEN_0)"),
  ('D2-M9-keepalive-not-detected', 'control: consume_data_done does not test skb->len == 0 (receive.c:362)',
   'Leanux/WG/RxData.lean',
   "  if ← branch .doneRxKeepalive (len == 0) then\n", "  if ← branch .doneRxKeepalive false then\n"),
  ('D2-M10-dead-as-crypted', 'control: the decrypt worker enqueues a failed decryption as CRYPTED '
   '(receive.c:499-501); the tampered-tag traces', 'Leanux/WG/RxData.lean',
   "      else enqueuePerPeerRx irqExit pkt .dead\n", "      else enqueuePerPeerRx irqExit pkt .crypted\n"),
  ('D2-M11-nonce-per-list', 'data: the sending counter is not advanced per packet (send.c:378-381); '
   'd2_staged_flush_4 repeats a nonce', 'Leanux/WG/Send.lean',
   "    setKeypair id { k with sendingCounter := k.sendingCounter + 1 }\n", "    setKeypair id k\n"),
  ('D2-M12-poll-outside-worker', 'scheduling control: the NAPI poll runs after the decrypt worker\'s section '
   'instead of inside it (design section 5); rejected only when a run shows order (b) (timing-dependent)',
   'Leanux/Env.lean',
   "  runWorker .decryptWorker (WG.decryptWorker napiSoftirq napiIrqExit (condResched SWITCH_DEPTH .decryptWorker))\n"
   "  if (← getDev).peers.toList.any (·.2.napiScheduled) then\n"
   "    invariant \"a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)\"\n",
   "  runWorker .decryptWorker (WG.decryptWorker (pure ()) (pure ()) (condResched SWITCH_DEPTH .decryptWorker))\n"
   "  napiSoftirq\n"),
]
# Stage E arm 4 (cookie-reply consumption and MAC2; docs/2026-10-05-e-dos.md
# sections 6.A and 10). E-M5 (freshness 120 vs 115 s) needs D3's time
# advance and is not claimed.
E_MUTANTS = [
  ('E-M1-cookie-stored-on-failed-decrypt', 'state: wg_cookie_message_consume stores the cookie without '
   'verifying the tag (cookie.c:216-222); e_cookie_bad_mac1_aad', 'Leanux/WG/Receive.lean',
   "  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent\n",
   "  let cookie := some ((xchachaEncrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 16)\n"
   "    p.lastMac1Sent).take 16)\n"),
  ('E-M2-mac2-ignores-cookie-valid', 'data: wg_cookie_add_mac_to_packet never uses the stored cookie '
   '(is_valid ignored, cookie.c:170); e_cookie_then_reinitiate\'s MAC2', 'Leanux/WG/Handshake.lean',
   "  if ← andM (branch .addMacCookieValid p.cookieIsValid)\n",
   "  if ← andM (branch .addMacCookieValid false)\n"),
  ('E-M3-mac2-keyed-by-mac1-key', 'data: compute_mac2 keyed by the MAC1 key, not the cookie (cookie.c:173-174)',
   'Leanux/WG/Handshake.lean',
   "    return body ++ mac1 ++ blake2s 16 p.cookie (body ++ mac1)\n",
   "    return body ++ mac1 ++ blake2s 16 p.cookieMac1Key (body ++ mac1)\n"),
  ('E-M4-have-sent-mac1-not-cleared', 'state: a consumed cookie leaves have_sent_mac1 set (cookie.c:227); '
   'e_cookie_double_reply decrypts the second reply where Linux goes to out (cookie.c:212)',
   'Leanux/WG/Receive.lean',
   "    setPeer pid { (← getPeer pid) with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true,\n"
   "                                       haveSentMac1 := false }\n",
   "    setPeer pid { (← getPeer pid) with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true }\n"),
]

# Stage D3 (timers; docs/2026-10-05-d3-timers.md, section 8). The patterns
# match stream M's code (task/d3-m at 2438924: the callbacks in
# Leanux/WG/Timers.lean, the clear work in Keypair.lean, the firing in
# Env.lean) and the interface commit's arm sites. Each is rejected only on
# the D3 traces named.
D3_MUTANTS = [
  ('D3-M1-attempts-not-incremented', 'state: the retransmit callback does not increment '
   'timer_handshake_attempts (timers.c:63); d3_retransmit_gives_up never gives up (tx_dropped, the give-up '
   'arm\'s zero-key arm record, a 21st initiation)', 'Leanux/WG/Timers.lean',
   "    setPeer pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }\n",
   "    setPeer pid p\n"),
  ('D3-M2-need-another-ignored', 'arm record: the keepalive callback ignores need_another_keepalive '
   '(timers.c:84-88); the re-arm never fires, so only its kind-303 record, left unconsumed, shows it '
   '(d3_keepalive_rearm_deleted); mod_peer_timer\'s two decisions are kept', 'Leanux/WG/Timers.lean',
   "    discard <| modPeerTimer pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS\n",
   "    discard <| modPeerTimerGuard pid\n"),
  ('D3-M3-firing-keeps-timer', 'state: a fired timer stays pending (expire_timers detaches it before the '
   'callback, timer.c:1828-1829); the next data_received or data_sent pending test differs, consuming an arm '
   'record or not (d3_new_handshake\'s transmission after the firing)', 'Leanux/Env.lean',
   "  | [pid] =>\n    delTimer pid t\n    runTimerSection w (WG.timerCallback pid t)\n",
   "  | [pid] =>\n    runTimerSection w (WG.timerCallback pid t)\n"),
  ('D3-M4-clear-keeps-handshake', 'state: the clear worker clears the keypairs but not the handshake '
   '(timers.c:129); the index removal\'s control flow (d3_zero_key, d3_zero_key_after_new_handshake)',
   'Leanux/WG/Keypair.lean',
   "def queuedExpiredZeroKeyMaterial (pid : PeerId) : M Unit := do\n  handshakeClear pid\n  keypairsClear pid\n",
   "def queuedExpiredZeroKeyMaterial (pid : PeerId) : M Unit := do\n  keypairsClear pid\n"),
  ('D3-M5-send-fresh-at-reject', 'behavior: send-side keep_key_fresh at REJECT_AFTER_TIME instead of '
   'REKEY_AFTER_TIME (send.c:134); no initiation after 121 s (d3_send_keep_key_fresh)', 'Leanux/WG/Data.lean',
   "          branch .freshExpired (← birthdateHasExpired k.sending.birthdate REKEY_AFTER_TIME)\n",
   "          branch .freshExpired (← birthdateHasExpired k.sending.birthdate REJECT_AFTER_TIME)\n"),
  ('D3-M6-no-lastminute-flag', 'hidden: receive-side keep_key_fresh does not set sent_lastminute_handshake '
   '(receive.c:236); the second data message reads the clock again (d3_rx_keep_key_fresh)',
   'Leanux/WG/RxData.lean',
   "    setPeer pid { (← getPeer pid) with sentLastminuteHandshake := true }\n    sendQueuedHandshakeInitiation pid false\n",
   "    sendQueuedHandshakeInitiation pid false\n"),
  ('D3-M7-send-ignores-reject-after-time', 'behavior: send_staged_packets reads the birthdate but ignores '
   'REJECT_AFTER_TIME (send.c:365); a data message instead of an initiation (d3_send_expired_key)',
   'Leanux/WG/Send.lean',
   "  if ← branch .stagedBirthdateExpired (← birthdateHasExpired k.sending.birthdate REJECT_AFTER_TIME) then\n",
   "  if ← branch .stagedBirthdateExpired (← (do let _ ← birthdateHasExpired k.sending.birthdate REJECT_AFTER_TIME; pure false)) then\n"),
  ('D3-M8-new-handshake-delay', 'arm record: timer_new_handshake armed at KEEPALIVE_TIMEOUT instead of '
   'KEEPALIVE_TIMEOUT + REKEY_TIMEOUT (timers.c:149); only the kind-303 expires check sees it (every trace '
   'that sends data after a session)', 'Leanux/WG/Handshake.lean',
   "      armTimer pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter)\n",
   "      armTimer pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + jitter)\n"),
]
# Stage E-B (under-load + cookie-reply creation; docs/2026-10-05-e-dos.md §6.B,
# §10). Checked on the e_underload_* traces (the sixth field 'e_underload').
E_UNDERLOAD_MUTANTS = [
  ('E-M6-under-load-threshold-gt', 'data: under_load uses `>` not `>=` the threshold (receive.c:112). NOT '
   'CLAIMED: the threshold is not a declared comparison and the leading packet runs with queue_len well above '
   '512, so `>` vs `>=` is not observable (like E-M5).',
   'Leanux/WG/Receive.lean',
   "  if ← branch .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8) then\n",
   "  if ← branch .hsUnderLoad (queueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 8) then\n", 'e_underload_flood'),
  ('E-M7-make-cookie-ignores-source-port', 'data: make_cookie hashes only the source IP, not the port '
   '(cookie.c:113); the cookie, hence the reply bytes, differ (e_underload_cookie)', 'Leanux/WG/Receive.lean',
   "  return blake2s 16 secret (addr ++ netBytes src.sport 2)\n",
   "  return blake2s 16 secret addr\n", 'e_underload'),
  ('E-M8-queue-under-load-ignored', 'behavior: the leading flood packet is treated as not under load despite '
   'queue_len >= 512 (receive.c:112-115); it takes the no-cookie proceed arm instead of sending a cookie — no '
   'reply where Linux sent one (e_underload_cookie)', 'Leanux/WG/Receive.lean',
   "    modify fun w => { w with lastUnderLoad := some now }\n    underLoad := true\n",
   "    modify fun w => { w with lastUnderLoad := some now }\n    underLoad := false\n", 'e_underload'),
  ('E-M9-mac2-compare-inverted', 'control: wg_cookie_validate_packet treats a non-matching MAC2 as valid '
   '(cookie.c:143); a no-cookie initiation then takes the ratelimiter/consume arm instead of a cookie reply, '
   'so the reply records disagree (e_underload_cookie)', 'Leanux/WG/Receive.lean',
   "  if ← branch .macCookieInvalid (computed2 != givenMac2) then return .noCookie\n",
   "  if ← branch .macCookieInvalid (computed2 == givenMac2) then return .noCookie\n", 'e_underload'),
  ('E-M10-ratelimiter-allow-inverted', 'control: wg_ratelimiter_allow denies a packet with tokens (the bucket '
   'compare inverted, ratelimiter.c:126); the hit packet is dropped before consume_initiation, so its flood_now '
   'read is missing (e_underload_ratelimit)', 'Leanux/WG/Receive.lean',
   "    let ret ← branchCmp .rlAllow (newTokens ≥ PACKET_COST) newTokens PACKET_COST\n",
   "    let ret ← branchCmp .rlAllow (newTokens < PACKET_COST) newTokens PACKET_COST\n", 'e_underload_ratelimit'),
  ('E-M11-ratelimiter-insert-tokens', 'data: a new ratelimiter entry starts at TOKEN_MAX, not TOKEN_MAX - '
   'PACKET_COST (ratelimiter.c:147); the next hit from the same IP reports a different token count '
   '(e_underload_ratelimit, the rlAllow operands)', 'Leanux/WG/Receive.lean',
   "      table := (ip, TOKEN_MAX - PACKET_COST, now) :: k.ratelimiter.table } }\n",
   "      table := (ip, TOKEN_MAX, now) :: k.ratelimiter.table } }\n", 'e_underload_ratelimit'),
]
# Workstream L (docs/2026-10-05-l-lifecycle.md, section 8): checked on the
# l_* traces of the wireguard suite (the sixth field), each naming the trace
# that rejects it. L-M10 is a data-only correction nothing observes: it is
# run and expected to pass (not claimed as evidence).
L_MUTANTS = [
  ('L-M1-stop-keeps-staged', 'behavior: wg_stop does not purge the staged packets (device.c:123); '
   'tx_dropped differs (l_down_purges_staged)', 'Leanux/WG/Device.lean',
   "    purgeStagedPackets pid\n    timersStop pid\n", "    timersStop pid\n", 'l_'),
  ('L-M2-stop-keeps-last-sent', 'behavior and hidden: wg_stop does not reset last_sent_handshake (device.c:127); '
   'the reset_last_sent record is left over (l_down_up_keepalive)', 'Leanux/WG/Device.lean',
   "    keypairsClear pid\n    resetLastSentHandshake pid\n  _ ← branch .stopPeersIter false\n",
   "    keypairsClear pid\n  _ ← branch .stopPeersIter false\n", 'l_'),
  ('L-M3-reinit-clears-port', 'data: wg_socket_reinit with a NULL new4 sets incoming_port 0 (socket.c:431-432); '
   'the dump after a down differs, and the reopen draws a port', 'Leanux/WG/Socket.lean',
   "  if ← branch .reinitHasNew4 new4.isSome then\n    let some port := new4 | invariant \"unreachable\"\n"
   "    modifyDev fun d => { d with incomingPort := port }   -- ntohs(inet_sk(new4)->inet_sport)\n",
   "  if ← branch .reinitHasNew4 new4.isSome then\n    let some port := new4 | invariant \"unreachable\"\n"
   "    modifyDev fun d => { d with incomingPort := port }   -- ntohs(inet_sk(new4)->inet_sport)\n"
   "  else modifyDev fun d => { d with incomingPort := 0 }\n", 'l_'),
  ('L-M4-set-port-stores-when-running', 'behavior: set_port stores the port instead of binding on a running '
   'device (netlink.c:326); l_set_port_running_inuse returns 0, l_set_port_running sends from 51820',
   'Leanux/WG/Netlink.lean', "  socketInit port\n",
   "  modifyDev fun d => { d with incomingPort := port }\n  return 0\n", 'l_'),
  ('L-M5-port-mod', 'data: the random port is low + rand % remaining instead of reciprocal_scale (udp.c:258); '
   'listen_port differs (l_random_port_natural, the steered traces)', 'Leanux/WG/Socket.lean',
   "  LOCAL_PORT_LOW + (rand * (LOCAL_PORT_HIGH - LOCAL_PORT_LOW + 1)) / 2 ^ 32\n",
   "  LOCAL_PORT_LOW + rand % (LOCAL_PORT_HIGH - LOCAL_PORT_LOW + 1)\n", 'l_'),
  ('L-M6-uninit-keeps-refcount', 'hidden: wg_ratelimiter_uninit does not drop init_refcnt (ratelimiter.c:208); '
   'the next creation leaves the ratelimiter_key record (l_delete_create, l_create_delete_create)',
   'Leanux/WG/Device.lean',
   "  modifyK fun k => { k with ratelimiter := { k.ratelimiter with refcnt := r - 1 } }\n", "", 'l_'),
  ('L-M7-ifindex-constant', 'data: register_netdevice gives ifindex 3 always (dev.c:10000-10018); '
   'the recreated device\'s dump differs (l_delete_create, l_create_delete_create)', 'Leanux/WG/Device.lean',
   "  modifyDev fun d => { d with ifindex }\n", "  modifyDev fun d => { d with ifindex := 3 }\n", 'l_'),
  ('L-M8-delete-skips-stop', 'hidden and control: deleting an up device skips wg_stop (dev.c:11526); '
   'the reset_last_sent record is left over (l_delete_up)', 'Leanux/WG/Device.lean',
   "  if (← getDev).running then wgDown\n", "", 'l_'),
  ('L-M9-failed-open-stays-running', 'behavior and control: a failed wg_open leaves __LINK_STATE_START set '
   '(dev.c:1556); the next port change binds (l_up_fixture_port)', 'Leanux/WG/Device.lean',
   "  if ret < 0 then modifyDev fun d => { d with running := false }\n", "", 'l_'),
  ('L-M10-update-gen-zero', 'data only, unobservable: device_update_gen starts at 0 (device.c:323); '
   'expected to pass (not claimed)', 'Leanux/WG/Device.lean',
   "  modifyDev fun d => { d with deviceUpdateGen := 1 }\n", "  modifyDev fun d => { d with deviceUpdateGen := 0 }\n",
   'l_'),
  ('L-M11-stop-keeps-keypairs', 'behavior and control: wg_stop does not clear the keypairs (device.c:126); '
   'the old session\'s data message is decrypted (l_down_after_session)', 'Leanux/WG/Device.lean',
   "    handshakeClear pid\n    keypairsClear pid\n", "    handshakeClear pid\n", 'l_'),
  ('L-M12-stop-keeps-handshake', 'behavior and control: wg_stop does not clear the handshake (device.c:125); '
   'the stale response is consumed (l_down_up_stale_response)', 'Leanux/WG/Device.lean',
   "    timersStop pid\n    handshakeClear pid\n", "    timersStop pid\n", 'l_'),
  ('L-M13-down-keeps-routes', 'environment: wg_down leaves the routes into wg0; the wg_xmit after it reaches '
   'wg_xmit (l_down_purges_staged)', 'Leanux/Env.lean',
   "  WG.wgDown\n  modify fun w => { w with routesViaWg0 := false }\n", "  WG.wgDown\n", 'l_'),
]
NOT_CLAIMED = {'L-M10-update-gen-zero', 'E-M6-under-load-threshold-gt'}
# evaluator.check on the traces of one suite whose ids start with a prefix
SUBSET = """import sys
sys.path.insert(0, '.')
import evaluator.check as c
prefix = sys.argv[1]
load = c.load_traces
c.load_traces = lambda *a, **k: [t for t in load(*a, **k) if t['id'].startswith(prefix)]
sys.exit(c.main(sys.argv[2:]))
"""
PENDING = {m[0] for m in D2_MUTANTS + D3_MUTANTS + L_MUTANTS if m[3] is None}
# Equivalent mutants: listed and reported as such, never run or scored as
# survivors [AGENT 2026-10-07, review S4].
EQUIVALENT = {
    'H-M8-response-unclamped': 'curve25519() clamps the scalar itself (lib/crypto/curve25519), so the '
                               'unclamped ephemeral gives the same public key and the same shared secret',
}

# The outcomes that are a verdict on the mirror: Linux and the mutated mirror
# disagree (behavior, control flow, hidden inputs), or the mutated mirror stops
# on its own (an invariant, a path outside its domain). Every other outcome
# (environment_failure, timeout, resource_busy, output_limit, crash,
# build_failure, invalid_output, invalid_coverage, invalid_input,
# missing_coverage, not_run, a guest error kind, anything new) is the
# infrastructure's: no verdict [AGENT 2026-10-07, review S2; as
# scripts/wg-d3-controls.py accepts only named mismatch kinds].
MISMATCH_OUTCOMES = frozenset({'semantic_mismatch', 'control_flow_mismatch', 'hidden_mismatch',
                               'mirror_invariant', 'unsupported_path'})

# A (allocation outcomes; docs/2026-10-05-a-alloc.md, section 7). Checked on
# the alloc suite (corpus/alloc: armed, steered traces); an unarmed run
# answers every allocation ok, so no other suite can reject these. A-M2
# (keypair_create, noise.c:100 record-only) and A-M4 (skb_cow_data never
# allocates on this fixture, A0) are dropped. The A2 entries (A-M1, A-M5,
# A-M6, A-M9, A-M13) are rejected by the a2_* traces of the (b-task)
# failslab-style extension [USER 2026-10-06]; A-M7/A-M8 by the a2_pipe_*
# traces since the D3+A integration (A's pipe sites, section 19.6).
A_MUTANTS = [
  ('A-M3-keepalive-sends-after-nomem', 'control: wg_packet_send_keepalive calls wg_packet_send_staged_packets '
   'after a failed allocation (send.c:228-229 returns). Survives on this base: both modeled callers (wg_open, '
   'set_peer) run wg_packet_send_staged_packets on the empty queue in the same operation, so the extra call '
   'changes no observation and covers nothing new; the distinguishing callers (receive.c:186 with an empty '
   'staged queue, the keepalive timers) are not reachable here',
   'Leanux/WG/Send.lean',
   "    if ← branch .keepaliveNoMem !(← hiddenAlloc .keepaliveSkb) then return\n",
   "    if ← branch .keepaliveNoMem !(← hiddenAlloc .keepaliveSkb) then return ← sendStagedPackets pid\n"),
  ('A-M10-sendbuf-ignores-record', 'behavior: wg_socket_send_buffer_to_peer ignores the allocation outcome '
   '(socket.c:194); a datagram Linux never sent', 'Leanux/WG/Handshake.lean',
   "  if ← branch .sendBufNoMem !(← hiddenAlloc .sendBufSkb) then return\n",
   "  _ ← hiddenAlloc .sendBufSkb\n  if ← branch .sendBufNoMem false then return\n"),
  ('A-M11-keepalive-ignores-record', 'behavior: wg_packet_send_keepalive ignores the allocation outcome '
   '(send.c:228); a keepalive staged (and an initiation sent) that Linux never had', 'Leanux/WG/Send.lean',
   "    if ← branch .keepaliveNoMem !(← hiddenAlloc .keepaliveSkb) then return\n",
   "    _ ← hiddenAlloc .keepaliveSkb\n    if ← branch .keepaliveNoMem false then return\n"),
  ('A-M12-alloc-skb-one-record', 'records: an __alloc_skb site consumes one record per consultation, not the '
   'sk_buff and then the data buffer (design 6.2, M6)', 'Leanux/Kernel/Defs.lean',
   '  | .sendBufSkb => ⟨11, "sendBufSkb", "drivers/net/wireguard/socket.c", 192, .exact 2⟩\n',
   '  | .sendBufSkb => ⟨11, "sendBufSkb", "drivers/net/wireguard/socket.c", 192, .exact 1⟩\n'),
  ('A-M1-peer-create-ignores-record', 'A2: wg_peer_create ignores the allocation outcome (peer.c:35)',
   'Leanux/WG/Peer.lean',
   "  if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)\n",
   "  _ ← hiddenAlloc .kmemCacheZallocPeer\n  if ← branch .peerCreateNoMem false then return .error (-ENOMEM)\n"),
  ('A-M5-fdtable-installed-after-nomem', 'A2: alloc_fdtable goes on after a failed fd array (file.c:152-154)',
   'Leanux/FS/File.lean',
   "  if ← branch .allocFdtableFdArrayNoMem !arrayOk then return .error (-ENOMEM)\n",
   "  _ ← branch .allocFdtableFdArrayNoMem !arrayOk\n"),
  ('A-M6-eventfd-keeps-fd', 'A2: do_eventfd forgets put_unused_fd on the file failure (eventfd.c:411-412)',
   'Leanux/FS/Eventfd.lean',
   "    putUnusedFd fd.toNat\n    eventfdFreeCtx cid  -- err:\n",
   "    eventfdFreeCtx cid  -- err:\n"),
  ('A-M7-pipe-accounting-kept', 'P/A2: alloc_pipe_info failure without the accounting revert (pipe.c:832); '
   'a2_pipe_bufs_nomem (the next pipe2\'s user_bufs operands)',
   'Leanux/FS/Pipe.lean',
   "  -- out_revert_acct:\n  _ ← accountPipeBuffers pipeBufs 0\n",
   "  -- out_revert_acct:\n"),
  ('A-M8-pipe-write-enomem', 'P/A2: pipe_write returns -ENOMEM instead of the partial count (pipe.c:515); '
   'a2_pipe_page_nomem_partial',
   'Leanux/FS/Pipe.lean',
   "          if !(← branchCmp .pipeWriteAllocRet (ret != 0) ret 0) then ret := -ENOMEM\n",
   "          _ ← branchCmp .pipeWriteAllocRet (ret != 0) ret 0\n          ret := -ENOMEM\n"),
  ('A-M9-intermediate-keeps-newnode', 'A2: add\'s third allocation failure keeps newnode (allowedips.c:235-239)',
   'Leanux/WG/AllowedIps.lean',
   "    listDel newnode\n    freeNode newnode\n    return -ENOMEM\n",
   "    return -ENOMEM\n"),
  # A2 (new): the one arm only a task-context failure reaches
  ('A-M13-dup3-enomem-as-ebadf', 'A2: ksys_dup3 maps every expand_files error to EBADF, not only EMFILE '
   '(file.c:1352-1354: ENOMEM is returned as is)', 'Leanux/FS/File.lean',
   "    if ← branch .dup3ExpandEmfile (err == -EMFILE) then return -EBADF\n",
   "    if ← branch .dup3ExpandEmfile true then return -EBADF\n"),
]
A_PENDING = {}
SUITE_OF = {m[0]: 'alloc' for m in A_MUTANTS}


def w4(text):
    fw = ("  if ← branch .setDevFwmark a.fwmark.isSome then\n"
          "    modifyDev fun d => { d with fwmark := a.fwmark.getD 0 }\n"
          "    for pid in (← getDev).peerList do\n"
          "      _ ← branch .setDevFwmarkPeerIter true\n"
          "      clearPeerEndpointSrc pid\n"
          "    _ ← branch .setDevFwmarkPeerIter false\n")
    port = ("  if ← branch .setDevPort a.listenPort.isSome then\n"
            "    let ret ← setPort (a.listenPort.getD 0)\n"
            "    if ← branch .setDevPortErr (ret != 0) then return ← zero ret\n")
    assert text.count(fw + port) == 1
    return text.replace(fw + port, port + fw)

def resched_records(out):
    """Kind-302 records (reschedules in task sections) in a run's Linux
    choice rows: a run with none cannot reject D1-M15."""
    n = 0
    for rows in glob.glob(os.path.join(ROOT, out, 'chunk-*', 'linux', 'hidden.jsonl')):
        for line in open(rows):
            row = json.loads(line)
            if row['mode'] == 'pc':
                n += sum(1 for r in row['records'] if r[0] & 0x7fff == 302)
    return n


def classify(report):
    """A mutant run's verdict from its check report (None: no report):
    (status, mismatch outcomes, other outcomes). 'rejected' needs a mismatch
    outcome in a run that was not aborted and has no other outcome; 'survived'
    needs a clean pass; any other run is 'no_verdict' (fail-closed: an
    infrastructure failure never counts as a rejection, and one beside a
    mismatch puts the run's oracle in doubt: a run against a kernel without
    the D3 ioctl fails the D3 traces `environment_failure` and the others
    `hidden_mismatch`) [AGENT 2026-10-07]."""
    if report is None:
        return 'no_verdict', [], ['no report']
    outcomes = {f['outcome'] for f in report['failures']}
    mismatches, other = sorted(outcomes & MISMATCH_OUTCOMES), sorted(outcomes - MISMATCH_OUTCOMES)
    if report.get('aborted'):
        return 'no_verdict', mismatches, other + ['aborted']
    if mismatches and not other:
        return 'rejected', mismatches, other
    if mismatches:
        return 'no_verdict', mismatches, other
    if report['status'] == 'pass' and not report['failures']:
        return 'survived', [], []
    return 'no_verdict', [], other or ['fail without failures']


def tally(results):
    """Counts per status, for the printed and the stored summary."""
    counts = {}
    for r in results.values():
        counts[r['status']] = counts.get(r['status'], 0) + 1
    return dict(sorted(counts.items()))


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def main():
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
    head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    mutants = MUTANTS + D1_MUTANTS + D2_MUTANTS + E_MUTANTS + E_UNDERLOAD_MUTANTS + D3_MUTANTS + L_MUTANTS + A_MUTANTS
    names = [m[0] for m in mutants]
    assert set(EQUIVALENT) <= set(names), 'an EQUIVALENT entry names no mutant'
    assert NOT_CLAIMED <= set(names), 'a NOT_CLAIMED entry names no mutant'
    selected = sys.argv[1:] or names
    unknown = sorted(set(selected) - set(names))
    if unknown:
        raise SystemExit(f'unknown mutants: {unknown}')
    results = {}
    for name, what, path, old, new, *subset in mutants:
        if name not in selected:
            continue
        if name in PENDING:   # a draft entry: its pattern is filled at integration
            results[name] = dict(description=what, base=head, file=path, status='pending')
            print(name, 'pending (no pattern yet)', flush=True)
            continue
        if name in A_PENDING:
            if old is not None:   # the pattern still matches the code
                assert open(os.path.join(ROOT, path)).read().count(old) == 1, f'{name}: pattern not unique/present'
            results[name] = dict(description=what, base=head, file=path, status='pending', reason=A_PENDING[name])
            print(name, A_PENDING[name], flush=True)
            continue
        if name in EQUIVALENT:
            results[name] = dict(description=what, base=head, file=path, status='equivalent',
                                 reason=EQUIVALENT[name])
            print(name, 'equivalent (not run):', EQUIVALENT[name], flush=True)
            continue
        full = os.path.join(ROOT, path)
        text = open(full).read()
        if old is None:
            mutated = w4(text)
        else:
            assert text.count(old) == 1, f'{name}: pattern not unique/present'
            mutated = text.replace(old, new)
        open(full, 'w').write(mutated)
        try:
            diff = run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout
            assert path in diff, f'{name}: mutation not applied'
            out = f'.artifacts/check/mutant-{name}'
            run(['rm', '-rf', out])
            # L: a sixth field restricts the suite to the traces whose ids start with it;
            # A: its mutants run on the alloc suite (SUITE_OF)
            check = ['-c', SUBSET, subset[0]] if subset else ['-m', 'evaluator.check']
            proc = run(['timeout', '3000', sys.executable, *check, '--suite', SUITE_OF.get(name, 'wireguard'),
                        '--out', out], capture_output=True, text=True)
            path_report = os.path.join(ROOT, out, 'report.json')
            report = json.load(open(path_report)) if os.path.exists(path_report) else None
            status, mismatches, other = classify(report)
            if report is None:
                results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status=status,
                                     no_verdict=other, stderr=proc.stderr[-2000:])
                print(name, status, '(no report)', proc.stderr[-400:], flush=True)
                continue
            kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                           {f['outcome'] for f in report['failures']})
            results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status=status,
                                 check_status=report['status'], counts=report['counts'], failure_kinds=kinds,
                                 mismatch_outcomes=mismatches, other_outcomes=other, aborted=report.get('aborted'),
                                 report=out + '/report.json', resched_records=resched_records(out))
            if name == 'D1-M15-ignore-resched' and status == 'survived' and not results[name]['resched_records']:
                results[name]['status'] = 'inconclusive'   # no reschedule occurred to ignore
            if name in NOT_CLAIMED:   # L-M10: run, expected to survive, never evidence
                results[name]['status'] = 'not-claimed-' + results[name]['status']
            if name == 'D2-M12-poll-outside-worker':
                orders = napi_orders(os.path.join(ROOT, out))
                results[name]['napi_orders'] = dict(a=orders['a'], bc=orders['bc'])
                if status == 'survived' and not orders['bc']:
                    results[name]['status'] = 'inconclusive'   # only order (a) occurred, which cannot reject it
            print(name, results[name]['status'], report['counts'], kinds, 'other', other,
                  'resched', results[name]['resched_records'], flush=True)
        finally:
            run(['git', 'checkout', '--', path])
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
    totals = tally(results)
    os.makedirs(os.path.join(ROOT, '.artifacts/check'), exist_ok=True)
    json.dump(dict(results, totals=totals), open(os.path.join(ROOT, '.artifacts/check/mutants-summary.json'), 'w'),
              indent=2)
    print('totals', totals, flush=True)
    no_verdict = sorted(n for n, r in results.items() if r['status'] == 'no_verdict')
    if no_verdict:
        print('NO VERDICT (infrastructure; rerun these):', ' '.join(no_verdict), flush=True)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
