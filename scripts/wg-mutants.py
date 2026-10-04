"""WireGuard mutants (stage A report, section 2; stages B1, B2 and C).

Each mutant is applied to a clean committed tree, verified as applied, checked
on the wireguard suite, then reverted. Run from the repository root:

    scripts/in-bundle python3 scripts/wg-mutants.py [NAME ...]

Every mutant must be rejected (status fail). W5 also aborts on a mirror
invariant; run `--trace wg_trie_v6` by hand to see A2 alone reject it.
"""
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
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
  ('C-M3-no-rx-traversal', 'behavior-preserving: no traversal timer after receiving', 'Leanux/WG/Receive.lean',
   "  setPeer pid { p with rxBytes := p.rxBytes + msg.length }\n  timersTraversal pid\n",
   "  setPeer pid { p with rxBytes := p.rxBytes + msg.length }\n"),
  ('C-M4-keypair-kept-indexed', 'behavior-preserving: the old next keypair stays in the index', 'Leanux/WG/Keypair.lean',
   '    keypairPut next true\n',
   '    keypairPut next false\n'),
  ('C-M5-endpoint-family-swapped', 'data: the learned endpoint tests IPv6 first', 'Leanux/WG/Handshake.lean',
   "    if ← branch .epFromSkbInet (src.family == 4) then\n",
   "    if ← branch .epFromSkbInet (src.family == 6) then\n"),
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
   "    timersTraversal pid\n    -- wg_timers_any_authenticated_packet_sent: del_timer\n    let now ← hiddenClock .initLastSentAgain\n",
   "    -- wg_timers_any_authenticated_packet_sent: del_timer\n    let now ← hiddenClock .initLastSentAgain\n"),
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
  ('H-M11-no-fixture-cut', 'negative control: cut records in an operation without its cut point (wg_xmit)',
   'Leanux/Syscalls.lean',
   '    Env.fixtureSend\n    let ret ← WG.wgXmit family addr (Env.xmitPacketLen family)\n',
   '    let ret ← WG.wgXmit family addr (Env.xmitPacketLen family)\n'),
  # Choice stream, step 2: paths only steering reaches
  ('S2-M1-lookup-ignores-type', 'state: the index lookup ignores its type mask', 'Leanux/WG/Peer.lean',
   "      if ← branch .idxTypeMatch (kinds.contains e.kind) then entry := some e\n",
   "      if ← branch .idxTypeMatch true then entry := some e\n"),
  ('S2-M2-insert-keeps-collision', 'state: the insert does not redraw after an unlocked collision',
   'Leanux/WG/Peer.lean',
   "    if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then continue\n",
   "    let _ ← bucketHas .idxInsWalk1 .idxInsCollide1 index\n"),
]

# Stage D1 (wg0 initiates), a draft: streams B and C write the targeted mirror
# code, so the patterns (old, new) are filled in at integration. Entries:
# (name, description, file, old, new, traces expected to reject it). Not run
# until they move into MUTANTS with their patterns.
D1_MUTANTS = [
  ('D1-M1-keys-responder-order', 'data: begin_session derives the initiator\'s keys in responder order',
   'Leanux/WG/Handshake.lean',
   "  setKeypair kp (if initiator then { k with sending := first, receiving := second }\n",
   "  setKeypair kp (if initiator then { k with sending := second, receiving := first }\n"),
  ('D1-M2-key-idx-internal', 'data: encrypt_packet writes the keypair\'s internal id as key_idx (send.c:207)',
   'Leanux/WG/Data.lean',
   "  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key (List.replicate plaintextLen 0))\n",
   "  return some (dataMessage k.internalId pkt.nonce k.sending.key (List.replicate plaintextLen 0))\n"),
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
   "  let paddingLen ← calculateSkbPadding pkt.plaintextLen DEVICE_MTU\n",
   "  let paddingLen ← (do let _ ← calculateSkbPadding pkt.plaintextLen DEVICE_MTU; pure 16)\n"),
  ('D1-M12-no-walltime', 'data: walltime_last_handshake is consumed but not stored (timers.c:197)',
   'Leanux/WG/Handshake.lean',
   "  let now ← hidden .walltimeLastHandshake\n  setPeer pid { (← getPeer pid) with walltimeLastHandshake := now }\n",
   "  let _ ← hidden .walltimeLastHandshake\n"),
  ('D1-M13-no-keep-key-fresh', 'control, behavior-preserving: the tx worker skips keep_key_fresh (send.c:259)',
   'Leanux/WG/Data.lean',
   "  if ← branch .doneDataSent dataSent then unsupported \"wg_timers_data_sent (a data packet's handshake timer)\"\n  keepKeyFresh pid\n",
   "  if ← branch .doneDataSent dataSent then unsupported \"wg_timers_data_sent (a data packet's handshake timer)\"\n"),
  ('D1-M14-no-keypair-put-tx', 'control, behavior-preserving: the tx worker keeps its keypair reference (send.c:280)',
   'Leanux/WG/Data.lean',
   "    keypairPut (some pkt.keypair) false\n    peerPut (some pid)\n    _ ← branch .txNeedResched (← needResched)\n",
   "    peerPut (some pid)\n    _ ← branch .txNeedResched (← needResched)\n"),
  ('D1-M15-ignore-resched', 'scheduling: cond_resched never switches, ignoring the resched records (kind 302); the corpus has receive-worker reschedules, though whether one occurs is timing-dependent',
   'Leanux/Env.lean',
   "    if (← peekHiddenSite) != some site.info.id then return false\n",
   "    if true then return false\n"),
]

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

def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)

assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
MUTANTS = MUTANTS + D1_MUTANTS
selected = sys.argv[1:] or [m[0] for m in MUTANTS]
results = {}
for name, what, path, old, new in MUTANTS:
    if name not in selected:
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
        proc = run(['timeout', '3000', sys.executable, '-m', 'evaluator.check', '--suite', 'wireguard',
                    '--out', out], capture_output=True, text=True)
        report = json.load(open(os.path.join(ROOT, out, 'report.json')))
        kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                       {f['outcome'] for f in report['failures']})
        results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status=report['status'],
                             counts=report['counts'], failure_kinds=kinds, report=out + '/report.json')
        print(name, report['status'], report['counts'], kinds, flush=True)
    finally:
        run(['git', 'checkout', '--', path])
assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
json.dump(results, open(os.path.join(ROOT, '.artifacts/check/mutants-summary.json'), 'w'), indent=2)
