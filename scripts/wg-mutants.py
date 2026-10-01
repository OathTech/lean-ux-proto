"""WireGuard stage A mutants (stage A report, section 2).

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
   "  keypairGetCurrent\n  if !(← branch .stagedNoKeypair true)",
   "  if !(← branch .stagedNoKeypair true)"),
  ('B1-M3-xmit-keeps-reference', 'behavior-preserving: wg_xmit never drops its peer reference', 'Leanux/WG/Device.lean',
   "  sendStagedPackets pid\n  peerPut peer\n  return 0   -- NETDEV_TX_OK",
   "  sendStagedPackets pid\n  return 0   -- NETDEV_TX_OK"),
  ('B1-M4-low-order-emits', 'behavior: the worker emits for a low-order peer key', 'Leanux/Env.lean',
   "    let created := d.staticIdentity.hasIdentity && p.precomputedStaticStatic != List.replicate 32 0\n",
   "    let created := d.staticIdentity.hasIdentity\n"),
  ('B1-M5-dead-before-expired', 'behavior-preserving: is_dead tested before the expiry', 'Leanux/WG/Send.lean',
   "  if ← branch .queuedNotExpired !p.lastSentExpired then return\n  if ← branch .queuedDead p.isDead then return\n",
   "  if ← branch .queuedDead p.isDead then return\n  if ← branch .queuedNotExpired !p.lastSentExpired then return\n"),
  # Stage B2 (receive)
  ('B2-M1-no-header-pull', 'parsing: a message shorter than its header passes the pull', 'Leanux/WG/Receive.lean',
   "  if ← orM (branch .prepPullFailed (msg.length < 4)) (branch .prepTrimFailed false) then return false\n",
   "  if ← orM (branch .prepPullFailed false) (branch .prepTrimFailed false) then return false\n"),
  ('B2-M2-cpu-never-wraps', 'state: last_cpu never wraps', 'Leanux/WG/Receive.lean',
   "    if ← branch .cpumaskWrap (next ≥ 1) then pure (0 : Int) else pure next\n",
   "    if ← branch .cpumaskWrap false then pure (0 : Int) else pure next\n"),
  ('B2-M3-length-before-type', 'order: validate_header_len tests the length first', 'Leanux/WG/Receive.lean',
   "  if ← andM (branch .hdrInit (t == MESSAGE_HANDSHAKE_INITIATION)) (branch .hdrInitLen (len == 148)) then\n",
   "  if ← andM (branch .hdrInitLen (len == 148)) (branch .hdrInit (t == MESSAGE_HANDSHAKE_INITIATION)) then\n"),
  ('B2-M4-response-off-by-one', 'parsing: a 91-byte response is accepted', 'Leanux/WG/Receive.lean',
   "(branch .hdrRespLen (len == 92)) then\n    return 92",
   "(branch .hdrRespLen (len == 92 || len == 91)) then\n    return 92"),
]

def w4(text):
    fw = ("  if ← branch .setDevFwmark a.fwmark.isSome then\n"
          "    modifyDev fun d => { d with fwmark := a.fwmark.getD 0 }\n"
          "    -- wg_socket_clear_peer_endpoint_src on each peer: see setPort\n"
          "    for _ in (← getDev).peerList do _ ← branch .setDevFwmarkPeerIter true\n"
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
