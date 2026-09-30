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
