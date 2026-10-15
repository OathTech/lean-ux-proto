"""The sentinel mutants: the speedbump that shows each verdict channel and
record instrument of the check still rejects a wrong mirror (AGENTS.md,
"Gates and speedbumps"). One entry per channel, each applied to a clean
committed tree, verified as applied, checked on the smallest corpus subset
that rejects it, then reverted. Run from the repository root at a claim
point (an integration, a stage):

    scripts/in-bundle python3 scripts/wg-mutants.py [NAME ...]

Every sentinel must be rejected: its run must end in a mirror-side verdict
(MISMATCH_OUTCOMES) with no other outcome. A run that fails only on the
infrastructure (an environment failure, a timeout, a busy QEMU slot, an
aborted run, no report) is "no_verdict", never a rejection, and the script
exits 1. Two sentinels' rejection depends on an order the kernel chose
(D2-M12's NAPI placement, Q-M1's dispatch order): a run in which the
recorded order cannot distinguish the mutant is "inconclusive", with the
distinguishing counts in the summary, not a survival (claim-point
robustness, 2026-10-13).

The catalogue this set was chosen from (about a hundred entries, one per
design item, 2026-09-30 to 2026-10-11) is in git history before this file's
2026-10-12 rewrite. A new instrument on the trust surface gets a one-off
mutant: add an entry here, run it by name once, report the result in the
instrument's commit, then delete the entry unless it replaces the sentinel of
its channel. Fields: (name, channel, what it changes, file, old, new, the id
prefix of the corpus subset or '' for the whole suite, the suite).
"""
import glob
import json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from evaluator.napi_orders import napi_orders  # noqa: E402
from evaluator.dispatch_orders import dispatch_orders  # noqa: E402

SENTINELS = [
  ('C-M2-receiver-is-sender',
   'semantic mismatch: an observation differs (a datagram byte)',
   'data: the response names its own index as the receiver',
   'Leanux/WG/Handshake.lean',
   '  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)\n',
   '  return some (le32 2 ++ le32 index ++ le32 index ++ e ++ encNothing ++ List.replicate 32 0)\n',
   'c_', 'wireguard'),
  ('B1-M5-dead-before-expired',
   'control-flow mismatch: decisions reordered (decision order differs from Linux)',
   'behavior-preserving: is_dead tested before the expiry',
   'Leanux/WG/Send.lean',
   '  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return\n  if ← branch .queuedDead p.isDead then return\n',
   '  if ← branch .queuedDead p.isDead then return\n  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return\n',
   'b1_', 'wireguard'),
  ('H-M7-flood-threshold',
   'operand comparison: operands differ from Linux on a declared comparison',
   'decision-preserving: the flood window is 200 ms (5 initiations a second)',
   'Leanux/WG/Handshake.lean',
   '  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64\n',
   '  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / 5\n',
   'c_', 'wireguard'),
  ('H-M1-tai64n-unrounded',
   'hidden record: a recorded value used wrongly (the timestamp keeps its nanoseconds)',
   'data: the timestamp keeps its nanoseconds',
   'Leanux/WG/Handshake.lean',
   '  be ((0x400000000000000a + sec) % 2 ^ 64) 8 ++ be (nsec - nsec % 2 ^ 24) 4\n',
   '  be ((0x400000000000000a + sec) % 2 ^ 64) 8 ++ be nsec 4\n',
   'b1_', 'wireguard'),
  ('H-M6-clock-before-ephemeral',
   'hidden record at the wrong site: the records are consumed out of order',
   'negative control: the clock is read before the ephemeral key',
   'Leanux/WG/Handshake.lean',
   '  let secret := clamp (← hidden .initEphemeral)\n',
   '  let _ ← hidden .tai64nNow\n  let secret := clamp (← hidden .initEphemeral)\n',
   'b1_', 'wireguard'),
  ('S2-M2-insert-keeps-collision',
   'unsupported_path stop: the mirror leaves its domain',
   'state: the insert does not redraw after an unlocked collision',
   'Leanux/WG/Peer.lean',
   '    if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then continue\n',
   '    let _ ← bucketHas .idxInsWalk1 .idxInsCollide1 index\n',
   's2_', 'wireguard'),
  ('B1-M4-low-order-emits',
   'mirror_invariant stop: an invariant the mirror checks itself',
   'behavior: the initiation ignores a null ephemeral-static DH (now the mirrored worker)',
   'Leanux/WG/Handshake.lean',
   '  if ← branch .initEsFailed es.isNone then return none\n',
   '  if ← branch .initEsFailed false then return none\n',
   'b1_', 'wireguard'),
  ('Q-M1-dispatch-order-ignored',
   'dispatch identity: the unit a section names (kind 307, the start record)',
   'dispatch order: the send worker runs the queue head, not the unit the record names; rejected only when a run '
   'shows a dispatch that was not the FIFO head with two pending (timing-dependent, evaluator/dispatch_orders.py)',
   'Leanux/Env.lean',
   '    | some u => resolveUnit .sendWorker u d.sendWorkQueue\n    | none => pure headPid\n',
   '    | some _ => pure headPid\n    | none => pure headPid\n',
   's2_', 'wireguard'),
  ('D3-M8-new-handshake-delay',
   'timer arm record (kind 303): expires differs',
   'arm record: timer_new_handshake armed at KEEPALIVE_TIMEOUT instead of KEEPALIVE_TIMEOUT + REKEY_TIMEOUT (timers.c:149); only the kind-303 expires check sees it (every trace that sends data after a session)',
   'Leanux/WG/Handshake.lean',
   '      armTimer pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) jc\n',
   '      armTimer pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + jitter) jc\n',
   'd3_', 'wireguard'),
  ('D2-M12-poll-outside-worker',
   'section placement: a NET_RX section outside the worker it nests in',
   "scheduling control: the NAPI poll runs after the decrypt worker's section instead of inside it (design section 5); rejected only when a run shows order (b) (timing-dependent)",
   'Leanux/Env/Batch.lean',
   '  | .decryptWorker => WG.decryptIter napiSoftirq napiIrqExit (condResched .decryptWorker)\n',
   '  | .decryptWorker => WG.decryptIter (pure ()) (pure ()) (condResched .decryptWorker)\n',
   'rx_', 'wireguard'),
  ('A-M10-sendbuf-ignores-record',
   'allocation outcome record (kind 305): the outcome is ignored',
   'behavior: wg_socket_send_buffer_to_peer ignores the allocation outcome (socket.c:194); a datagram Linux never sent',
   'Leanux/WG/Handshake.lean',
   '  if ← branch .sendBufNoMem !(← hiddenAlloc .sendBufSkb) then return\n',
   '  _ ← hiddenAlloc .sendBufSkb\n  if ← branch .sendBufNoMem false then return\n',
   '', 'alloc'),
  ('W7-M9-resched-ignored-bulk',
   'bulk scheduling (W7, Env/Batch.lean condResched): the units a resched record switched to are not run',
   "scheduling: the per-item resched record is consumed but the worker does not yield, so the units the kernel ran at the switch are not run there (D1-M15's bulk form)",
   'Leanux/Env/Batch.lean',
   "  _ ← hidden site\n  return true\n",
   "  _ ← hidden site\n  return false\n",
   'w7_', 'wireguard'),
  ('W9-M3-cache-never-hits',
   'dst-cache jiffies record (kind 306): the recorded jiffies are ignored (the cache never hits)',
   'data: the dst cache never hits (every send misses: socket.c:51 and the arms 53-82); the data send of '
   'w9_session_two_sends hits in Linux (the keepalive after the session cached the dst)',
   'Leanux/WG/Socket.lean',
   "    if timeAfter c.refreshTs c.resetTs && s.gen == gen then return some s\n",
   "    if false && timeAfter c.refreshTs c.resetTs && s.gen == gen then return some s\n",
   'w9_session_two', 'wireguard'),
  # ---- B3, one-off (docs/2026-10-15-design-b3-timer-wheel.md, section 9): the
  # timer wheel's arithmetic and order, and the kind-313/314 instrument. Each
  # run once by name at the build's claim point, the result in its commit,
  # then deleted (none replaces a sentinel's channel) [AGENT 2026-10-15].
  ('B3-M1-round-down',
   'hidden-input mismatch: the kind-314 bucket expiry differs (calc_index rounds up)',
   'arithmetic: calc_index without the + 1, so a bucket expiry at or before the expiry',
   'Leanux/Kernel/TimerWheel.lean',
   '  let e := (expires >>> (LVL_SHIFT lvl).toUInt64) + 1\n',
   '  let e := (expires >>> (LVL_SHIFT lvl).toUInt64)\n',
   'd3_persistent_k', 'wireguard'),
  ('B3-M2-level-threshold',
   'hidden-input mismatch: the kind-314 slot differs (the level threshold)',
   'arithmetic: LVL_START(4) as 135001, the zero-key timer (135000) on level 3 (slot 192+, width 512)',
   'Leanux/Kernel/TimerWheel.lean',
   '  else if delta < LVL_START 4 then calcIndex expires 3\n',
   '  else if delta < 135001 then calcIndex expires 3\n',
   'd3_persistent_k', 'wireguard'),
  ('B3-M3-fifo-in-bucket',
   'hidden-input mismatch: the section names another timer than the wheel runs next (LIFO within a slot)',
   'order: the oldest enqueue first within a slot',
   'Leanux/Kernel/TimerWheel.lean',
   '      && (levelOf a.slot > levelOf b.slot || (levelOf a.slot == levelOf b.slot && a.enqueued > b.enqueued)))\n',
   '      && (levelOf a.slot > levelOf b.slot || (levelOf a.slot == levelOf b.slot && a.enqueued < b.enqueued)))\n',
   'w12_retransmit_lifo', 'wireguard'),
  ('B3-M5-never-keeps-slot',
   'hidden-input mismatch: a kind-314 record expected on a same-slot re-arm (the C keeps the slot)',
   'control flow: every re-arm re-enqueues (the same-slot path of __mod_timer :1123-1130 gone)',
   'Leanux/Kernel/TimerWheel.lean',
   '  | some we => if we.slot == slot then .kept we else .enqueued slot bexp\n',
   '  | some _ => .enqueued slot bexp\n',
   'd3_persistent_k', 'wireguard'),
  ('B3-M6-between-zone-fires',
   'hidden-input mismatch: a timer due by its expiry but not by its bucket (the between zone) never fires',
   'rule: expires instead of the bucket expiry as the due test',
   'Leanux/Kernel/TimerWheel.lean',
   '        (p.wheel t).bind fun we => if timeBeforeEq we.bucketExpiry j then some (pid, t, we) else none\n',
   '        (p.wheel t).bind fun we => if timeBeforeEq ((p.timer t).getD we.bucketExpiry) j then some (pid, t, we) else none\n',
   'd3_between_zone', 'wireguard'),
  ('B3-M7-clk-is-jm',
   'hidden-input mismatch: the kind-314 slot differs (the base clock taken as mod_timer\'s read)',
   'instrument: the kind-313 base clock ignored (clk := J_m), a re-arm inside a catch-up pass on level 2 instead of 3',
   'Leanux/WG/State.lean',
   '  let (clk, u2) := (recordWord64 cb 0, recordWord cb 1)\n',
   '  let (clk, u2) := (jm, recordWord cb 1)\n',
   'd3_keepalive_rearm_catchup', 'wireguard'),
]

# evaluator.check on the traces of one suite whose ids start with a prefix
SUBSET = """import sys
sys.path.insert(0, '.')
import evaluator.check as c
prefix = tuple(sys.argv[1].split(','))   # one id prefix, or several comma-separated
load = c.load_traces
c.load_traces = lambda *a, **k: [t for t in load(*a, **k) if t['id'].startswith(prefix)]
sys.exit(c.main(sys.argv[2:]))
"""

# The outcomes that are a verdict on the mirror: Linux and the mutated mirror
# disagree (behavior, control flow, hidden inputs), or the mutated mirror stops
# on its own (an invariant, a path outside its domain). Every other outcome
# (environment_failure, timeout, resource_busy, output_limit, crash,
# build_failure, invalid_output, invalid_coverage, invalid_input,
# missing_coverage, not_run, a guest error kind, anything new) is the
# infrastructure's: no verdict.
MISMATCH_OUTCOMES = frozenset({'semantic_mismatch', 'control_flow_mismatch', 'hidden_mismatch',
                               'mirror_invariant', 'unsupported_path'})


def classify(report):
    """A mutant run's verdict from its check report (None: no report):
    (status, mismatch outcomes, other outcomes). 'rejected' needs a mismatch
    outcome in a run that was not aborted and has no other outcome; 'survived'
    needs a clean pass; any other run is 'no_verdict' (fail-closed: an
    infrastructure failure never counts as a rejection, and one beside a
    mismatch puts the run's oracle in doubt)."""
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
    counts = {}
    for r in results.values():
        counts[r['status']] = counts.get(r['status'], 0) + 1
    return dict(sorted(counts.items()))


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def main():
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
    head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    names = [m[0] for m in SENTINELS]
    selected = sys.argv[1:] or names
    unknown = sorted(set(selected) - set(names))
    if unknown:
        raise SystemExit(f'unknown mutants: {unknown}')
    results = {}
    for name, channel, what, path, old, new, subset, suite in SENTINELS:
        if name not in selected:
            continue
        full = os.path.join(ROOT, path)
        text = open(full).read()
        assert text.count(old) == 1, f'{name}: pattern not unique/present'
        open(full, 'w').write(text.replace(old, new))
        try:
            diff = run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout
            assert path in diff, f'{name}: mutation not applied'
            out = f'.artifacts/check/mutant-{name}'
            run(['rm', '-rf', out])
            check = ['-c', SUBSET, subset] if subset else ['-m', 'evaluator.check']
            proc = run(['timeout', '3000', sys.executable, *check, '--suite', suite, '--out', out],
                       capture_output=True, text=True)
            path_report = os.path.join(ROOT, out, 'report.json')
            report = json.load(open(path_report)) if os.path.exists(path_report) else None
            status, mismatches, other = classify(report)
            if report is None:
                results[name] = dict(channel=channel, description=what, base=head, file=path, exit=proc.returncode,
                                     status=status, no_verdict=other, stderr=proc.stderr[-2000:])
                print(name, status, '(no report)', proc.stderr[-400:], flush=True)
                continue
            kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                           {f['outcome'] for f in report['failures']})
            results[name] = dict(channel=channel, description=what, base=head, file=path, exit=proc.returncode,
                                 status=status, check_status=report['status'], counts=report['counts'],
                                 failure_kinds=kinds, mismatch_outcomes=mismatches, other_outcomes=other,
                                 aborted=report.get('aborted'), report=out + '/report.json')
            if name == 'D2-M12-poll-outside-worker':
                orders = napi_orders(os.path.join(ROOT, out))
                results[name]['napi_orders'] = dict(a=orders['a'], bc=orders['bc'])
                if status == 'survived' and not orders['bc']:
                    results[name]['status'] = 'inconclusive'   # only order (a) occurred, which cannot reject it
            if name == 'Q-M1-dispatch-order-ignored':
                # the same class: the recorded dispatch order distinguishes the
                # mutant only when a dispatch ran a unit that was not the FIFO
                # head with two pending (evaluator/dispatch_orders.py)
                orders = dispatch_orders(os.path.join(ROOT, out))
                results[name]['dispatch_orders'] = dict(fifo=orders['fifo'], non_fifo=orders['non_fifo'],
                                                        single=orders['single'])
                if status == 'survived' and not orders['non_fifo']:
                    results[name]['status'] = 'inconclusive'   # every dispatch ran the FIFO head, which cannot reject it
            print(name, results[name]['status'], report['counts'], kinds, 'other', other, flush=True)
        finally:
            run(['git', 'checkout', '--', path])
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
    totals = tally(results)
    os.makedirs(os.path.join(ROOT, '.artifacts/check'), exist_ok=True)
    json.dump(dict(results, totals=totals), open(os.path.join(ROOT, '.artifacts/check/mutants-summary.json'), 'w'),
              indent=2)
    print('totals', totals, flush=True)
    inconclusive = sorted(n for n, r in results.items() if r['status'] == 'inconclusive')
    bad = sorted(n for n, r in results.items() if r['status'] not in ('rejected', 'inconclusive'))
    if inconclusive:
        print('INCONCLUSIVE (the recorded order did not distinguish the mutant this run; rerun alone, where it must '
              'reject):', ' '.join(inconclusive), flush=True)
    if bad:
        print('NOT REJECTED (a survivor is a defect in the check; no verdict is infrastructure, rerun):', ' '.join(bad), flush=True)
    return 1 if bad or inconclusive else 0


if __name__ == '__main__':
    sys.exit(main())
