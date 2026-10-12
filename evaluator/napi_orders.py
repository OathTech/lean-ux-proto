"""Where the decrypt worker's NAPI poll ran, per received data message, in a
check run's Linux choice records (docs/2026-10-04-d2-data-plane.md, section
5): order (a), a NET_RX section right after the decrypt worker's resched
record (ksoftirqd took the softirq at the worker's cond_resched), or order
(b/c), a NET_RX section inside the decrypt worker's section without one
(the softirq ran inline at the next bh-enable or at an interrupt exit).

The scheduling control D2-M12 is rejected only by a (b/c) placement, so a
mutant run with none is inconclusive.

W7 stream H (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.3 and 5.4) adds, per
coverage-child operation:
- `polls_per_run`: the NET_RX sections nested in each decrypt-worker
  section (a histogram: polls -> runs), and the (a)/(b/c) split above;
- `nested_yields`: the phase-1 nesting proxy, a resched record (kind 302)
  inside a unit's section that is itself inside another unit's section
  (the softirq excluded: `net_rx_action` never yields mid-poll), per
  (outer, inner) pair; with multi-item queues each such yield is a phase-1
  rejection whenever the outer has queued work.
The items per poll are the mirror's (`wg_prev_queue_peek.peeked` and the
dequeue outcomes in the report's decision table), not the records'. Usage:

    scripts/in-bundle python3 -m evaluator.napi_orders RUN_DIR
"""
import glob
import json
import os
import sys

from harness.linux import DISPATCH_SYMBOLS, dispatch_addresses

SECTION_START, SECTION_STOP, RESCHED = 300, 301, 302


def napi_orders(run_dir, kernel=None):
    """{'a': n, 'bc': n, 'bc_ops': [(trace, op), ...], 'polls_per_run': {polls: runs},
    'nested_yields': {'outer>inner': n}, 'nested_yield_ops': [(trace, op), ...]}
    over the coverage child's records of every chunk in `run_dir`."""
    addresses = dict(zip(DISPATCH_SYMBOLS, dispatch_addresses(kernel)))
    names = {a: s for s, a in addresses.items()}
    decrypt, netrx = addresses['wg_packet_decrypt_worker'], addresses['net_rx_action']
    ops = {}
    for path in glob.glob(os.path.join(run_dir, 'chunk-*', 'linux', 'hidden.jsonl')):
        for line in open(path):
            row = json.loads(line)
            if row['mode'] == 'pc':
                ops.setdefault((os.path.dirname(path), row['id'], row['index']), []).extend(row['records'])
    counts = {'a': 0, 'bc': 0, 'bc_ops': [], 'polls_per_run': {}, 'nested_yields': {}, 'nested_yield_ops': []}
    for (_, trace, index), records in sorted(ops.items()):
        # open sections in sequence order (a stop names no function: it
        # closes the innermost open one), and the previous record's kind
        open_, previous = [], None
        polls = []   # per open decrypt-worker section, its poll count (stack)
        for kind, _, _, _, data in sorted(records, key=lambda r: r[2]):
            kind &= 0x7fff
            if kind == SECTION_START:
                # a start record is {func, unit} (16 bytes) since the
                # dispatch-order capture; its first word is the function
                func = int.from_bytes(bytes.fromhex(data[:16]), 'little')
                if func == netrx and decrypt in open_:
                    if previous == RESCHED:
                        counts['a'] += 1
                    else:
                        counts['bc'] += 1
                        counts['bc_ops'].append((trace, index))
                    if polls:
                        polls[-1] += 1
                if func == decrypt:
                    polls.append(0)
                open_.append(func)
            elif kind == SECTION_STOP and open_:
                func = open_.pop()
                if func == decrypt and polls:
                    n = polls.pop()
                    counts['polls_per_run'][n] = counts['polls_per_run'].get(n, 0) + 1
            elif kind == RESCHED:
                # the phase-1 nesting proxy: a yield in a unit nested in
                # another unit (softirq sections do not count as units)
                units = [f for f in open_ if f != netrx]
                if len(units) >= 2:
                    pair = f"{names.get(units[-2], hex(units[-2]))}>{names.get(units[-1], hex(units[-1]))}"
                    counts['nested_yields'][pair] = counts['nested_yields'].get(pair, 0) + 1
                    counts['nested_yield_ops'].append((trace, index))
            previous = kind
    return counts


def phase1_rejections(run_dir):
    """The traces the mirror rejected with the phase-1 nesting detector
    (`Env/Batch.lean` condResched), from the run's report."""
    path = os.path.join(run_dir, 'report.json')
    if not os.path.exists(path):
        return []
    report = json.load(open(path))
    return [f['id'] for f in report.get('failures', [])
            if 'yielded below an open worker with queued work' in (f.get('detail') or '')]


if __name__ == '__main__':
    result = napi_orders(sys.argv[1])
    result['phase1_rejections'] = phase1_rejections(sys.argv[1])
    print(json.dumps(result, indent=1))
