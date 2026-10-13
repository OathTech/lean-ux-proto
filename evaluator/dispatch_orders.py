"""Whether the handshake send worker's dispatch order distinguishes the
dispatch-identity sentinel (Q-M1-dispatch-order-ignored) in a check run's
Linux choice records. `handshake_send_wq` is unbound
(docs/2026-10-11-dispatch-order.md), so two queued units may run in either
order; the kernel's queue record (kind 307 `{work, func}` at `__queue_work`)
names each unit as it is queued and the section start (kind 300
`{func, unit}`) names the unit each dispatch ran. The mutant runs the queue
head instead of the unit the start record names, so it is rejected only by
an operation in which a dispatch ran a unit that was not the head of the
pending FIFO while at least two were pending ("non-FIFO"); a run with none
is inconclusive (the same class as D2-M12's placement orders,
`evaluator/napi_orders.py`). Usage:
    scripts/in-bundle python3 -m evaluator.dispatch_orders RUN_DIR
"""
import glob
import json
import os
import sys

from harness.linux import DISPATCH_SYMBOLS, dispatch_addresses

SECTION_START, QUEUE = 300, 307


def dispatch_orders(run_dir, kernel=None, symbol='wg_packet_handshake_send_worker'):
    """{'fifo': n, 'non_fifo': n, 'non_fifo_ops': [(trace, op), ...], 'single': n} over the
    coverage child's records of every chunk in `run_dir`: operations in which
    at least two units of `symbol` were pending at a dispatch, split by
    whether every dispatch ran the FIFO head; `single` counts operations
    where never more than one was pending (which cannot distinguish)."""
    addresses = dict(zip(DISPATCH_SYMBOLS, dispatch_addresses(kernel)))
    func = addresses[symbol]
    ops = {}
    for path in glob.glob(os.path.join(run_dir, 'chunk-*', 'linux', 'hidden.jsonl')):
        for line in open(path):
            row = json.loads(line)
            if row['mode'] == 'pc':
                ops.setdefault((os.path.dirname(path), row['id'], row['index']), []).extend(row['records'])
    counts = {'fifo': 0, 'non_fifo': 0, 'non_fifo_ops': [], 'single': 0}
    for (_, trace, index), records in sorted(ops.items()):
        pending, saw_two, non_fifo, any_queue = [], False, False, False
        for kind, _, _, _, data in sorted(records, key=lambda r: r[2]):
            kind &= 0x7fff
            if kind not in (SECTION_START, QUEUE) or len(data) < 32:
                continue
            words = [int.from_bytes(bytes.fromhex(data[i:i + 16]), 'little') for i in (0, 16)]
            if kind == QUEUE and words[1] == func:
                pending.append(words[0])
                any_queue = True
            elif kind == SECTION_START and words[0] == func:
                unit = words[1]
                if len(pending) >= 2:
                    saw_two = True
                    if unit != pending[0]:
                        non_fifo = True
                if unit in pending:
                    pending.remove(unit)
        if not any_queue:
            continue
        if not saw_two:
            counts['single'] += 1
        elif non_fifo:
            counts['non_fifo'] += 1
            counts['non_fifo_ops'].append((trace, index))
        else:
            counts['fifo'] += 1
    return counts


if __name__ == '__main__':
    print(json.dumps(dispatch_orders(sys.argv[1]), indent=2))
