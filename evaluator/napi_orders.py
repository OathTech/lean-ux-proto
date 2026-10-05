"""Where the decrypt worker's NAPI poll ran, per received data message, in a
check run's Linux choice records (docs/2026-10-04-d2-data-plane.md, section
5): order (a), a NET_RX section right after the decrypt worker's resched
record (ksoftirqd took the softirq at the worker's cond_resched), or order
(b/c), a NET_RX section inside the decrypt worker's section without one
(the softirq ran inline at the next bh-enable or at an interrupt exit).

The scheduling control D2-M12 is rejected only by a (b/c) placement, so a
mutant run with none is inconclusive. Usage:

    scripts/in-bundle python3 -m evaluator.napi_orders RUN_DIR
"""
import glob
import json
import os
import sys

from harness.linux import DISPATCH_SYMBOLS, dispatch_addresses

SECTION_START, SECTION_STOP, RESCHED = 300, 301, 302


def napi_orders(run_dir, kernel=None):
    """{'a': n, 'bc': n, 'bc_ops': [(trace, op), ...]} over the coverage
    child's records of every chunk in `run_dir`."""
    addresses = dict(zip(DISPATCH_SYMBOLS, dispatch_addresses(kernel)))
    decrypt, netrx = addresses['wg_packet_decrypt_worker'], addresses['net_rx_action']
    ops = {}
    for path in glob.glob(os.path.join(run_dir, 'chunk-*', 'linux', 'hidden.jsonl')):
        for line in open(path):
            row = json.loads(line)
            if row['mode'] == 'pc':
                ops.setdefault((os.path.dirname(path), row['id'], row['index']), []).extend(row['records'])
    counts = {'a': 0, 'bc': 0, 'bc_ops': []}
    for (_, trace, index), records in sorted(ops.items()):
        # open sections in sequence order (a stop names no function: it
        # closes the innermost open one), and the previous record's kind
        open_, previous = [], None
        for kind, _, _, _, data in sorted(records, key=lambda r: r[2]):
            kind &= 0x7fff
            if kind == SECTION_START:
                func = int.from_bytes(bytes.fromhex(data), 'little')
                if func == netrx and decrypt in open_:
                    if previous == RESCHED:
                        counts['a'] += 1
                    else:
                        counts['bc'] += 1
                        counts['bc_ops'].append((trace, index))
                open_.append(func)
            elif kind == SECTION_STOP and open_:
                open_.pop()
            previous = kind
    return counts


if __name__ == '__main__':
    print(json.dumps(napi_orders(sys.argv[1]), indent=1))
