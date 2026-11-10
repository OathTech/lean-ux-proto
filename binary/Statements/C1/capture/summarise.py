#!/usr/bin/env python3
"""C1 phase A: one page of counts from the per-trace outputs of analyse.py
(analysis.json) and Check.lean (lean-check.jsonl, lean-full-entry.jsonl).

  scripts/in-bundle /usr/bin/python3 -B binary/Statements/C1/capture/summarise.py .tmp/c1/capture-*
"""
from collections import Counter
import json
from pathlib import Path
import sys


def tally(counter, label, verdict):
    counter[(label, 'ok' if str(verdict).startswith('ok') else str(verdict))] += 1


def main():
    entry, service, ret, lookups, other, classes, frame = (Counter() for _ in range(7))
    depths, paths, instructions, between, cases, patched, problems = [], Counter(), Counter(), [], [], {}, []
    accessed, above = Counter(), []
    closed, covered = [], Counter()
    for directory in map(Path, sys.argv[1:]):
        analysis = json.loads((directory / 'analysis.json').read_text())
        trace = analysis['trace']
        problems += [f'{trace}: {p}' for p in analysis['problems']]
        patched.update({f'{trace} {k}': v for k, v in analysis['guestTextDiffersFromElf'].items()})
        for call in analysis['calls']:
            shape = [(s['kind'], s['returnSite'], bool(s['result'])) for s in call['services']]
            cases.append((trace, call['call'], f"v{call['family']} {call['addr'][:8]}/{call['cidr']} peer {call['pid']}",
                          ' '.join(f"{k}@{site}:{'obj' if ok else ('NULL' if k == 'alloc' else '-')}" for k, site, ok in shape) or 'no service call',
                          call['eax'] - 2**32 if call['eax'] >= 2**31 else call['eax'], call['steps']))
            for s in call['services']:
                depths.append(s['stackDepth'])
                slow = [f for f in ('___slab_alloc', '__slab_free', 'allocate_slab', '__alloc_pages_noprof') if f in s['functions']]
                paths[(s['kind'], 'slow path: ' + '+'.join(slow) if slow else
                       'forced NULL by the pre-hook' if s['kind'] == 'alloc' and not s['result'] else 'fast path')] += 1
                for name, count in s['instructions'].items():
                    instructions[name] += count
                for name in ('this_cpu_cmpxchg16b_emu', 'stack_trace_save', 'unwind_next_frame', '__kcov_alloc_pre', '__kcov_alloc_post'):
                    if name in s['functions']:
                        instructions['calls into ' + name] += 1
                for k, n in s.get('accessed', {}).items():
                    accessed[k if not k.startswith('task_struct') else 'task_struct'] += n
                above.append(s.get('highestAccessAboveEntryRsp', 0))
                for k, n in s['changedBytes'].items():
                    classes[(s['kind'], k)] += n
                for item in s['outsideScratchBufferAndSlab']:
                    other[(s['kind'], item['what'].split('+')[0] if not item['what'].startswith('direct map') else 'direct map (slab and page-allocator metadata)')] += 1
                if s['kind'] == 'alloc':
                    tally(service, 'python: outcome and site equal the recorded run\'s next allocation record', 'ok' if s['agreesWithRecord'] else 'DIFFERS')
                tally(service, 'python: no change in a kept node, the table, a peer or above the return word (whole RAM)',
                      'ok' if not s['violatesKeptOrHeap'] else 'VIOLATED')
        for call in analysis['calls']:
            stray = [x for x in call['callOutsideWindowBufferHeapBeforeArena'] if x['cls'] != 'other']
            tally(frame, 'python: whole RAM across the call changed only in the stack window, the buffer, the table, '
                  'peer fields, nodes, the slab page and the words the services changed', 'ok' if not stray else f'STRAY {stray}')
        # the closed world over the whole RAM: revision 2 admits no heap change between calls; revision 3
        # also a registered peer's count up by one (peerGetMaybeZero returning the peer) or down by one from above one (peerPut)
        def paired(h):
            if not (h['what'].startswith('peer ') and h['what'].endswith(' refcount') and h['bytes'] == 1):
                return False
            old, new = int(h['old'], 16), int(h['new'], 16)
            return (new == old + 1 and old >= 1) or (new == old - 1 and old > 1)
        first2 = first3 = len(analysis['calls'])
        for gap in analysis['between']:
            if gap['heapChanged']:
                between.append((trace, gap['beforeCall'], [(h['what'], h['old'], h['new']) for h in gap['heapChanged']]))
                first2 = min(first2, gap['beforeCall'])
                if not all(paired(h) for h in gap['heapChanged']):
                    first3 = min(first3, gap['beforeCall'])
        closed.append((trace, len(analysis['calls']), first2, first3))
        for line in (directory / 'lean-check.jsonl').read_text().splitlines():
            row = json.loads(line)
            if 'insertion' in row and row['seed'] == 0 and 'ABORTED' not in row['insertion']:
                for revision in (2, 3):
                    if row['insertion'].get(f'covered by the headline from the empty table, revision {revision}'):
                        covered[(trace, revision)] += 1
        full = directory / 'lean-full-entry.jsonl'
        if full.exists():
            for line in full.read_text().splitlines():
                for k, v in json.loads(line)['fullEntry'].items():
                    if k in ('emptyTable', 'insertReady'):
                        tally(entry, f'verbatim, whole 32 MiB buffer loaded, first call: {k}', v)
        for line in (directory / 'lean-check.jsonl').read_text().splitlines():
            row = json.loads(line)
            if 'lookup' in row:
                for k, v in row['lookup'].items():
                    if k in ('lookupReady (captured window)', 'Returned', "rax is the mirror's peer", 'ABORTED'):
                        tally(lookups, k, v)
                continue
            call = row['insertion']
            if 'ABORTED' in call:
                problems.append(f'{trace} call {call["call"]} seed {row["seed"]}: {call["ABORTED"]}')
                continue
            for k, v in call.items():
                if k in ('emptyTable', 'insertReady (captured window)', 'c1.stack-peers (revision 4): the stack window apart from every peer object',
                         'whole buffer apart from the heap, the caller\'s spans and the coverage metadata'):
                    tally(entry, k, v)
                elif isinstance(v, str) and k not in ('key',):
                    tally(ret, k, v)
            for s in call['services']:
                for k, v in s.items():
                    if isinstance(v, str) and k != 'kind':
                        tally(service, f"{s['kind']}: {k}", v)
    print('CALLS (trace, call, arguments, service calls, eax, native steps)')
    for row in cases:
        print('  ', *row, sep=' | ')
    for title, counter in (('WRAPPER ENTRY (each check counted once per call and seed)', entry),
                           ('SERVICE CALLS', service), ('WRAPPER RETURN', ret), ('WRAPPER FRAME (once per call)', frame), ('LOOKUPS AFTERWARDS', lookups)):
        print(title)
        for (label, verdict), n in sorted(counter.items()):
            print(f'   {n:4d}  {label}: {verdict}')
    print('SERVICE PATHS', dict(paths))
    print('STACK DEPTH below the service entry rsp: min', min(depths), 'max', max(depths))
    print('INSTRUCTIONS AND CALLS inside services', dict(instructions))
    print('BYTES CHANGED across service calls, by class (whole RAM)', {f'{k[0]} {k[1]}': n for k, n in sorted(classes.items())})
    print('CHANGED OUTSIDE scratch, buffer and slab page (service calls that changed it)')
    for (kind, what), n in sorted(other.items()):
        print(f'   {n:4d}  {kind}: {what}')
    print('ADDRESSES ACCESSED by service instructions (read or written; instruction operands, all service calls)',
          dict(accessed.most_common()))
    print('HIGHEST ACCESS ABOVE the service entry rsp (bytes): min', min(above), 'max', max(above))
    print('GUEST TEXT differing from the ELF at the service functions', patched)
    print('HEAP WORDS CHANGED BY THE CALLER between calls', between)
    print('CLOSED WORLD: calls from the empty table inside it (whole RAM between calls; Check.lean on the captured states)')
    for trace, calls, first2, first3 in closed:
        print(f'   {trace}: {calls} calls; revision 2: {first2} (Lean: {covered[(trace, 2)]}); '
              f'revision 3: {first3} (Lean: {covered[(trace, 3)]})')
    print('PROBLEMS', problems)


if __name__ == '__main__':
    main()
