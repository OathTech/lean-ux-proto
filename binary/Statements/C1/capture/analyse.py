#!/usr/bin/env python3
"""C1 phase A: read one capture (capture_insertions.py) against the C1
statements, in the renderings that are not executable Lean, and write the
slim input for Check.lean.

What it reports, per trace:
- every service call: what changed in the WHOLE guest RAM across it, sorted
  into the clauses of `ServiceWrites` (stack scratch, coverage buffer, the
  slab page outside nodes that stay handed out) and everything else, named
  by ELF symbol; the stack depth used; which functions and which
  instructions outside the pinned semantics the guest executed inside it;
- the outcome of each allocation against the allocation records of the
  recorded run that the mirror consumes;
- across each wrapper call: what changed outside the stack window, the
  coverage buffer and the heap;
- between consecutive calls: what the caller changed in the heap.

The arena it proposes is the smallest one that makes `ServiceWrites` true of
this run: the slab pages of the nodes plus every other range a service
changed outside its scratch and the buffer. Check.lean then evaluates the
caller premises with that arena.

  scripts/in-bundle /usr/bin/python3 -B binary/Statements/C1/capture/analyse.py .tmp/c1/capture-<trace>
"""
import bisect
import re
import subprocess
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path[:0] = [str(ROOT / 'binary')]
from elftools.elf.elffile import ELFFile   # noqa: E402
from target import ORACLE                   # noqa: E402

PAGE = 4096
DIRECT, IMAGE = 0xffff888000000000, 0xffffffff80000000   # nokaslr; checked against the debugger's translations
NODE = 72
REFCOUNT, LIST = (1056, 4), (1096, 16)                    # wg_peer: refcount, allowedips_list (checked below)
SPECIAL = {b'\x9d': 'popf', b'\x9c': 'pushf', b'\xfa': 'cli', b'\xfb': 'sti', b'\x0f\x31': 'rdtsc',
           b'\x48\x0f\xc7': 'cmpxchg16b', b'\x0f\x18': 'prefetch', b'\xf3\x48\xab': 'rep stos',
           b'\xf3\x48\xa5': 'rep movs', b'\xf3\xa4': 'rep movsb', b'\xf3\xaa': 'rep stosb'}


def symbols():
    with ORACLE.open('rb') as stream:
        elf = ELFFile(stream)
        table = sorted((s['st_value'], s['st_size'], s.name) for s in elf.get_section_by_name('.symtab').iter_symbols()
                       if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_value'] >= IMAGE and s.name)
        sections = [(s['sh_addr'], s['sh_size'], s.name) for s in elf.iter_sections() if s['sh_addr'] >= IMAGE]
        text = [(s['sh_addr'], s.data()) for s in elf.iter_sections()
                if s['sh_flags'] & 4 and s['sh_type'] == 'SHT_PROGBITS']
    starts = [row[0] for row in table]

    def function(address):
        i = bisect.bisect_right(starts, address) - 1
        return (table[i][0], max(table[i][1], 1)) if i >= 0 and address < table[i][0] + max(table[i][1], 1) else None

    def name(address):
        i = bisect.bisect_right(starts, address) - 1
        if i >= 0 and (address < table[i][0] + max(table[i][1], 1) or address - table[i][0] < 0x1000 and table[i][1] == 0):
            offset = address - table[i][0]
            return table[i][2] + (f'+{offset:#x}' if offset else ''), table[i][2]
        for base, size, section in sections:
            if base <= address < base + size:
                return f'section {section}+{address - base:#x}', f'section {section}'
        return None, None

    def code(address, size=3):
        for base, data in text:
            if base <= address < base + len(data):
                return data[address - base:address - base + size]
        return b''
    return name, code, function


REGS = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi', 'rsp', 'rbp', 'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15']
OPERAND = re.compile(r'(-?0x[0-9a-f]+)?\((%\w+)?(?:,(%\w+))?(?:,(\d))?\)')
ABSOLUTE = re.compile(r'(?<![\w$(])0x(ffff[0-9a-f]{12})(?![\w(])')
_listing = {}


def disassemble(start, size):
    """objdump's text for one function of the pinned ELF: pc -> (mnemonic, operands, comment address)."""
    if start not in _listing:
        text = subprocess.run(['objdump', '-d', '--no-show-raw-insn', f'--start-address={start:#x}',
                               f'--stop-address={start + size:#x}', str(ORACLE)], capture_output=True, text=True, check=True).stdout
        rows = {}
        for line in text.splitlines():
            m = re.match(r'^([0-9a-f]{16}):\s+(\S+)\s*(.*)$', line)
            if m:
                body, _, comment = m[3].partition('#')
                target = re.match(r'\s*([0-9a-f]{16})', comment)
                rows[int(m[1], 16)] = (m[2], body.strip(), int(target[1], 16) if target else None)
        _listing[start] = rows
    return _listing[start]


def accesses(row, regs):
    """Addresses one instruction reads or writes, from the ELF's text and the
    registers before it. Read and write are not told apart. Approximate at
    the three boot-patched sites, which the caller handles."""
    mnemonic, body, comment = row
    value = dict(zip(REGS, regs))
    found = []
    if mnemonic in ('push', 'call'):
        found.append(value['rsp'] - 8)
    if mnemonic in ('pop', 'ret', 'popf', 'leave'):
        found.append(value['rbp'] if mnemonic == 'leave' else value['rsp'])
    if mnemonic == 'pushf':
        found.append(value['rsp'] - 8)
    if mnemonic == 'rep':
        found.append(value['rdi'])
        if 'movs' in body:
            found.append(value['rsi'])
        return found
    if mnemonic in ('lea', 'nop', 'nopw', 'nopl', 'prefetcht0', 'prefetchw', 'jmp', 'call') and '*' not in body:
        return found
    for m in OPERAND.finditer(body):
        displacement = int(m[1], 16) if m[1] else 0
        if m[2] == '%rip':
            if comment is not None:
                found.append(comment)
            continue
        base = value.get((m[2] or '%').lstrip('%'), 0) if m[2] else 0
        index = value.get(m[3].lstrip('%'), 0) if m[3] else 0
        found.append((base + index * int(m[4] or 1) + displacement) % 2**64)
    found += [int(m[1], 16) for m in ABSOLUTE.finditer(body)]
    return found


def main():
    out = Path(sys.argv[1]).resolve()
    capture = json.loads((out / 'capture.json').read_text())
    layout = json.loads((out / 'layouts.json').read_text())
    probe = json.loads((out / 'input.json').read_text())
    peer_layout = layout['wg_peer']
    if peer_layout['members']['allowedips_list'] != LIST[0] or probe['lookup']['offsets']['peerRefcount'] != REFCOUNT[0]:
        raise ValueError('peer offsets differ from the statement layout')
    name, code, function = symbols()

    def next_symbol_size(base):
        i = 1
        while name(base + i)[1] == name(base)[1]:
            i += 1
        return i
    to_virtual = {gpa: page for page, gpa in capture['translations'] if gpa is not None}
    for page, gpa in capture['translations']:
        if gpa is not None and page >= IMAGE and page - IMAGE != gpa or DIRECT <= page < DIRECT + 2**40 and page - DIRECT != gpa:
            raise ValueError('address-space constants differ from the debugger translation')
    sites = {address: 70 + site for address, site in probe['allocationReturns']}
    table = capture['calls'][0]['table']
    peers = [a for a, _ in capture['peers']]
    keys = [key for _, key in capture['peers']]
    records = [[site, list(bytes.fromhex(data))] for op in (capture['hidden'] or []) for site, data in op
               if site in (77, 78, 79)]
    report, arena_extra, all_nodes, depth, problems = [], [], [], 0, []
    lean_calls, lean_stop = [], False
    first_peers = capture.get('peersAtFirstCall') or len(capture['peers'])
    used_records = 0

    def virtual(physical):
        page = physical // PAGE * PAGE
        if page in to_virtual:
            return to_virtual[page] + physical % PAGE
        if physical >= 0x1000000 and name(IMAGE + physical)[0]:
            return IMAGE + physical
        return DIRECT + physical

    def classify(run, call, rsp, window, kept, objects):
        """One changed run -> (class, virtual address, length, description)."""
        physical, old, new = run
        n = len(old) // 2
        a = virtual(physical)
        area, capacity = call['coverage'], call['capacity']
        if rsp - window <= a and a + n <= rsp:
            return 'stack', a, n, f'rsp-{rsp - a}'
        if rsp - 16384 <= a < rsp + 16384:
            return 'stack-outside', a, n, f'rsp{a - rsp:+d} (outside the {window}-byte window)'
        if area and area <= a and a + n <= area + 8 * capacity:
            return 'coverage', a, n, f'area+{a - area}'
        for o in kept:
            if a < o + NODE and o < a + n:
                return 'kept-node', a, n, f'node {o:#x}+{a - o}'
        for o in objects:
            if a < o + NODE and o < a + n:
                return 'object', a, n, f'object {o:#x}+{a - o}'
        if table <= a < table + 24:
            return 'table', a, n, ['root4', 'root6', 'seq'][(a - table) // 8]
        for i, p in enumerate(peers):
            if p <= a < p + peer_layout['size']:
                field = 'refcount' if REFCOUNT[0] <= a - p < sum(REFCOUNT) else \
                    'allowedips_list' if LIST[0] <= a - p < sum(LIST) else f'+{a - p}'
                return ('peer-field' if not field.startswith('+') else 'peer-other'), a, n, f'peer {i} {field}'
        if any(a // PAGE == o // PAGE for o in all_nodes + objects):
            return 'slab-page', a, n, f'slab page {a // PAGE * PAGE:#x}+{a % PAGE}'
        if call['task'] <= a < call['task'] + 0x2000:
            return 'other', a, n, f'task_struct+{a - call["task"]:#x}'
        symbol = name(a)[0] if a >= IMAGE else None
        return 'other', a, n, symbol or f'direct map {a:#x}'

    for call in capture['calls']:
        entry = call['initial']['registers']
        row = dict(call=call['index'], family=call['family'], addr=call['want']['addr'], cidr=call['want']['cidr'],
                   pid=keys.index(call['want']['key']), eax=call['returned']['registers']['rax'] % 2**32, services=[])
        live = list(call['nodesBefore'])
        for service in call['services']:
            s_entry = service['initial']['registers']
            rsp = s_entry['rsp']
            kept = live if service['kind'] == 'alloc' else [o for o in live if o != s_entry['rsi']]
            objects = [service['allocation']] if service['kind'] == 'alloc' and service['allocation'] else \
                [s_entry['rsi']] if service['kind'] == 'free' else []
            all_nodes.extend(o for o in objects if o not in all_nodes)
            classes = [classify(run, call, rsp, 16384, kept, objects) for run in service['diff']]
            lowest = min([a for c, a, n, d in classes if c == 'stack'], default=rsp)
            used = max(rsp - lowest, rsp - service['lowestRsp'])
            depth = max(depth, used)
            functions = Counter(name(pc)[1] or f'{pc:#x}' for pc in service['pcs'])
            special = Counter()
            for pc in service['pcs']:
                raw = code(pc)
                for pattern, label in SPECIAL.items():
                    if raw.startswith(pattern):
                        special[label] += 1
            touched = Counter()
            above = 0
            for pc, regs in zip(service['pcs'], service.get('regs') or []):
                span = function(pc)
                insn = span and disassemble(*span).get(pc)
                if pc in (probe['alloc'] + 0x85, probe['free'] + 0xf4):   # boot-patched: cmpxchg16b (%rsi)
                    found = [regs[4], regs[4] + 8]
                elif insn is None:
                    touched['undecoded instruction'] += 1
                    continue
                else:
                    found = accesses(insn, regs)
                for a in found:
                    if rsp + 8 <= a < rsp + 16384:
                        above = max(above, a + 8 - rsp)
                        touched['stack above the return word (caller frames)'] += 1
                    elif rsp - 16384 <= a < rsp + 8:
                        touched['own stack and the return word'] += 1
                    elif call['coverage'] and call['coverage'] <= a < call['coverage'] + 8 * call['capacity']:
                        touched['coverage buffer'] += 1
                    elif call['task'] <= a < call['task'] + 0x2000:
                        touched[f'task_struct+{(a - call["task"]) // 8 * 8:#x}'] += 1
                    elif any(a // PAGE == o // PAGE for o in all_nodes + objects):
                        touched['slab page'] += 1
                    elif a >= IMAGE:
                        touched[name(a)[1] or f'image {a:#x}'] += 1
                    else:
                        touched['other direct-map or vmalloc address'] += 1
            other = [(a, n, d, run[1], run[2]) for (c, a, n, d), run in zip(classes, service['diff']) if c == 'other']
            for a, n, d, _, _ in other:
                arena_extra.append((a, n, d))
            bad = [(c, hex(a), n, d) for c, a, n, d in classes if c in ('kept-node', 'table', 'peer-field', 'peer-other', 'stack-outside')]
            item = dict(kind=service['kind'], returnSite=sites.get(service['returnPC'], service['returnPC']),
                        result=service['allocation'], steps=len(service['pcs']), stackDepth=used,
                        lowestRspDepth=rsp - service['lowestRsp'],
                        changedBytes={k: sum(n for c, a, n, d in classes if c == k) for k in sorted({c for c, *_ in classes})},
                        coverageWordsAppended=(service['returned']['registers'] and
                                               sum(n for c, a, n, d in classes if c == 'coverage')),
                        outsideScratchBufferAndSlab=[dict(address=hex(a), bytes=n, what=d, old=o, new=w) for a, n, d, o, w in other],
                        slabPageOutsideObject=[dict(address=hex(a), bytes=n, what=d) for c, a, n, d in classes if c == 'slab-page'],
                        violatesKeptOrHeap=bad, accessed=dict(touched.most_common()), highestAccessAboveEntryRsp=above, functions=dict(functions.most_common()), instructions=dict(special),
                        interruptFlagCleared=not service['flagsCleared'] & 0x200, directionFlagSet=bool(service['flagsSeen'] & 0x400))
            if service['kind'] == 'alloc':
                record = records[used_records] if used_records < len(records) else None
                used_records += 1
                item['mirrorRecord'] = record and dict(site=record[0], outcome=record[1][0])
                item['agreesWithRecord'] = bool(record and record[0] == item['returnSite'] and
                                                record[1][0] == (1 if service['allocation'] else 0))
                if not item['agreesWithRecord']:
                    problems.append(f'call {call["index"]}: allocation outcome differs from the recorded record')
            if bad:
                problems.append(f'call {call["index"]} {service["kind"]}: writes outside ServiceWrites: {bad}')
            live = service['nodesAfter']
            row['services'].append(item)
        window = 200 + depth
        classes = [classify(run, call, entry['rsp'], window, [], call['nodesAfter'] + call['nodesBefore']) for run in call['diff']]
        row['callChanged'] = {k: sum(n for c, a, n, d in classes if c == k) for k in sorted({c for c, *_ in classes})}
        row['callOutsideWindowBufferHeapBeforeArena'] = [dict(address=hex(a), bytes=n, what=d, cls=c)
                                                         for c, a, n, d in classes if c in ('other', 'stack-outside', 'peer-other')]
        row['steps'] = call['nativeSteps']
        row['coverageMode'] = call['mode']
        report.append(row)
        slim = lambda e, words: dict(registers=e['registers'], blocks=[
            dict(address=b['address'], bytes=b['bytes'][:8 * words] if b['address'] == call['coverage'] else b['bytes'])
            for b in e['blocks']])
        # room for the callbacks of the lookups Check.lean runs on the last checked call's final state
        words = call['coverageUsedAfter'] + 2048
        if row['pid'] >= first_peers:
            lean_stop = True   # a peer created between calls: outside the closed world; Lean checks stop here
        if not lean_stop:
          lean_calls.append(dict(family=call['family'], key=int(call['want']['addr'], 16), cidr=call['want']['cidr'],
                               pid=row['pid'], initial=slim(call['initial'], words), returned=slim(call['returned'], words),
                               services=[dict(kind=s['kind'], initial=slim(s['initial'], words),
                                              returned=slim(s['returned'], words), allocation=s['allocation'])
                                         for s in call['services']], executedPCs=call['executedPCs']))
    patched = {}
    for which, raw in (capture.get('serviceText') or {}).items():
        base, guest = probe[which], bytes.fromhex(raw)
        size = next_symbol_size(base)
        elf = code(base, size)
        patched[which] = [f'+{i:#x}: ELF {elf[i:i+1].hex()} guest {guest[i:i+1].hex()}' for i in range(len(elf)) if elf[i] != guest[i]]
    between = []
    for gap in capture['between']:
        call = capture['calls'][gap['before']]
        rsp = call['initial']['registers']['rsp']
        classes = [classify(run, call, rsp, 0, call['nodesBefore'], []) for run in gap['diff']]
        heap = [dict(address=hex(a), bytes=n, what=d, old=run[1], new=run[2]) for (c, a, n, d), run in zip(classes, gap['diff'])
                if c in ('kept-node', 'table', 'peer-field', 'slab-page') or
                (c == 'other' and any(x <= a < x + m for x, m, _ in arena_extra))]
        between.append(dict(beforeCall=gap['before'], changedBytes=sum(len(r[1]) // 2 for r in gap['diff']), heapChanged=heap))
    pages = sorted({o // PAGE * PAGE for o in all_nodes})
    arena = [(p, PAGE) for p in pages]
    for a, n, d in sorted(set(arena_extra)):
        if not any(x <= a and a + n <= x + m for x, m in arena):
            arena.append((a, n))
    lookups = [[c['family'], int(c['want']['addr'], 16)] for c in capture['calls'][:len(lean_calls)]]
    seen = []
    for item in lookups + [[4, 0x0b000001], [4, 0x0a010201], [6, 0xfe80 << 112]]:
        if item not in seen:
            seen.append(item)
    summary = dict(trace=capture['trace'], ended=capture['ended'], steer=capture['steer'], calls=report, between=between,
                   allocationRecordsOfTheRecordedRun=[(s, b[0]) for s, b in records], recordsConsumedByCapture=used_records,
                   depth=depth, leanCalls=len(lean_calls), arena=[(hex(a), n) for a, n in arena], guestTextDiffersFromElf=patched,
                   arenaBeyondSlabPages=sorted({(hex(a), n, d) for a, n, d in arena_extra}), problems=problems)
    (out / 'analysis.json').write_text(json.dumps(summary, indent=1) + '\n')
    (out / 'lean-input.json').write_text(json.dumps(dict(
        table=table, peers=peers[:first_peers], arena=arena, cache=capture['calls'][0]['cacheValue'], depth=(depth + 7) // 8 * 8,
        calls=lean_calls, lookups=seen, records=records)) + '\n')
    print(json.dumps(dict(trace=capture['trace'], calls=len(report), services=sum(len(r['services']) for r in report),
                          depth=depth, arena_spans=len(arena), problems=problems), indent=1))


if __name__ == '__main__':
    main()
