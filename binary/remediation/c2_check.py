#!/usr/bin/env python3
"""Check C2 count/register clauses and finite native frame observations.

Full physical RAM is compared against the physical image of the statement's
write footprint. Kernel image/direct-map aliases are separately checked for
counterexamples to its literal virtual-address EqualOutside predicate.
Neither a physical-frame pass nor absence of a found alias counterexample
admits the complete Lean statement. That distinction is in the output.
"""
import argparse
import json
from pathlib import Path

from c2_capture import ENTRY, DONE, REJECT, PREEMPT, WINDOW_OFFSET, WINDOW_BYTES, ELF_SHA256, IDENTITY
from c2_memory import DIRECT_MAP, IMAGE_BASE, changed_runs, images, read, translate


def in_footprint(kp, address):
    return kp + WINDOW_OFFSET <= address < kp + WINDOW_OFFSET + WINDOW_BYTES or PREEMPT <= address < PREEMPT + 4


def check_visit(row, before, after, image):
    kp, skb = row['kp'], row['skb']
    old_top, new_top = row['entry']['page_table_root'], row['exit']['page_table_root']
    if row['forced']:
        raise ValueError('forced visit is outside this native observation experiment')
    if row['entry']['regs']['rip'] != ENTRY or row['exit']['regs']['rip'] not in (DONE, REJECT):
        raise ValueError('visit has the wrong entry or exit cut')
    if row['entry']['regs']['rbx'] != kp or row['entry']['regs']['r15'] != skb:
        raise ValueError('entry pointer metadata differs from registers')
    for side, memory in [('entry', before), ('exit', after)]:
        top = row[side]['page_table_root']
        for field, address, size in [('window', kp + WINDOW_OFFSET, WINDOW_BYTES),
                                     ('nonce', skb + 0x28, 8), ('preempt', PREEMPT, 4)]:
            if read(memory, top, address, size).hex() != row[side][field]:
                raise ValueError(f'{side} {field} differs between debugger read and RAM snapshot')
        if read(memory, top, ENTRY, DONE - ENTRY).hex() != image['code']:
            raise ValueError('captured C2 code differs from the pinned ELF')
        alias = row[side]['count_alias']
        if read(memory, top, alias['address'], 4).hex() != alias['bytes']:
            raise ValueError('count alias differs between debugger read and RAM snapshot')
    addresses = list(range(kp + WINDOW_OFFSET, kp + WINDOW_OFFSET + WINDOW_BYTES)) + list(range(PREEMPT, PREEMPT + 4))
    permitted = set()
    for address in addresses:
        old, new = translate(before, old_top, address), translate(after, new_top, address)
        if old != new:
            raise ValueError('write-footprint translation changed during the visit')
        permitted.add(old)
    runs = list(changed_runs(before, after))
    outside = []
    alias = []
    alias_errors = []
    image_lo = image['symbols']['_text'] - IMAGE_BASE
    image_hi = image['symbols']['_end'] - IMAGE_BASE
    for address, length in runs:
        forbidden = [a for a in range(address, address + length) if a not in permitted]
        if forbidden:
            outside.append(dict(physical=hex(forbidden[0]), bytes=len(forbidden)))
        # One verified changed virtual byte suffices to refute EqualOutside.
        # Retain several locations for diagnosis, not an unbounded evidence log.
        if len(alias) >= 8:
            continue
        for physical in range(address, address + length):
            candidates = [DIRECT_MAP + physical]
            if image_lo <= physical < image_hi:
                candidates.append(IMAGE_BASE + physical)
            for virtual in candidates:
                if in_footprint(kp, virtual):
                    continue
                try:
                    old_at, new_at = translate(before, old_top, virtual), translate(after, new_top, virtual)
                    old_byte, new_byte = read(before, old_top, virtual, 1), read(after, new_top, virtual, 1)
                except ValueError as error:
                    if len(alias_errors) < 8:
                        alias_errors.append(dict(address=hex(virtual), error=str(error)))
                    continue
                if old_at == physical == new_at and old_byte != new_byte:
                    alias.append(dict(virtual=hex(virtual), physical=hex(physical),
                                      before=old_byte.hex(), after=new_byte.hex(),
                                      allowed_physical_alias=physical in permitted))
                    break
            if len(alias) >= 8:
                break
    preempt = int.from_bytes(bytes.fromhex(row['entry']['preempt']), 'little')
    actual = int.from_bytes(bytes.fromhex(row['exit']['preempt']), 'little')
    expected = (preempt + 0x200) % 2**32
    count = dict(status='pass' if actual == expected else 'fail',
                 before=hex(preempt), expected=hex(expected), actual=hex(actual))
    changed_registers = [name for name in ('rsp', 'r15', 'r12', 'rbx')
                         if row['entry']['regs'][name] != row['exit']['regs'][name]]
    bad_unlock = row['exit']['regs']['rip'] == DONE and row['exit']['regs']['rsi'] % 2**32 != 0x200
    return dict(visit=row['visit'], count=count,
                registers=dict(status='fail' if changed_registers or bad_unlock else 'pass',
                               changed=changed_registers, bad_unlock_argument=bad_unlock),
                physical_frame=dict(status='fail' if outside else 'pass',
                                    changed_bytes=sum(n for _, n in runs),
                                    outside_bytes=sum(r['bytes'] for r in outside),
                                    examples=outside[:8]),
                native_virtual_frame=dict(status='fail' if alias else 'unresolved',
                                          counterexamples=alias, unobserved_aliases=alias_errors))


def check(capture):
    capture = Path(capture)
    metadata = json.loads((capture / 'metadata.json').read_text())
    summary = json.loads((capture / 'summary.json').read_text())
    if metadata['schema'] != 'c2-native-frame-v2' or metadata['forced']:
        raise ValueError('unsupported or forced capture')
    image = metadata['image']
    if image['elf_sha256'] != ELF_SHA256 or image['identity'] != IDENTITY:
        raise ValueError('capture uses a different image')
    rows = [json.loads(line) for line in (capture / 'visits.jsonl').read_text().splitlines()]
    if not rows or len(rows) != summary['visits'] or summary['snapshots'] != 2 * len(rows):
        raise ValueError('missing visits or snapshots')
    stream = iter(images(capture / 'ram', metadata['ram_bytes'], summary['snapshots']))
    reports = []
    for i, row in enumerate(rows):
        if row['visit'] != i or row['entry']['snapshot'] != 2 * i or row['exit']['snapshot'] != 2 * i + 1:
            raise ValueError('nonconsecutive visit/snapshot indices')
        reports.append(check_visit(row, next(stream), next(stream), image))
    failures = {field: sum(row[field]['status'] == 'fail' for row in reports)
                for field in ('count', 'registers', 'physical_frame', 'native_virtual_frame')}
    return dict(status='fail' if any(failures.values()) else 'incomplete', mode=metadata['mode'],
                visits=len(reports), failures=failures, all_clauses_admitted=False,
                claim_scope='individual visits; physical frame is a projection, not EqualOutside',
                unchecked=['source refinement', 'complete instruction semantics',
                           'all virtual aliases and non-RAM domains', 'allocation lifetime and hand-overs'],
                visits_detail=reports)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    args = parser.parse_args()
    report = check(args.capture)
    print(json.dumps(report))
    return 1 if report['status'] == 'fail' else 2


if __name__ == '__main__':
    raise SystemExit(main())
