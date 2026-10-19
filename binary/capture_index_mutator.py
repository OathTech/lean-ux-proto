#!/usr/bin/env python3
"""Capture actual sequential index mutator entry/return bytes, read-only.

Use an existing successful recording for the selected anchor. Caller roots
include unlinked arguments and peers already removed from device membership.
The complete actual KCOV allocation is captured for the proved readiness
assertion. Run under capped with the project bundle environment.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from capture_lookup import Remote, slot, capture
from census import ROOT, ORACLE
from layouts import layouts
from pin import verify_pin
from generate_random_layout import layout_values


def random_private(remote, task, layout):
    """Capture the initialized provider and selected recording graph as-is."""
    blocks, nodes = {}, []

    def block(address, size):
        if not 0 < size or not 0 < address or address+size > 2**64:
            raise ValueError('invalid private capture allocation')
        blocks[address, size] = remote.read(address, size)

    for name, size in [('readyAddress', 4), ('cacheAddress', 108),
                       ('cpuAddress', 40), ('baseAddress', 40), ('sequenceAddress', 8)]:
        block(layout[name], size)
    ready = remote.word(layout['readyAddress'], 4)
    if not 0 < ready < 2**31:
        block(layout['initAddress'], 4)
    for offset in [layout['taskObject'], layout['taskHandle']]:
        block(task+offset, 8)
    block(task+layout['taskDropped'], 4)
    obj = remote.word(task+layout['taskObject'])
    selected, direct = 0, False
    if obj:
        block(obj, layout['objectSteer']+8)
        selected = remote.word(obj+layout['objectSteer'])
        direct = remote.word(obj+layout['objectRemote'], 1) != 0 or selected != 0
    if not direct:
        handle = remote.word(task+layout['taskHandle'])
        if handle:
            slot = layout['remoteMapAddress']+8*((handle*0x61c8864680b583eb % 2**64)//2**60)
            block(slot, 8)
            link = remote.word(slot)
            while link:
                base = link-layout['remoteLink']
                if base <= 0 or base in nodes or len(nodes) >= 256:
                    raise ValueError('cyclic or oversized captured remote bucket')
                nodes.append(base)
                block(base, layout['remoteLink']+16)
                if remote.word(base+layout['remoteHandle']) == handle:
                    obj = remote.word(base+layout['remoteObject'])
                    block(obj, layout['objectSteer']+8)
                    selected = remote.word(obj+layout['objectSteer'])
                    break
                link = remote.word(base+layout['remoteLink'])
    if selected:
        count = remote.word(selected+layout['steerCount'], 4)
        if count > 64:
            raise ValueError('oversized captured steering table')
        block(selected, layout['steerEntries']+count*layout['entrySize'])
    return dict(blocks=[dict(address=a, bytes=list(data)) for (a, _), data in sorted(blocks.items())],
                remoteNodes=nodes)


def completed_operations(path, trace):
    completed = []
    for line in path.read_text().splitlines():
        if line.startswith('LEANUX_COVERAGE '):
            row = json.loads(line.split(' ', 1)[1])
            if row['id'] != trace:
                raise ValueError('capture requires an isolated trace')
            completed.append(row['index'])
    if completed != list(range(len(completed))):
        raise ValueError('noncontiguous completed operation prefix')
    return completed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--anchor', choices=['remove', 'replace', 'insert'], required=True)
    parser.add_argument('--call-index', type=int, default=0,
                        help='zero-based selected call within the operation (insert only)')
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True)
    parser.add_argument('--operation', type=int, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=240)
    parser.add_argument('--instruction-budget', type=int, default=10000)
    args = parser.parse_args()
    if not 0 < args.instruction_budget <= 1000000:
        raise ValueError('invalid instruction budget')
    if args.call_index < 0 or (args.anchor != 'insert' and args.call_index):
        raise ValueError('call-index is nonnegative and only supported for insertion')
    probe = json.loads(args.input.read_text())
    check, out = args.check.resolve(), args.out.resolve()
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('capture requires a passing isolated differential recording')
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                         cwd=ROOT, text=True).strip()).parent
    sys.path.insert(0, str(ROOT))
    from harness.linux import verify_kernel
    from target import pins, verify_image
    verify_image()
    identity, kraken = verify_kernel(ORACLE.parent, expected=pins()[0]), verify_pin(ROOT)
    layout = layouts(ORACLE)
    provider_layout = layout_values() if args.anchor == 'insert' else None
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'snapshot.json').exists() or (out / 'gdb.sock').exists():
        raise ValueError('capture output is already occupied')
    command = json.loads((check / 'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel')+1]).resolve() != ORACLE.parent / 'arch/x86/boot/bzImage':
        raise ValueError('recorded QEMU command names another kernel')
    entry = probe['instructions'][0]['pc']
    expected = {'remove': 0xffffffff813a0400, 'replace': 0xffffffff813a0350,
                'insert': 0xffffffff813a01a0}[args.anchor]
    if entry != expected:
        raise ValueError('input anchor mismatch')
    endpoint, boot = out / 'gdb.sock', out / 'boot.log'
    command += ['-S', '-chardev', f'socket,path={endpoint},server=on,wait=off,id=pairgdb', '-gdb', 'chardev:pairgdb']
    with slot(shared), boot.open('wb') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log, stderr=log)
        remote = None
        try:
            deadline = time.monotonic() + 10
            while not endpoint.exists():
                if process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('QEMU debugger did not start; inspect boot.log')
                time.sleep(0.02)
            remote = Remote(endpoint, args.timeout)
            remote.breakpoint(entry)
            selected = 0
            for occurrence in range(256):
                regs = remote.resume()
                if regs['rip'] != entry:
                    raise ValueError('unexpected stop while selecting invocation')
                completed = completed_operations(boot, probe['trace']['id'])
                if len(completed) > args.operation:
                    raise ValueError('selected operation passed without the requested linked mutator')
                if len(completed) == args.operation:
                    previous = remote.word(regs['rsi']+probe['offsets']['hash']+probe['offsets']['pprev'])
                    if args.anchor == 'insert' and selected == args.call_index:
                        break
                    if args.anchor != 'insert' and previous:
                        break
                    selected += 1
                remote.breakpoint(entry, False)
                remote.resume(step=True)
                remote.breakpoint(entry)
            else:
                raise ValueError('selected mutator never occurred')
            roots = [regs['rsi']] + ([regs['rdx']] if args.anchor == 'replace' else [])
            print(f'capturing {args.anchor} entry, occurrence {occurrence}, completed {completed}', flush=True)
            initial = capture(remote, regs, probe, layout, args.instruction_budget,
                              root_entries=roots, read_output=False, include_retired=True, full_coverage=True)
            if provider_layout is not None:
                private = random_private(remote, initial['task'], provider_layout)
                initial['randomPrivate'] = dict(blocks=[(b['address'], len(b['bytes'])) for b in private['blocks']],
                                                remoteNodes=private['remoteNodes'])
                initial['blocks'] += private['blocks']
            print(f'captured {sum(len(b["bytes"]) for b in initial["blocks"])} entry bytes', flush=True)
            return_pc = remote.word(regs['rsp'])
            remote.breakpoint(entry, False)
            if int(remote.command('qqemu.sstep'), 16) != 7:
                raise ValueError('QEMU stepping must defer IRQs/timers for the sequential experiment')
            executed, returned = [], regs
            random_services, random_entry = [], None
            def read_blocks():
                return [dict(address=b['address'], bytes=list(remote.read(b['address'], len(b['bytes']))))
                        for b in initial['blocks']]
            for _ in range(args.instruction_budget):
                if args.anchor == 'insert' and returned['rip'] == 0xffffffff81375000:
                    if random_entry is not None:
                        raise ValueError('nested random service')
                    random_entry = dict(registers=returned, blocks=read_blocks())
                    random_start = len(executed)
                    random_return = remote.word(returned['rsp'])
                executed.append(returned['rip'])
                returned = remote.resume(step=True)
                if random_entry is not None and returned['rip'] == random_return:
                    if random_return != entry+0x79 or returned['rsp'] != random_entry['registers']['rsp']+8:
                        raise ValueError('random service returned to the wrong boundary')
                    random_services.append(dict(initial=random_entry,
                        returned=dict(registers=returned, blocks=read_blocks()),
                        executedPCs=executed[random_start:]))
                    random_entry = None
                if returned['rip'] == return_pc:
                    break
            else:
                raise ValueError('capture instruction budget exhausted')
            if returned['rsp'] != regs['rsp']+8:
                raise ValueError('return stack mismatch')
            if random_entry is not None or (args.anchor == 'insert' and not random_services):
                raise ValueError('incomplete or missing random service capture')
            for name in ['rbx', 'rbp', 'r12', 'r13', 'r14', 'r15']:
                if returned[name] != regs[name]:
                    raise ValueError(f'callee-saved register changed: {name}')
            final_blocks = read_blocks()
            result = dict(origin='actual stopped QEMU mutator; unmodified bytes and registers', anchor=args.anchor,
                          kernel=identity, image_sha256=hashlib.sha256(ORACLE.read_bytes()).hexdigest(), kraken=kraken,
                          trace=probe['trace']['id'], operation=args.operation, instructionBudget=args.instruction_budget,
                          executionMode='sequential', executedPCs=executed, completedOperations=completed,
                          occurrence=occurrence, initial=initial, returned=dict(registers=returned, blocks=final_blocks),
                          randomServices=random_services)
        finally:
            if remote:
                remote.socket.close()
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                    raise RuntimeError('owned QEMU cleanup timed out; capture failed')
            endpoint.unlink(missing_ok=True)
    (out / 'snapshot.json').write_text(json.dumps(result) + '\n')
    (out / 'layouts.json').write_text(json.dumps(layout) + '\n')
    print(json.dumps(dict(status='captured', anchor=args.anchor, instructions=len(executed),
                          peers=len(initial['peers']), keypairs=len(initial['keypairs']),
                          retained_peers=len(initial['retainedPeers']))), flush=True)


if __name__ == '__main__':
    main()
