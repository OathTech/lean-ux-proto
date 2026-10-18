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
    parser.add_argument('--anchor', choices=['remove', 'replace'], required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True)
    parser.add_argument('--operation', type=int, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=240)
    parser.add_argument('--instruction-budget', type=int, default=10000)
    args = parser.parse_args()
    if not 0 < args.instruction_budget <= 1000000:
        raise ValueError('invalid instruction budget')
    probe = json.loads(args.input.read_text())
    check, out = args.check.resolve(), args.out.resolve()
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('capture requires a passing isolated differential recording')
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                         cwd=ROOT, text=True).strip()).parent
    sys.path.insert(0, str(ROOT))
    from harness.linux import verify_kernel
    identity, kraken = verify_kernel(ORACLE.parent), verify_pin(ROOT)
    layout = layouts(ORACLE)
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'snapshot.json').exists() or (out / 'gdb.sock').exists():
        raise ValueError('capture output is already occupied')
    command = json.loads((check / 'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel')+1]).resolve() != ORACLE.parent / 'arch/x86/boot/bzImage':
        raise ValueError('recorded QEMU command names another kernel')
    entry = probe['instructions'][0]['pc']
    expected = {'remove': 0xffffffff813a0400, 'replace': 0xffffffff813a0350}[args.anchor]
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
            for occurrence in range(256):
                regs = remote.resume()
                if regs['rip'] != entry:
                    raise ValueError('unexpected stop while selecting invocation')
                completed = completed_operations(boot, probe['trace']['id'])
                if len(completed) > args.operation:
                    raise ValueError('selected operation passed without the requested linked mutator')
                if len(completed) == args.operation:
                    previous = remote.word(regs['rsi']+probe['offsets']['hash']+probe['offsets']['pprev'])
                    if previous:
                        break
                remote.breakpoint(entry, False)
                remote.resume(step=True)
                remote.breakpoint(entry)
            else:
                raise ValueError('selected mutator never occurred')
            roots = [regs['rsi']] + ([regs['rdx']] if args.anchor == 'replace' else [])
            print(f'capturing {args.anchor} entry, occurrence {occurrence}, completed {completed}', flush=True)
            initial = capture(remote, regs, probe, layout, args.instruction_budget,
                              root_entries=roots, read_output=False, include_retired=True, full_coverage=True)
            print(f'captured {sum(len(b["bytes"]) for b in initial["blocks"])} entry bytes', flush=True)
            return_pc = remote.word(regs['rsp'])
            remote.breakpoint(entry, False)
            if int(remote.command('qqemu.sstep'), 16) != 7:
                raise ValueError('QEMU stepping must defer IRQs/timers for the sequential experiment')
            executed, returned = [], regs
            for _ in range(args.instruction_budget):
                executed.append(returned['rip'])
                returned = remote.resume(step=True)
                if returned['rip'] == return_pc:
                    break
            else:
                raise ValueError('capture instruction budget exhausted')
            if returned['rsp'] != regs['rsp']+8:
                raise ValueError('return stack mismatch')
            for name in ['rbx', 'rbp', 'r12', 'r13', 'r14', 'r15']:
                if returned[name] != regs[name]:
                    raise ValueError(f'callee-saved register changed: {name}')
            final_blocks = [dict(address=b['address'], bytes=list(remote.read(b['address'], len(b['bytes']))))
                            for b in initial['blocks']]
            result = dict(origin='actual stopped QEMU mutator; unmodified bytes and registers', anchor=args.anchor,
                          kernel=identity, image_sha256=hashlib.sha256(ORACLE.read_bytes()).hexdigest(), kraken=kraken,
                          trace=probe['trace']['id'], operation=args.operation, instructionBudget=args.instruction_budget,
                          executionMode='sequential', executedPCs=executed, completedOperations=completed,
                          occurrence=occurrence, initial=initial, returned=dict(registers=returned, blocks=final_blocks))
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
