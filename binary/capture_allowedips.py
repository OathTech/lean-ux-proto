#!/usr/bin/env python3
"""Capture a sequential allowed-IPs call from QEMU without changing guest bytes.

The complete KCOV allocation is read because the current proved callback
readiness assertion requires it. Headers/return capture only a bounded prefix.
All output is ephemeral. Run through capped.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

from capture_lookup import Remote, slot
from census import ROOT, ORACLE
from layouts import layouts
from pin import verify_pin


def capture(remote, regs, probe, layout, budget):
    blocks, nodes, peers = {}, set(), set()

    def block(address, size):
        data = remote.read(address, size)
        for (previous, length), content in blocks.items():
            lo, hi = max(address, previous), min(address+size, previous+length)
            if lo < hi and data[lo-address:hi-address] != content[lo-previous:hi-previous]:
                raise ValueError('overlapping snapshot reads disagree')
        blocks[address, size] = data
        return data

    def walk(root):
        todo = [root] if root else []
        while todo:
            address = todo.pop()
            if address in nodes or len(nodes) >= 256:
                raise ValueError('cyclic, shared or oversized captured trie')
            nodes.add(address)
            block(address, probe['offsets']['nodeSize'])
            peer = remote.word(address+probe['offsets']['peer'])
            if peer:
                peers.add(peer)
            todo.extend(child for bit in range(2)
                        if (child := remote.word(address+probe['offsets']['children']+8*bit)))

    walk(regs['rdi'])
    if not peers:
        raise ValueError('pilot cannot discover device without a trie peer')
    peer_layout = layout['wg_peer']
    devices = {remote.word(p+peer_layout['members']['device']) for p in peers}
    if len(devices) != 1:
        raise ValueError('trie peers disagree on device')
    device, = devices
    block(device, layout['wg_device']['size'])
    roots_base = device+layout['wg_device']['members']['peer_allowedips']
    roots = [remote.word(roots_base+layout['allowedips']['members'][field])
             for field in ('root4', 'root6')]
    family = regs['rsi']
    if family not in (32, 128) or roots[0 if family == 32 else 1] != regs['rdi']:
        raise ValueError('ABI root/family differs from device roots')
    other = roots[1 if family == 32 else 0]
    walk(other)
    head = device+layout['wg_device']['members']['peer_list']
    cursor, members = remote.word(head), set()
    while cursor != head:
        p = cursor-peer_layout['members']['peer_list']
        if p in members or len(members) >= 256:
            raise ValueError('cyclic or oversized captured peer list')
        members.add(p)
        cursor = remote.word(cursor)
    if not peers <= members:
        raise ValueError('trie peer outside device membership')
    peer_rows = []
    for p in sorted(members):
        data = block(p, peer_layout['size'])
        key = peer_layout['members']['handshake']+layout['noise_handshake']['members']['remote_static']
        peer_rows.append(dict(address=p, publicKey=list(data[key:key+32])))
    block(regs['rsp']-2048, 2064)
    block(regs['rdx'], family//8)
    pcpu = probe['preempt']-layout['pcpu_hot']['members']['preempt_count']
    block(pcpu, layout['pcpu_hot']['size'])
    task = remote.word(pcpu+layout['pcpu_hot']['members']['current_task'])
    for offset, size in ((0x6e0, 4), (0x6e4, 4), (0x6e8, 8), (0x704, 4)):
        block(task+offset, size)
    if remote.word(task+0x6e0, 4) != 2:
        raise ValueError('capture requires KCOV_TRACE_PC mode')
    capacity, area = remote.word(task+0x6e4, 4), remote.word(task+0x6e8)
    if not area or not 1 < capacity <= 2**26:
        raise ValueError('unsupported captured coverage buffer')
    used = remote.word(area)
    if used >= capacity:
        raise ValueError('coverage count exceeds allocation')
    # Read every byte, including unused words, never fabricate mapped zeros.
    print(f'reading full callback allocation: {capacity*8} bytes', flush=True)
    block(area, capacity*8)
    extent = min(capacity, used+1+budget)*8
    observed = [(a, extent if a == area else size) for a, size in sorted(blocks)]
    return dict(registers=regs, peers=peer_rows, keypairs=[], device=device,
                nodes=sorted(nodes), root4=roots[0], root6=roots[1], task=task,
                coverage=area, capacity=capacity, coverageUsed=used,
                coverageCapturedWords=capacity,
                blocks=[dict(address=a, bytes=list(data)) for (a, _), data in sorted(blocks.items()) if a != area]), observed, blocks[area,capacity*8]


def endpoint(remote, regs, spans):
    return dict(registers=regs, blocks=[dict(address=a, bytes=list(remote.read(a, size))) for a, size in spans])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--instruction-budget', type=int, default=100000)
    args = parser.parse_args()
    if not 0 < args.instruction_budget <= 1000000:
        raise ValueError('invalid instruction budget')
    started = time.monotonic()
    probe, layout = json.loads(args.input.read_text()), layouts(ORACLE)
    packet = probe['trace']['ops'][probe['operation']]['packet']
    width, query = (32 if packet['family'] == 4 else 128), bytes.fromhex(packet['dst'])
    check = args.check.resolve()
    if json.loads((check/'report.json').read_text())['status'] != 'pass':
        raise ValueError('capture requires a successful differential recording')
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                        cwd=ROOT, text=True).strip()).parent
    sys.path.insert(0, str(ROOT))
    from harness.linux import verify_kernel
    identity, kraken = verify_kernel(ORACLE.parent), verify_pin(ROOT)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'snapshot.json').exists():
        raise ValueError('output already contains a snapshot')
    command = json.loads((check/'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel')+1]).resolve() != ORACLE.parent/'arch/x86/boot/bzImage':
        raise ValueError('recording names another kernel')
    socket = out/'gdb.sock'
    if socket.exists():
        raise ValueError('debugger endpoint already exists')
    command += ['-S', '-chardev', f'socket,path={socket},server=on,wait=off,id=pairgdb', '-gdb', 'chardev:pairgdb']
    entry = probe['entry']
    with slot(shared), (out/'boot.log').open('wb') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log, stderr=log)
        remote = None
        try:
            deadline = time.monotonic()+10
            while not socket.exists():
                if process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('QEMU debugger did not start; inspect boot.log')
                time.sleep(0.02)
            remote = Remote(socket, args.timeout)
            remote.breakpoint(entry)
            for occurrence in range(256):
                regs = remote.resume()
                if regs['rip'] != entry:
                    raise ValueError('unexpected stop selecting invocation')
                if regs['rsi'] == width and remote.read(regs['rdx'], width//8) == query:
                    break
                remote.breakpoint(entry, False)
                remote.resume(step=True)
                remote.breakpoint(entry)
            else:
                raise ValueError('selected invocation never occurred')
            completed = []
            for line in (out/'boot.log').read_text().splitlines():
                if line.startswith('LEANUX_COVERAGE '):
                    row = json.loads(line.split(' ', 1)[1])
                    if row['id'] != probe['trace']['id']:
                        raise ValueError('capture requires an isolated trace')
                    completed.append(row['index'])
            if completed != list(range(probe['operation'])):
                raise ValueError(f'wrong operation prefix: {completed}')
            print(f'capturing width {width}, operation {probe["operation"]}, occurrence {occurrence}', flush=True)
            initial, spans, coverage_bytes = capture(remote, regs, probe, layout, args.instruction_budget)
            return_pc = remote.word(regs['rsp'])
            remote.breakpoint(entry, False)
            if int(remote.command('qqemu.sstep'), 16) != 7:
                raise ValueError('QEMU stepping mode is not ENABLE|NOIRQ|NOTIMER')
            executed, headers, returned = [], [], regs
            # Independent header observations include the actual graph, locals,
            # metadata and KCOV header; no full allocation copy per iteration.
            header_spans = [(a, 8 if a == initial['coverage'] else size) for a, size in spans]
            for _ in range(args.instruction_budget):
                if returned['rip'] == entry+0xd5:
                    headers.append(endpoint(remote, returned, header_spans))
                executed.append(returned['rip'])
                returned = remote.resume(step=True)
                if returned['rip'] == return_pc:
                    break
            else:
                raise ValueError('capture instruction budget exhausted')
            if returned['rsp'] != regs['rsp']+8 or any(returned[n] != regs[n] for n in ('rbx', 'rbp', 'r12', 'r13', 'r14', 'r15')):
                raise ValueError('return did not restore ABI state')
            if remote.word(initial['coverage']) >= min(initial['capacity'], initial['coverageUsed']+1+args.instruction_budget):
                raise ValueError('returned coverage exceeds captured extent')
            result = dict(origin='QEMU stopped invocation; unmodified bytes and registers',
                          kernel=identity, image_sha256=hashlib.sha256(ORACLE.read_bytes()).hexdigest(), kraken=kraken,
                          trace=probe['trace']['id'], operation=probe['operation'], occurrence=occurrence,
                          instructionBudget=args.instruction_budget, executionMode='sequential',
                          executedPCs=executed, completedOperations=completed, initial=initial,
                          headers=headers, bulkBlocks=[dict(address=initial['coverage'], file='coverage.bin', size=len(coverage_bytes))],
                          returned=endpoint(remote, returned, spans))
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
                    raise RuntimeError('QEMU cleanup required a kill; capture failed')
            socket.unlink(missing_ok=True)
    (out/'coverage.bin').write_bytes(coverage_bytes)
    (out/'snapshot.json').write_text(json.dumps(result)+'\n')
    (out/'layouts.json').write_text(json.dumps(layout)+'\n')
    print(json.dumps(dict(status='captured', width=width, instructions=len(executed), headers=len(headers),
                          nodes=len(initial['nodes']), peers=len(initial['peers']),
                          entry_bytes=sum(len(b['bytes']) for b in initial['blocks'])+len(coverage_bytes),
                          seconds=round(time.monotonic()-started, 3))), flush=True)


if __name__ == '__main__':
    main()
