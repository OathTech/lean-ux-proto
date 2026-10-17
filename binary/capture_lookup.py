#!/usr/bin/env python3
"""Capture an index-lookup entry and return through QEMU's read-only GDB path.

Run under capped and scripts/in-bundle, with --input from pair_run.py and
--check naming its differential check. No guest register or memory writes;
TCG hardware breakpoints leave the read-only oracle image unchanged.
Protocol: https://sourceware.org/gdb/current/onlinedocs/gdb.html/Packets.html
QEMU: https://www.qemu.org/docs/master/system/gdb.html#using-unix-sockets
"""
import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from xml.parsers import expat

from census import ROOT, ORACLE
from pin import verify_pin


class Remote:
    def __init__(self, path, timeout):
        self.socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.socket.settimeout(timeout)
        self.socket.connect(str(path))
        features = self.command('qSupported:xmlRegisters=i386;qXfer:features:read+')
        if b'qXfer:features:read+' not in features:
            raise ValueError('QEMU did not advertise register descriptions')
        self.registers = {}
        self._register_xml('target.xml', 0)

    def _byte(self):
        b = self.socket.recv(1)
        if not b:
            raise EOFError('QEMU closed the debugger connection')
        return b

    def command(self, command):
        payload = command.encode('ascii')
        self.socket.sendall(b'$' + payload + b'#' + f'{sum(payload) % 256:02x}'.encode())
        if self._byte() != b'+':
            raise ValueError(f'debugger command not acknowledged: {command[:80]}')
        if self._byte() != b'$':
            raise ValueError('invalid debugger packet start')
        encoded = bytearray()
        while (b := self._byte()) != b'#':
            encoded.extend(b)
        checksum = int(self._byte() + self._byte(), 16)
        if checksum != sum(encoded) % 256:
            raise ValueError('debugger packet checksum mismatch')
        self.socket.sendall(b'+')
        decoded, i = bytearray(), 0
        while i < len(encoded):
            if encoded[i] == ord('}'):
                i += 1
                decoded.append(encoded[i] ^ 32)
            elif encoded[i] == ord('*'):
                i += 1
                if not decoded or encoded[i] < 29:
                    raise ValueError('invalid debugger run-length encoding')
                decoded.extend([decoded[-1]] * (encoded[i] - 29))
            else:
                decoded.append(encoded[i])
            i += 1
        return bytes(decoded)

    def _xml(self, name):
        data = b''
        while True:
            reply = self.command(f'qXfer:features:read:{name}:{len(data):x},800')
            if reply[:1] not in (b'm', b'l'):
                raise ValueError(f'cannot read register XML {name}: {reply!r}')
            data += reply[1:]
            if reply[:1] == b'l':
                # GDB target descriptions use literal xi:include names without
                # necessarily declaring an XML namespace. Parse those names as
                # GDB does; no external DTD or entity is fetched.
                tree = ET.TreeBuilder()
                parser = expat.ParserCreate()
                parser.StartElementHandler = tree.start
                parser.EndElementHandler = tree.end
                parser.CharacterDataHandler = tree.data
                parser.Parse(data, True)
                return tree.close()

    def _register_xml(self, name, number):
        for element in self._xml(name).iter():
            if element.tag.endswith('include'):
                number = self._register_xml(element.attrib['href'], number)
            elif element.tag == 'reg':
                number = int(element.attrib.get('regnum', number))
                self.registers[element.attrib['name']] = (number, int(element.attrib['bitsize']))
                number += 1
        return number

    def regs(self):
        result = {}
        for name in ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi', 'rsp', 'rbp',
                     'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'rip', 'eflags']:
            number, bits = self.registers[name]
            raw = bytes.fromhex(self.command(f'p{number:x}').decode('ascii'))
            if len(raw)*8 != bits:
                raise ValueError(f'register width mismatch: {name}')
            result[name] = int.from_bytes(raw, 'little')
        return result

    def read(self, address, size):
        data = b''
        while len(data) < size:
            chunk = min(1024, size - len(data))
            reply = self.command(f'm{address+len(data):x},{chunk:x}')
            if reply.startswith(b'E'):
                raise ValueError(f'unmapped capture read at {address+len(data):#x}, size {chunk}: {reply!r}')
            raw = bytes.fromhex(reply.decode('ascii'))
            if len(raw) != chunk:
                raise ValueError('short capture read')
            data += raw
        return data

    def word(self, address, size=8):
        return int.from_bytes(self.read(address, size), 'little')

    def breakpoint(self, address, insert=True):
        command = f'{"Z" if insert else "z"}1,{address:x},1'
        if self.command(command) != b'OK':
            raise ValueError(f'TCG hardware breakpoint refused: {command}')

    def resume(self, step=False):
        reply = self.command('s' if step else 'c')
        if reply[:3] not in (b'T05', b'S05'):
            raise ValueError(f'unexpected guest stop: {reply!r}')
        return self.regs()


@contextmanager
def slot(shared):
    paths = [shared / '.artifacts/runs' / ('qemu.lock' if i == 0 else f'qemu.lock.{i}')
             for i in range(int(os.environ.get('LEANUX_QEMU_SLOTS', '16')))]
    for path in paths:
        lock = path.open('a+')
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            lock.close()
            continue
        try:
            yield
        finally:
            lock.close()
        return
    raise RuntimeError('all shared QEMU slots occupied; capture did not start')


def capture(remote, regs, probe, layout, instruction_budget):
    """Read a pointer closure. Expected mirror field values are not inputs."""
    blocks, entries, peers = {}, [], set()

    def block(address, size):
        data = remote.read(address, size)
        for (previous, length), content in blocks.items():
            lo, hi = max(address, previous), min(address+size, previous+length)
            if lo < hi and data[lo-address:hi-address] != content[lo-previous:hi-previous]:
                raise ValueError('overlapping snapshot reads disagree while CPU stopped')
        blocks[address, size] = data
        return data

    o = probe['offsets']
    table = block(regs['rdi'], o['tableSize'])
    for bucket in range(8192):
        cursor = int.from_bytes(table[bucket*8:bucket*8+8], 'little')
        seen = set()
        while cursor:
            if cursor in seen or len(seen) >= 256:
                raise ValueError('cyclic or oversized captured bucket')
            seen.add(cursor)
            address = cursor - o['hash']
            entry = block(address, o['entrySize'])
            peer = int.from_bytes(entry[o['peer']:o['peer']+8], 'little')
            kind = int.from_bytes(entry[o['kind']:o['kind']+4], 'little')
            entries.append(dict(address=address, kind=kind, peer=peer))
            if peer:
                peers.add(peer)
            if kind == 1:
                peers.add(address - o['peerHandshake'] - o['handshakeEntry'])
            elif kind != 2:
                raise ValueError(f'unknown entry kind {kind}')
            cursor = int.from_bytes(entry[o['hash']+o['next']:o['hash']+o['next']+8], 'little')
    if not peers:
        raise ValueError('pilot cannot discover device membership without a peer root')
    peer_layout = layout['wg_peer']
    device_offset = peer_layout['members']['device']
    devices = {remote.word(p+device_offset) for p in peers}
    if len(devices) != 1:
        raise ValueError('captured peers disagree on owning device')
    device, = devices
    device_data = block(device, layout['wg_device']['size'])
    index_off = layout['wg_device']['members']['index_hashtable']
    if int.from_bytes(device_data[index_off:index_off+8], 'little') != regs['rdi']:
        raise ValueError('captured device has a different index table')
    head = device + layout['wg_device']['members']['peer_list']
    peer_link = peer_layout['members']['peer_list']
    cursor = remote.word(head)
    members = set()
    while cursor != head:
        p = cursor - peer_link
        if p in members or len(members) >= 256:
            raise ValueError('cyclic or oversized captured peer list')
        members.add(p)
        cursor = remote.word(cursor)
    if not peers <= members:
        raise ValueError('table references peer outside device membership')
    peers = members
    peer_rows, keypairs = [], set()
    for p in sorted(peers):
        data = block(p, peer_layout['size'])
        key_offset = o['peerHandshake'] + layout['noise_handshake']['members']['remote_static']
        peer_rows.append(dict(address=p, publicKey=list(data[key_offset:key_offset+32])))
        for name in ['current_keypair', 'previous_keypair', 'next_keypair']:
            offset = peer_layout['members']['keypairs'] + layout['noise_keypairs']['members'][name]
            ptr = int.from_bytes(data[offset:offset+8], 'little')
            if ptr:
                keypairs.add(ptr)
    keypairs.update(e['address'] - o['keypairEntry'] for e in entries if e['kind'] == 2)
    for p in sorted(keypairs):
        block(p, layout['noise_keypair']['size'])
    # Include the actual caller frame and enough lower stack for this anchored
    # function plus its decoded services. No bytes are zero-filled.
    block(regs['rsp'] - 2048, 2064)
    block(regs['rcx'], 8)
    pcpu = probe['preempt'] - layout['pcpu_hot']['members']['preempt_count']
    block(pcpu, layout['pcpu_hot']['size'])
    task = remote.word(pcpu + layout['pcpu_hot']['members']['current_task'])
    # These offsets are pinned by the decoded KCOV bodies and existing M1.
    task_fields = [(task+0x6e0, 4), (task+0x6e4, 4), (task+0x6e8, 8), (task+0x704, 4)]
    for address, width in task_fields:
        block(address, width)
    if remote.word(task+0x6e0, 4) != 2:
        raise ValueError('capture pilot requires KCOV_TRACE_PC mode')
    capacity, area = remote.word(task+0x6e4, 4), remote.word(task+0x6e8)
    if not area or not 1 < capacity <= 2**26:
        raise ValueError(f'unsupported captured KCOV buffer: {area:#x}, {capacity}')
    used = remote.word(area)
    if used >= capacity:
        raise ValueError(f'captured KCOV count exceeds capacity: {used}, {capacity}')
    # Capture real bytes for the existing prefix and bounded execution's write
    # headroom. The rest of the large allocation stays unmapped in the snapshot;
    # a replay that accesses it must fail, rather than obtain fabricated zeros.
    captured_words = min(capacity, used + 1 + instruction_budget)
    block(area, captured_words*8)
    return dict(registers=regs, peers=peer_rows, keypairs=sorted(keypairs),
                entries=entries, device=device, task=task, coverage=area, capacity=capacity,
                coverageUsed=used, coverageCapturedWords=captured_words,
                blocks=[dict(address=a, bytes=list(data)) for (a, _), data in sorted(blocks.items())])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--check', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=180)
    parser.add_argument('--instruction-budget', type=int, default=100000)
    args = parser.parse_args()
    if not 0 < args.instruction_budget <= 1000000:
        raise ValueError('instruction budget must be between 1 and 1000000')
    probe = json.loads(args.input.read_text())
    layout = json.loads((args.input.parent/'layouts.json').read_text())
    check = args.check.resolve()
    if json.loads((check/'report.json').read_text())['status'] != 'pass':
        raise ValueError('capture requires a successful differential recording')
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                        cwd=ROOT, text=True).strip()).parent
    sys.path.insert(0, str(ROOT))
    from harness.linux import verify_kernel
    identity = verify_kernel(ORACLE.parent)
    kraken = verify_pin(ROOT)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out/'snapshot.json').exists():
        raise ValueError('output already contains a snapshot; use a fresh output directory')
    command = json.loads((check/'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel')+1]).resolve() != ORACLE.parent/'arch/x86/boot/bzImage':
        raise ValueError('recorded QEMU command names another kernel')
    endpoint = out/'gdb.sock'
    if endpoint.exists():
        raise ValueError('debugger endpoint already exists; refusing to connect to another process')
    command += ['-S', '-chardev', f'socket,path={endpoint},server=on,wait=off,id=pairgdb', '-gdb', 'chardev:pairgdb']
    entry = probe['instructions'][0]['pc']
    with slot(shared), (out/'boot.log').open('wb') as log:
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
                if regs['rdx'] % 2**32 == probe['query'] and regs['rsi'] % 2**32 == 1:
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
                        raise ValueError('capture pilot requires an isolated trace')
                    completed.append(row['index'])
            if completed != list(range(probe['operation'])):
                raise ValueError(f'invocation is not in the selected operation: completed {completed}')
            print(f'capturing entry {entry:#x}, occurrence {occurrence}, query {probe["query"]:#x}', flush=True)
            initial = capture(remote, regs, probe, layout, args.instruction_budget)
            return_pc = remote.word(regs['rsp'])
            remote.breakpoint(entry, False)
            remote.breakpoint(return_pc)
            returned = remote.resume()
            if returned['rip'] != return_pc or returned['rsp'] != regs['rsp']+8:
                raise ValueError('breakpoint did not stop at selected invocation return')
            for name in ['rbx', 'rbp', 'r12', 'r13', 'r14', 'r15']:
                if returned[name] != regs[name]:
                    raise ValueError(f'callee-saved register not restored: {name}')
            if remote.word(initial['coverage']) >= initial['coverageCapturedWords']:
                raise ValueError('returned coverage exceeds captured memory extent')
            final_blocks = [dict(address=b['address'], bytes=list(remote.read(b['address'], len(b['bytes']))))
                            for b in initial['blocks']]
            result = dict(origin='QEMU stopped invocation; unmodified guest bytes and registers',
                          kernel=identity, image_sha256=hashlib.sha256(ORACLE.read_bytes()).hexdigest(),
                          kraken=kraken, trace=probe['trace']['id'], operation=probe['operation'],
                          instructionBudget=args.instruction_budget,
                          completedOperations=completed,
                          occurrence=occurrence, initial=initial,
                          returned=dict(registers=returned, blocks=final_blocks))
        finally:
            if remote:
                remote.socket.close()
            # Only this Popen child is terminated; no process-name matching.
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                    raise RuntimeError('QEMU cleanup timed out and required a kill; capture failed')
            endpoint.unlink(missing_ok=True)
    # Publish success only after the owned QEMU child has terminated normally
    # in response to our deliberate stop at the captured return.
    (out/'snapshot.json').write_text(json.dumps(result)+'\n')
    print(json.dumps(dict(status='captured', pc=return_pc, result=returned['rax'],
                          peers=len(initial['peers']), keypairs=len(initial['keypairs']),
                          bytes=sum(len(b['bytes']) for b in initial['blocks']))), flush=True)


if __name__ == '__main__':
    main()
