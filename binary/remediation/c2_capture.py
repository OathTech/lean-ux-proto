#!/usr/bin/env python3
"""Capture C2 entry/exit plus all 256 MiB RAM on the pinned clean image.

This is a bounded local-call experiment, not a complete lifecycle capture.
The prepared command comes from the archive's two_device.py --prepare-only.
No kernel, guest memory or register is written. 'sequential' single-steps
the range with IRQs/timers deferred; 'ordinary' resumes to the first exit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'binary'), str(ROOT)]
from capture_lookup import Remote, slot
from harness.linux import verify_kernel
from c2_memory import ADDRESS, DIRECT_MAP, IMAGE_BASE, Writer, translate

IDENTITY = '558b24bf9be22fc6292fccd5de29fd461628e63ac51acc9ead420b74b8fc401a'
ELF_SHA256 = 'b87b16f8f9ed8c9aa9e67b7625d2be650a52ed1bc8bb689c6c0e0c57127fe9e3'
ENTRY, DONE, REJECT = 0xffffffff8123f9e1, 0xffffffff8123fa8d, 0xffffffff8123fcff
PREEMPT, WINDOW_OFFSET, WINDOW_BYTES = 0xffffffff818c8588, 136, 1032
RAM_BYTES = 256 * 2**20


class ObservingRemote(Remote):
    def monitor(self, text):
        payload = ('qRcmd,' + text.encode().hex()).encode('ascii')
        self.socket.sendall(b'$' + payload + b'#' + f'{sum(payload) % 256:02x}'.encode())
        if self._byte() != b'+':
            raise ValueError('monitor command not acknowledged')
        output = bytearray()
        while True:
            if self._byte() != b'$':
                raise ValueError('invalid monitor packet start')
            body = bytearray()
            while (b := self._byte()) != b'#':
                body.extend(b)
            if int(self._byte() + self._byte(), 16) != sum(body) % 256:
                raise ValueError('monitor packet checksum mismatch')
            self.socket.sendall(b'+')
            if body == b'OK':
                return output.decode('ascii')
            if body[:1] != b'O':
                raise ValueError(f'monitor command failed: {body!r}')
            output.extend(bytes.fromhex(body[1:].decode('ascii')))

    def go(self):
        try:
            reply = self.command('c')
        except (EOFError, BrokenPipeError, ConnectionResetError):
            # QEMU may close before the final packet's ACK is written. The
            # caller still requires exit status zero and the workload marker.
            return None
        if reply[:1] in (b'W', b'X'):
            return None
        if reply[:3] not in (b'T05', b'S05'):
            raise ValueError(f'unexpected guest stop: {reply!r}')
        return self.regs()


def image_description(kernel):
    with kernel.open('rb') as source:
        if hashlib.file_digest(source, 'sha256').hexdigest() != ELF_SHA256:
            raise ValueError('the command does not use the pinned net-clean-2 ELF')
    verify_kernel(kernel.parent, expected=IDENTITY)
    symbols = {}
    result = subprocess.run(['nm', str(kernel)], text=True, capture_output=True, check=True)
    if result.stderr:
        raise ValueError(f'nm diagnostics: {result.stderr}')
    for line in result.stdout.splitlines():
        fields = line.split()
        if len(fields) == 3 and fields[2] in ('init_top_pgt', '_text', '_end'):
            symbols[fields[2]] = int(fields[0], 16)
    if set(symbols) != {'init_top_pgt', '_text', '_end'}:
        raise ValueError('missing or ambiguous target symbols')
    from elftools.elf.elffile import ELFFile
    with kernel.open('rb') as source:
        elf = ELFFile(source)
        section = elf.get_section_by_name('.text')
        start = ENTRY - section['sh_addr']
        code = section.data()[start:start + DONE - ENTRY]
    if len(code) != DONE - ENTRY:
        raise ValueError('C2 range missing from .text')
    return dict(identity=IDENTITY, elf_sha256=ELF_SHA256, symbols=symbols,
                page_table_root=symbols['init_top_pgt'] - IMAGE_BASE, code=code.hex())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--command', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--mode', choices=['ordinary', 'sequential'], required=True)
    parser.add_argument('--first', type=int, default=32)
    parser.add_argument('--timeout', type=float, default=900)
    args = parser.parse_args()
    if not 1 <= args.first <= 128:
        raise ValueError('this bounded experiment admits 1 to 128 visits')
    command = json.loads(args.command.read_text())
    for name, expected in [('-m', '256'), ('-cpu', 'qemu64'), ('-smp', '1')]:
        if command.count(name) != 1 or command[command.index(name) + 1] != expected:
            raise ValueError(f'unexpected prepared guest option {name}')
    if command.count('-kernel') != 1 or '-S' in command or '-gdb' in command:
        raise ValueError('unexpected prepared command')
    kernel = Path(command[command.index('-kernel') + 1]).resolve().parents[3] / 'vmlinux'
    description = image_description(kernel)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    writer = Writer(out / 'ram', RAM_BYTES)
    metadata = dict(schema='c2-native-frame-v2', mode=args.mode, first=args.first,
                    ram_bytes=RAM_BYTES, image=description, forced=False,
                    observation='complete physical RAM and explicitly translated kernel virtual bytes')
    (out / 'metadata.json').write_text(json.dumps(metadata) + '\n')
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                        cwd=ROOT, text=True).strip()).parent
    socket = out / 'gdb.sock'
    command += ['-S', '-chardev', f'socket,path={socket},server=on,wait=off,id=c2gdb', '-gdb', 'chardev:c2gdb']
    visits, stray, opened = 0, 0, None
    started = time.monotonic()
    with slot(shared), (out / 'boot.log').open('wb') as boot, (out / 'visits.jsonl').open('w') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=boot, stderr=boot)
        try:
            deadline = time.monotonic() + 10
            while not socket.exists():
                if process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('QEMU debugger did not start')
                time.sleep(0.02)
            remote = ObservingRemote(socket, args.timeout)
            if int(remote.command('qqemu.sstep'), 16) != 7:
                raise ValueError('QEMU single stepping must defer interrupts and timers')
            for pc in (ENTRY, DONE, REJECT):
                remote.breakpoint(pc)

            def side(regs, kp, skb):
                if remote.read(ENTRY, DONE - ENTRY).hex() != description['code']:
                    raise ValueError('live C2 instruction bytes differ from pinned ELF')
                row = dict(regs=regs, window=remote.read(kp + WINDOW_OFFSET, WINDOW_BYTES).hex(),
                           nonce=remote.read(skb + 0x28, 8).hex(), preempt=remote.read(PREEMPT, 4).hex())
                control = remote.monitor('info registers')
                cr3, cr4 = re.search(r'CR3=([0-9a-fA-F]+)', control), re.search(r'CR4=([0-9a-fA-F]+)', control)
                if cr3 is None or cr4 is None or int(cr4[1], 16) & (1 << 12):
                    raise ValueError('missing CR3/CR4 or unsupported five-level paging')
                row['page_table_root'] = int(cr3[1], 16) & ADDRESS
                dump = out / 'physical.bin'
                if dump.exists():
                    raise ValueError('stale RAM dump')
                answer = remote.monitor(f'pmemsave 0 {RAM_BYTES:#x} "{dump}"')
                if answer.strip():
                    raise ValueError(f'pmemsave diagnostics: {answer}')
                data = dump.read_bytes()
                dump.unlink()
                alias = DIRECT_MAP + translate(data, row['page_table_root'], PREEMPT)
                row['count_alias'] = dict(address=alias, bytes=remote.read(alias, 4).hex())
                row['snapshot'] = writer.add(data)
                return row

            while True:
                if time.monotonic() - started > args.timeout:
                    raise TimeoutError('capture wall-clock budget exhausted')
                regs = remote.go()
                if regs is None:
                    break
                pc = regs['rip']
                if pc == ENTRY:
                    if opened is not None:
                        raise ValueError('nested C2 entry before its exit')
                    opened = dict(visit=visits, kp=regs['rbx'], skb=regs['r15'], forced=False,
                                  entry=side(regs, regs['rbx'], regs['r15']))
                    if args.mode == 'sequential':
                        remote.breakpoint(ENTRY, False)
                        pcs = []
                        for _ in range(2048):
                            if regs['rip'] in (DONE, REJECT):
                                break
                            if not ENTRY <= regs['rip'] < DONE:
                                raise ValueError('sequential execution left C2 before an exit')
                            pcs.append(regs['rip'])
                            regs = remote.resume(step=True)
                        else:
                            raise ValueError('C2 instruction budget exhausted')
                        remote.breakpoint(ENTRY)
                        opened['executed_pcs'] = pcs
                        pc = regs['rip']
                if pc in (DONE, REJECT):
                    if opened is None:
                        stray += 1
                    else:
                        opened['exit'] = side(regs, opened['kp'], opened['skb'])
                        log.write(json.dumps(opened) + '\n')
                        log.flush()
                        opened, visits = None, visits + 1
                        if visits == args.first:
                            for address in (ENTRY, DONE, REJECT):
                                remote.breakpoint(address, False)
                elif pc != ENTRY:
                    raise ValueError(f'unexpected stop {pc:#x}')
                armed = visits < args.first
                if armed:
                    remote.breakpoint(pc, False)
                remote.resume(step=True)
                if armed:
                    remote.breakpoint(pc)
            remote.socket.close()
            process.wait(timeout=30)
            if process.returncode:
                raise ValueError(f'QEMU exited {process.returncode}')
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            socket.unlink(missing_ok=True)
    if opened is not None or visits == 0:
        raise ValueError('missing complete C2 visits')
    if 'PLAIN done' not in (out / 'boot.log').read_text():
        raise ValueError('prepared workload did not complete')
    summary = dict(status='captured', visits=visits, stray_exit_stops=stray,
                   quota_reached=visits == args.first, sampled=False, snapshots=writer.count,
                   claim_scope='individual visits only; no lifetime or whole-workload admission',
                   seconds=round(time.monotonic() - started, 3))
    (out / 'summary.json').write_text(json.dumps(summary) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
