#!/usr/bin/env python3
"""C1 phase A: capture every allowed-IPs insertion of one recorded trace in a
stopped s5 guest, with the allocation sites armed (the oracle's ordinary
recording mode).

For each call of wg_allowedips_insert_v4/_v6 it records the registers and the
memory the C1 statements talk about at the wrapper's entry and return and at
every call of and return from the two service addresses, and, across each of
those intervals and between consecutive calls, the difference of the WHOLE
guest RAM (QEMU's pmemsave through the debugger's monitor passthrough), so
that what a service wrote is observed, not assumed.

It uses the binary package's existing debugger client (capture_lookup.Remote)
and QEMU slot lock, starts the guest from the recorded check's own QEMU
command, and writes neither guest registers nor guest memory. The call is
single-stepped with interrupts and timers deferred: a sequential environment,
as in the existing captures. No harness, guest or kernel file is changed.

  LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle /usr/bin/python3 -B \
    binary/Statements/C1/capture/capture_insertions.py \
    --check .artifacts/check/c1-<trace> --out .tmp/c1/capture-<trace>
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path[:0] = [str(ROOT / 'binary'), str(ROOT)]
from capture_lookup import Remote, slot          # noqa: E402
from layouts import layouts                       # noqa: E402
from pin import verify_pin                        # noqa: E402
from target import ORACLE, pins, verify_image     # noqa: E402
from allowedips_mutation import prepare           # noqa: E402

NAMES = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi', 'rsp', 'rbp', 'r8', 'r9', 'r10', 'r11',
         'r12', 'r13', 'r14', 'r15', 'rip', 'eflags']
PAGE = 4096


class Fast(Remote):
    """The package's client plus: all registers in one packet, and the
    monitor passthrough (read-only commands: pmemsave, gva2gpa)."""

    def _layout(self):
        offset, table = 0, {}
        for name, (number, bits) in sorted(self.registers.items(), key=lambda item: item[1][0]):
            table[name] = (offset, bits // 8)
            offset += bits // 8
        self._offsets = {name: table[name] for name in NAMES}

    def regs(self):
        if not hasattr(self, '_offsets'):
            self._layout()
        raw = bytes.fromhex(self.command('g').decode('ascii').replace('x', '0'))
        return {name: int.from_bytes(raw[o:o + n], 'little') for name, (o, n) in self._offsets.items()}

    def monitor(self, text):
        payload = ('qRcmd,' + text.encode().hex()).encode('ascii')
        self.socket.sendall(b'$' + payload + b'#' + f'{sum(payload) % 256:02x}'.encode())
        if self._byte() != b'+':
            raise ValueError('monitor command not acknowledged')
        output = b''
        while True:
            if self._byte() != b'$':
                raise ValueError('invalid debugger packet start')
            body = bytearray()
            while (b := self._byte()) != b'#':
                body.extend(b)
            self._byte(); self._byte()
            self.socket.sendall(b'+')
            if bytes(body) == b'OK':
                return output.decode(errors='replace')
            if body[:1] == b'O':
                output += bytes.fromhex(body[1:].decode('ascii'))
            else:
                raise ValueError(f'monitor command failed: {text}: {bytes(body)!r}')


def diff(old, new):
    """Changed byte runs between two RAM images: [physical address, old hex, new hex]."""
    runs = []
    for page in range(0, len(old), PAGE):
        a, b = old[page:page + PAGE], new[page:page + PAGE]
        if a == b:
            continue
        i = 0
        while i < PAGE:
            if a[i] == b[i]:
                i += 1
                continue
            j = i
            while j < PAGE and a[j] != b[j]:
                j += 1
            runs.append([page + i, bytes(a[i:j]).hex(), bytes(b[i:j]).hex()])
            i = j
    return runs


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--check', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--step-budget', type=int, default=2000000)
    parser.add_argument('--coverage-words', type=int, default=8192)
    args = parser.parse_args()
    check, out = args.check.resolve(), args.out.resolve()
    if json.loads((check / 'report.json').read_text())['status'] != 'pass':
        raise ValueError('capture requires a passing isolated differential recording')
    [trace] = [json.loads(line) for line in (check / 'chunk-000/model/inputs.jsonl').read_text().splitlines()]
    expected = [dict(op=i, family=a['family'], addr=a['addr'], cidr=a['cidr'], key=p['public_key'])
                for i, op in enumerate(trace['ops']) if op['op'] == 'wg_set'
                for p in op['config'].get('peers', []) for a in p.get('allowed_ips', [])]
    verify_image()
    pin = verify_pin(ROOT)
    from harness.linux import verify_kernel
    identity = verify_kernel(ORACLE.parent, expected=pins()[0])
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'capture.json').exists():
        raise ValueError('capture output is already occupied')
    prepare(out / 'input.json')
    probe = json.loads((out / 'input.json').read_text())
    layout = layouts(ORACLE)
    peer_layout, node_size = layout['wg_peer'], probe['lookup']['offsets']['nodeSize']
    key_offset = peer_layout['members']['handshake'] + layout['noise_handshake']['members']['remote_static']
    shared = Path(subprocess.check_output(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                                          cwd=ROOT, text=True).strip()).parent
    command = json.loads((check / 'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel') + 1]).resolve() != ORACLE.parent / 'arch/x86/boot/bzImage':
        raise ValueError('recorded command names another kernel')
    ram = command[command.index('-m') + 1]
    ram_bytes = int(ram.rstrip('MmGg')) * (2**30 if ram[-1] in 'Gg' else 2**20)
    if ram_bytes > 2**31:
        raise ValueError('guest RAM larger than the low memory range this capture dumps')
    socket = out / 'gdb.sock'
    command += ['-S', '-chardev', f'socket,path={socket},server=on,wait=off,id=pairgdb', '-gdb', 'chardev:pairgdb']
    if shutil.which(command[0]) is None:
        command = [str(ROOT / 'scripts/in-bundle'), *command]
    dump_path = out / 'ram.bin'
    started = time.monotonic()
    calls, between, peers, nodes, translations, text = [], [], {}, [], {}, {}
    ended, initial_peers = 'all expected calls captured', 0
    with slot(shared), (out / 'boot.log').open('wb') as log:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL, stdout=log, stderr=log)
        remote = None
        try:
            deadline = time.monotonic() + 10
            while not socket.exists():
                if process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('QEMU debugger did not start; inspect boot.log')
                time.sleep(0.02)
            remote = Fast(socket, 600)

            def dump():
                dump_path.unlink(missing_ok=True)
                reply = remote.monitor(f'pmemsave 0 {ram_bytes:#x} "{dump_path}"')
                if not dump_path.exists():
                    raise ValueError(f'pmemsave wrote nothing: {reply!r}')
                data = dump_path.read_bytes()
                if len(data) != ram_bytes:
                    raise ValueError('short RAM dump')
                return data

            def translate(address, size):
                for page in range(address // PAGE, (address + size - 1) // PAGE + 1):
                    if page not in translations:
                        reply = remote.monitor(f'gva2gpa {page * PAGE:#x}')
                        translations[page] = int(reply.split('gpa:')[1].split()[0], 16) if 'gpa:' in reply else None

            for pc in [probe['insert4'], probe['insert6']]:
                remote.breakpoint(pc)
            last_return = None
            for index, want in enumerate(expected):
                try:
                    regs = remote.resume()
                except (EOFError, ValueError, OSError) as stop:
                    ended = f'guest ended before call {index}: {stop}'
                    break
                family = 4 if regs['rip'] == probe['insert4'] else 6
                table, peer, width = regs['rdi'], regs['rcx'], 4 if family == 4 else 16
                if regs['rip'] not in (probe['insert4'], probe['insert6']) or family != want['family'] or \
                        remote.read(regs['rsi'], width) != bytes.fromhex(want['addr']) or regs['rdx'] % 256 != want['cidr'] or \
                        remote.read(peer + key_offset, 32) != bytes.fromhex(want['key']):
                    raise ValueError(f'call {index} differs from the trace: {regs} {want}')
                if not peers:   # every peer of the device, in creation order (the device's peer list)
                    head = remote.word(peer + peer_layout['members']['device']) + layout['wg_device']['members']['peer_list']
                    link = remote.word(head)
                    while link != head and len(peers) < 64:
                        other = link - peer_layout['members']['peer_list']
                        peers[other] = remote.read(other + key_offset, 32).hex()
                        link = remote.word(link)
                    # the code the guest runs at the two service addresses (boot-time patching)
                    text = {name: remote.read(probe[name], 0x400).hex() for name in ['alloc', 'free']}
                    if remote.regs() != Remote.regs(remote):
                        raise ValueError('register packet layout differs from the per-register reads')
                    initial_peers = len(peers)
                if peer not in peers:   # created by the caller since the first call (outside the closed world)
                    peers[peer] = want['key']
                pcpu = probe['lookup']['preempt'] - layout['pcpu_hot']['members']['preempt_count']
                task = remote.word(pcpu + layout['pcpu_hot']['members']['current_task'])
                mode, capacity, area = remote.word(task + 0x6e0, 4), remote.word(task + 0x6e4, 4), remote.word(task + 0x6e8)
                used = remote.word(area) if area else 0
                stack_low = regs['rsp'] - 3072
                spans = [(table, layout['allowedips']['size']), (stack_low, 3072 + 256), (regs['rsi'], width),
                         (probe['cacheWord'], 8), (pcpu, layout['pcpu_hot']['size']), (task + 0x6e0, 0x38)]
                spans += [(p, peer_layout['size']) for p in peers]
                spans += [(n, node_size) for n in nodes]
                if area:
                    spans.append((area, 8 * min(capacity, used + args.coverage_words)))
                for a, size in spans:
                    translate(a, size)

                def endpoint(registers):
                    return dict(registers=registers,
                                blocks=[dict(address=a, bytes=list(remote.read(a, size))) for a, size in spans])
                entry_ram = dump()
                if index == 0 and area:   # the whole buffer once, for the verbatim readiness check
                    (out / 'coverage-call0.bin').write_bytes(remote.read(area, 8 * capacity))
                if last_return is not None:
                    between.append(dict(before=index, diff=diff(last_return, entry_ram)))
                call = dict(index=index, want=want, family=family, table=table, peer=peer, task=task, mode=mode,
                            capacity=capacity, coverage=area, coverageUsed=used, pcpu=pcpu,
                            cacheValue=remote.word(probe['cacheWord']), nodesBefore=list(nodes),
                            initial=endpoint(regs), services=[], executedPCs=[])
                return_pc = remote.word(regs['rsp'])
                for pc in [probe['insert4'], probe['insert6']]:
                    remote.breakpoint(pc, False)
                if int(remote.command('qqemu.sstep'), 16) != 7:
                    raise ValueError('QEMU stepping must defer IRQs and timers')
                service, current, service_ram = None, regs, None
                for steps in range(args.step_budget):
                    pc = current['rip']
                    if service is None and pc in (probe['alloc'], probe['free']):
                        service = dict(kind='alloc' if pc == probe['alloc'] else 'free', initial=endpoint(current),
                                       returnPC=remote.word(current['rsp']), pcs=[], regs=[], lowestRsp=current['rsp'],
                                       flagsSeen=0, flagsCleared=0xffffffff)
                        service_ram = dump()
                    if service is None:
                        call['executedPCs'].append(pc)
                    else:
                        service['pcs'].append(pc)
                        service['regs'].append([current[name] for name in NAMES[:16]])
                        service['lowestRsp'] = min(service['lowestRsp'], current['rsp'])
                        service['flagsSeen'] |= current['eflags']
                        service['flagsCleared'] &= current['eflags']
                    current = remote.resume(step=True)
                    if service is not None and current['rip'] == service['returnPC'] and \
                            current['rsp'] == service['initial']['registers']['rsp'] + 8:
                        if service['kind'] == 'alloc' and current['rax']:
                            if current['rax'] in nodes:
                                raise ValueError('allocator returned an object already handed out')
                            nodes.append(current['rax'])
                            spans.append((current['rax'], node_size))
                            translate(current['rax'], node_size)
                        if service['kind'] == 'free':
                            freed = service['initial']['registers']['rsi']
                            nodes.remove(freed)
                        after = dump()
                        service.update(returned=endpoint(current), allocation=current['rax'],
                                       diff=diff(service_ram, after), nodesAfter=list(nodes))
                        if service['kind'] == 'free':
                            spans.remove((freed, node_size))
                        call['services'].append(service)
                        service = None
                    if service is None and current['rip'] == return_pc and current['rsp'] == regs['rsp'] + 8:
                        break
                else:
                    raise ValueError('capture step budget exhausted')
                last_return = dump()
                call.update(returned=endpoint(current), nativeSteps=steps + 1, diff=diff(entry_ram, last_return),
                            nodesAfter=list(nodes), coverageUsedAfter=remote.word(area) if area else 0)
                if call['coverageUsedAfter'] - used >= args.coverage_words:
                    raise ValueError('coverage window too small for this call')
                calls.append(call)
                print(json.dumps(dict(call=index, family=family, eax=current['rax'] % 2**32, steps=steps + 1,
                                      services=[(s['kind'], len(s['pcs']), s['allocation']) for s in call['services']])),
                      flush=True)
                if current['rax'] % 2**32:
                    ended = f'call {index} returned {current["rax"] % 2**32:#x}; the caller abandons the set'
                    break
                for pc in [probe['insert4'], probe['insert6']]:
                    remote.breakpoint(pc)
        finally:
            if remote:
                remote.socket.close()
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill(); process.wait()
            socket.unlink(missing_ok=True)
            dump_path.unlink(missing_ok=True)
    result = dict(origin='stopped QEMU, sequential stepping; services executed natively by the guest',
                  kernel=identity, image_sha256=pins()[1], kraken=pin, trace=trace['id'], hidden=trace.get('hidden'),
                  steer=trace.get('steer'), expected=expected, ended=ended, ramBytes=ram_bytes,
                  peers=[[a, key] for a, key in peers.items()],
                  translations=[[page * PAGE, gpa] for page, gpa in sorted(translations.items())],
                  calls=calls, between=between, serviceText=text, peersAtFirstCall=initial_peers)
    (out / 'capture.json').write_text(json.dumps(result) + '\n')
    (out / 'layouts.json').write_text(json.dumps(layout) + '\n')
    print(json.dumps(dict(status='captured', calls=len(calls), ended=ended, seconds=round(time.monotonic() - started, 1))))


if __name__ == '__main__':
    main()
