#!/usr/bin/env python3
"""Capture the first IPv4 insertion and its allocator boundary in stopped QEMU.

Generic allocator internals are executed by QEMU and recorded as an explicit
external-service transition. Kraken replay executes the WireGuard body. The
capturer never substitutes heap bytes, allocator results or instruction steps.
"""
import argparse
import json
from pathlib import Path
import subprocess
import shutil
import sys
import time

from capture_lookup import Remote, slot
from capture_index_mutator import completed_operations
from layouts import layouts
from pin import verify_pin
from target import ROOT, ORACLE, pins, verify_image


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--check',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--instruction-budget',type=int,default=100000)
    args = parser.parse_args()
    started = time.monotonic()
    if not 0 < args.instruction_budget <= 1000000:
        raise ValueError('invalid instruction budget')
    check, out = args.check.resolve(), args.out.resolve()
    if json.loads((check/'report.json').read_text())['status'] != 'pass':
        raise ValueError('capture requires a passing isolated differential recording')
    [trace] = [json.loads(line) for line in (check/'chunk-000/model/inputs.jsonl').read_text().splitlines()]
    if trace['id'] != 'b1_trie_routing':
        raise ValueError('first-insertion capture requires b1_trie_routing')
    first_peer = trace['ops'][0]['config']['peers'][0]
    query = first_peer['allowed_ips'][0]
    if query['family'] != 4:
        raise ValueError('first insertion is not IPv4')
    [allocation_record] = [r for r in trace['hidden'][0] if r[0] == 77][:1]
    if bytes.fromhex(allocation_record[1])[0] != 1:
        raise ValueError('selected recorded allocation did not succeed')
    probe = json.loads(args.input.read_text())
    verify_image()
    pin = verify_pin(ROOT)
    sys.path.insert(0,str(ROOT))
    from harness.linux import verify_kernel
    identity = verify_kernel(ORACLE.parent,expected=pins()[0])
    layout = layouts(ORACLE)
    shared = Path(subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],cwd=ROOT,text=True).strip()).parent
    out.mkdir(parents=True,exist_ok=True)
    socket = out/'gdb.sock'
    if socket.exists() or (out/'snapshot.json').exists():
        raise ValueError('capture output is already occupied')
    command = json.loads((check/'chunk-000/linux/qemu-command.json').read_text())
    if Path(command[command.index('-kernel')+1]).resolve() != ORACLE.parent/'arch/x86/boot/bzImage':
        raise ValueError('recorded command names another kernel')
    command += ['-S','-chardev',f'socket,path={socket},server=on,wait=off,id=pairgdb','-gdb','chardev:pairgdb']
    if shutil.which(command[0]) is None:
        command = [str(ROOT/'scripts/in-bundle'),*command]
    with slot(shared), (out/'boot.log').open('wb') as log:
        process = subprocess.Popen(command,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=log,stderr=log)
        remote = None
        try:
            deadline = time.monotonic()+10
            while not socket.exists():
                if process.poll() is not None or time.monotonic()>deadline:
                    raise RuntimeError('QEMU debugger did not start; inspect boot.log')
                time.sleep(0.02)
            remote = Remote(socket,240)
            remote.breakpoint(probe['insert4'])
            regs = remote.resume()
            if regs['rip'] != probe['insert4'] or completed_operations(out/'boot.log',trace['id']) != []:
                raise ValueError('wrong invocation or operation prefix')
            if remote.read(regs['rsi'],4) != bytes.fromhex(query['addr']) or regs['rdx']%256 != query['cidr']:
                raise ValueError('captured query differs from selected source call')
            table, peer = regs['rdi'],regs['rcx']
            if remote.word(table) or remote.word(table+8):
                raise ValueError('first-insertion capture expected empty roots')
            device = remote.word(peer+layout['wg_peer']['members']['device'])
            if table != device+layout['wg_device']['members']['peer_allowedips']:
                raise ValueError('argument table differs from peer device')
            key_offset = layout['wg_peer']['members']['handshake']+layout['noise_handshake']['members']['remote_static']
            if remote.read(peer+key_offset,32) != bytes.fromhex(first_peer['public_key']):
                raise ValueError('argument peer differs from selected source peer')
            spans = [(table,layout['allowedips']['size']),(peer,layout['wg_peer']['size']),
                     (regs['rsp']-2048,2064),(regs['rsi'],4),(probe['cacheWord'],8)]
            pcpu = probe['lookup']['preempt']-layout['pcpu_hot']['members']['preempt_count']
            spans.append((pcpu,layout['pcpu_hot']['size']))
            task = remote.word(pcpu+layout['pcpu_hot']['members']['current_task'])
            spans += [(task+offset,size) for offset,size in [(0x6e0,4),(0x6e4,4),(0x6e8,8),(0x704,4)]]
            if remote.word(task+0x6e0,4) != 2:
                raise ValueError('capture requires PC coverage mode')
            capacity, area = remote.word(task+0x6e4,4),remote.word(task+0x6e8)
            used = remote.word(area)
            if not area or not used < capacity <= 2**26:
                raise ValueError('invalid coverage allocation')
            coverage = remote.read(area,capacity*8)
            # Endpoint snapshots cover all possibly appended words, without
            # duplicating the full untouched allocation at every stop.
            spans.append((area,min(capacity,used+args.instruction_budget+1)*8))
            def endpoint(registers, include_coverage=True):
                return dict(registers=registers,blocks=[dict(address=a,bytes=list(remote.read(a,size)))
                            for a,size in spans if include_coverage or a != area])
            initial = endpoint(regs,False)
            return_pc = remote.word(regs['rsp'])
            remote.breakpoint(probe['insert4'],False)
            if int(remote.command('qqemu.sstep'),16) != 7:
                raise ValueError('QEMU stepping must defer IRQs and timers')
            executed, services, current_service = [], [], None
            returned = regs
            for steps in range(args.instruction_budget):
                pc = returned['rip']
                if pc in [probe['alloc'],probe['free']]:
                    if current_service is not None or pc != probe['alloc']:
                        raise ValueError('unexpected service for first empty-root insertion')
                    current_service = dict(initial=endpoint(returned),returnPC=remote.word(returned['rsp']))
                if current_service is None:
                    executed.append(pc)
                returned = remote.resume(step=True)
                if current_service is not None and returned['rip']==current_service['returnPC']:
                    if returned['rsp'] != current_service['initial']['registers']['rsp']+8 or returned['rax']==0:
                        raise ValueError('allocator failed or returned with the wrong stack')
                    allocation = returned['rax']
                    node = remote.read(allocation,probe['lookup']['offsets']['nodeSize'])
                    if any(node):
                        raise ValueError('zalloc returned nonzero bytes')
                    spans.append((allocation,len(node)))
                    current_service.update(returned=endpoint(returned),allocation=allocation)
                    services.append(current_service)
                    current_service = None
                if returned['rip']==return_pc and returned['rsp']==regs['rsp']+8:
                    break
            else:
                raise ValueError('capture instruction budget exhausted')
            if current_service is not None or len(services)!=1:
                raise ValueError('incomplete allocator capture')
            if any(returned[name] != regs[name] for name in ['rbx','rbp','r12','r13','r14','r15']):
                raise ValueError('callee-save register mismatch')
            result = dict(origin='actual stopped QEMU first insertion; generic allocator boundary recorded',
                          kernel=identity,image_sha256=pins()[1],kraken=pin,executionMode='sequential',
                          trace=trace['id'],operation=0,completedOperations=[],instructionBudget=args.instruction_budget,
                          family=4,key=int(query['addr'],16),cidr=query['cidr'],publicKey=first_peer['public_key'],
                          allocationRecord=allocation_record,
                          table=table,peer=peer,task=task,coverage=area,capacity=capacity,coverageUsed=used,
                          initial=initial,returned=endpoint(returned),services=services,executedPCs=executed,
                          nativeSteps=steps+1,bulkBlocks=[dict(address=area,file='coverage.bin',size=len(coverage))])
        finally:
            if remote:
                remote.socket.close()
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill(); process.wait()
                    raise RuntimeError('QEMU cleanup required a kill; capture failed')
            socket.unlink(missing_ok=True)
    (out/'coverage.bin').write_bytes(coverage)
    (out/'snapshot.json').write_text(json.dumps(result)+'\n')
    (out/'layouts.json').write_text(json.dumps(layout)+'\n')
    print(json.dumps(dict(status='captured',wireguard_and_callbacks=len(executed),native_steps=result['nativeSteps'],
                         services=len(services),entry_bytes=sum(len(b['bytes']) for b in initial['blocks'])+len(coverage),
                         seconds=round(time.monotonic()-started,3))))


if __name__ == '__main__':
    main()
