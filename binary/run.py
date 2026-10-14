#!/usr/bin/env python3
"""Run under capped: python3 binary/run.py [--check EXISTING_CHECK_DIRECTORY]."""
import argparse
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile

from census import ROOT, ORACLE, extract, run
from layouts import layouts

PIN = '8af78062037bc237b341d20252aafd1797c1bcb7'
TRACE = 'd1_wrong_receiver_index_same_bucket'
TOOLCHAIN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.35.0/bin'


def bootstrap():
    [lock] = [r for r in json.loads((ROOT / 'dependencies/sources.lock.json').read_text()) if r['name'] == 'kraken']
    if lock['commit'] != PIN or lock['toolchain'] != (ROOT / 'binary/lean-toolchain').read_text().strip():
        raise ValueError('dependency pin or toolchain drift')
    dest = ROOT / '.deps/kraken'
    shared = ROOT.parents[1] / '.deps/kraken'
    if not dest.exists():
        data = subprocess.check_output(['git', '-C', str(shared), 'archive', PIN])
        dest.mkdir(parents=True)
        tarfile.open(fileobj=io.BytesIO(data)).extractall(dest, filter='data')
    # Refuse source drift in the private copy, without consulting/building any
    # shared cache. No shared dependency file is modified.
    data = subprocess.check_output(['git', '-C', str(shared), 'archive', PIN])
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        for member in archive.getmembers():
            if member.isfile():
                if (dest / member.name).read_bytes() != archive.extractfile(member).read():
                    raise ValueError(f'private Kraken source drift: {member.name}')


def checked_command(args, cwd, env=None):
    subprocess.run(args, cwd=cwd, env=env, check=True)


def jsonl(path):
    return [json.loads(s) for s in path.read_text().splitlines()]


def prepare(check, out):
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('requires one successful differential trace')
    expected = [s.strip() for s in (ROOT / 'kernel/identity-x86_64-net-choice.txt').read_text().splitlines()
                if s.strip() and not s.startswith('#')][-1]
    if hashlib.sha256(ORACLE.read_bytes()).hexdigest() != expected:
        raise ValueError('oracle image hash mismatch')
    chunk = check / 'chunk-000'
    [trace] = jsonl(chunk / 'model/inputs.jsonl')
    if trace['id'] != TRACE:
        raise ValueError(f'wrong trace: {trace["id"]}')
    f, = [f for f in extract(ORACLE) if f['name'] == 'wg_index_hashtable_lookup']
    o = layouts(ORACLE)
    (out / 'layouts.json').write_text(json.dumps(o, indent=2)+'\n')
    entry, node, head, table = [o[n] for n in ('index_hashtable_entry', 'hlist_node', 'hlist_head', 'index_hashtable')]
    offsets = dict(tableSize=table['size'], buckets=table['members']['hashtable'],
                   headSize=head['size'], first=head['members']['first'], entrySize=entry['size'],
                   peer=entry['members']['peer'], hash=entry['members']['index_hash'],
                   next=node['members']['next'], pprev=node['members']['pprev'],
                   kind=entry['members']['type'], index=entry['members']['index'])
    hooks, labels, instructions = {}, {}, []
    for i in f['instructions']:
        pc, size, asm = i['pc'], len(bytes.fromhex(i['bytes'])), i['normalized']
        instructions.append(dict(pc=pc, size=size, asm=asm))
        if m := re.match(r'(j\w+|call)\s+L_([0-9a-f]+)$', asm):
            target = int(m[2], 16)
            labels['L_' + m[2]] = target
            # Check the printed target against the actual instruction's rel8/rel32.
            raw = bytes.fromhex(i['bytes'])
            width = 1 if len(raw) == 2 else 4
            if (pc + size + int.from_bytes(raw[-width:], 'little', signed=True)) % 2**64 != target:
                raise ValueError('disassembly branch displacement mismatch')
            if m[1] == 'call':
                name = re.search(r'<([^>]+)>', i['asm'])[1]
                hooks[target] = name
    allowed = {'__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_cmp4',
               '__sanitizer_cov_trace_const_cmp4', '__local_bh_enable_ip', 'wg_peer_get_maybe_zero'}
    if set(hooks.values()) != allowed:
        raise ValueError(f'call inventory drift: {hooks}')
    # Resolve the actual RIP target and check the anonymous-struct DWARF offset.
    if o['pcpu_hot']['members']['preempt_count'] != 8:
        raise ValueError('pcpu_hot.preempt_count layout drift')
    preempt_rows = [i for i in f['instructions'] if '<pcpu_hot+0x8>' in i['asm']]
    [preempt_row] = preempt_rows
    preempt = int(re.search(r'#\s+([0-9a-f]+)', preempt_row['asm'])[1], 16)
    operation = trace['ops'][3]
    message = bytes.fromhex(operation['message'])
    if operation['op'] != 'wg_inject' or len(message) != 92 or message[:4] != b'\x02\0\0\0':
        raise ValueError('probe expects a handshake response at operation 3')
    query = int.from_bytes(message[8:12], 'little')
    data = dict(instructions=instructions, labels=list(labels.items()), hooks=list(hooks.items()),
                offsets=offsets, preempt=preempt, trace=trace, operation=3, query=query)
    path = out / 'input.json'
    path.write_text(json.dumps(data)+'\n')
    return path, f, chunk


def compare(path, f, chunk):
    result = json.loads(run(str(ROOT / 'binary/.lake/build/bin/binary-probe'), 'run', str(path)))
    coverage, = [r for r in jsonl(chunk / 'linux/coverage.jsonl') if r['index'] == 3]
    low, high = f['entry'], f['entry'] + f['size']
    kernel_pcs = [int(pc, 16) for pc in coverage['pcs'] if low < int(pc, 16) <= high]
    machine_pcs = result['coverage']
    if len(machine_pcs) != len(set(machine_pcs)):
        raise ValueError('recorded KCOV cannot check repeated coverage points exactly')
    if machine_pcs != kernel_pcs:
        raise ValueError(f'Kraken/kernel coverage disagreement: Kraken={machine_pcs}, kernel={kernel_pcs}')
    [model] = jsonl(chunk / 'model/model.stdout')
    decisions = [b['label'] for b in model['branches'] if b['index'] == 3 and
                 b['label'].startswith('wg_index_hashtable_lookup.')]
    if decisions != result['decisions']:
        raise ValueError(f'prefix/full-mirror decision disagreement: {result["decisions"]} != {decisions}')
    # Comparison child is an independent execution; it confirms operand values,
    # not an additional ordering claim about the coverage child's execution.
    comparisons, = [r for r in jsonl(chunk / 'linux/comparisons.jsonl') if r['index'] == 3]
    kernel_cmps = [(int(r[3], 16), int(r[1], 16), int(r[2], 16)) for r in comparisons['records']
                   if low < int(r[3], 16) <= high]
    # Lean serializes a triple as a nested pair.
    machine_cmps = [(pc, a, b) for pc, (a, b) in result['comparisons']]
    if machine_cmps != kernel_cmps:
        raise ValueError(f'Kraken/kernel operand disagreement: {machine_cmps} != {kernel_cmps}')
    result['kernel_coverage'] = kernel_pcs
    result['coverage_comparison'] = 'exact sequence of instrumented block entries on this nonrepeating path'
    result['kernel_memory_comparison'] = 'not recorded; memory checked against mirror under explicit entry relation'
    result['check_directory'] = str(chunk.parent)
    print(json.dumps(result, indent=2))
    (path.parent / 'comparison.json').write_text(json.dumps(result, indent=2)+'\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', type=Path, help='reuse a completed check; default makes a fresh recorded run')
    args = p.parse_args()
    bootstrap()
    checked_command([str(TOOLCHAIN / 'lake'), 'build', 'binary-probe'], ROOT / 'binary')
    if args.check:
        check = args.check.resolve()
    else:
        stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S')
        check = ROOT / '.artifacts/check' / ('binary-tv-' + stamp)
        # The bundle fixes tools and guest libraries. Prepend this package's
        # Lean afterwards, so the check's freshness test uses the same version.
        env = dict(os.environ, LEANUX_KERNEL_DIR=str(ORACLE.parent))
        shell = f'export PATH="{TOOLCHAIN}:$PATH"; exec python3 -m evaluator.check --suite wireguard --trace {TRACE} --out "$1"'
        checked_command([str(ROOT / 'scripts/in-bundle'), '/bin/sh', '-c', shell, 'binary-tv', str(check)], ROOT, env)
    out = ROOT / '.tmp/binary-tv'
    out.mkdir(parents=True, exist_ok=True)
    path, f, chunk = prepare(check, out)
    compare(path, f, chunk)


if __name__ == '__main__':
    main()
