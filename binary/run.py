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

PIN = 'e033e3dac812a576881a329b2d4c174364f3d44c'
TRACE = 'd1_wrong_receiver_index_same_bucket'
TOOLCHAIN = Path.home() / '.elan/toolchains/leanprover--lean4---v4.35.0/bin'


def bootstrap():
    [lock] = [r for r in json.loads((ROOT / 'dependencies/sources.lock.json').read_text()) if r['name'] == 'kraken']
    if lock['commit'] != PIN or lock['toolchain'] != (ROOT / 'binary/lean-toolchain').read_text().strip():
        raise ValueError('dependency pin or toolchain drift')
    dest = ROOT / '.deps/kraken'
    shared = ROOT.parents[1] / '.deps/kraken'
    if not dest.exists():
        dest.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(shared), str(dest)], check=True)
        subprocess.run(['git', '-C', str(dest), 'switch', '-c', 'task/binary-adequacy', lock['upstream_commit']], check=True)
        for patch in lock['patches']:
            subprocess.run(['git', '-C', str(dest), '-c', 'user.name=Codex',
                            '-c', 'user.email=codex@localhost', 'am', '--committer-date-is-author-date',
                            str(ROOT / patch)], check=True)
    actual = subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != PIN:
        raise ValueError(f'private Kraken commit drift: {actual}')
    # Refuse source drift in the private copy, without consulting/building any
    # shared cache. No shared dependency file is modified.
    data = subprocess.check_output(['git', '-C', str(dest), 'archive', PIN])
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        for member in archive.getmembers():
            if member.isfile():
                if (dest / member.name).read_bytes() != archive.extractfile(member).read():
                    raise ValueError(f'private Kraken source drift: {member.name}')


def checked_command(args, cwd, env=None):
    subprocess.run(args, cwd=cwd, env=env, check=True)


def jsonl(path):
    return [json.loads(s) for s in path.read_text().splitlines()]


def prepare(check, out, trace_name):
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('requires one successful differential trace')
    expected = [s.strip() for s in (ROOT / 'kernel/identity-x86_64-net-choice.txt').read_text().splitlines()
                if s.strip() and not s.startswith('#')][-1]
    if hashlib.sha256(ORACLE.read_bytes()).hexdigest() != expected:
        raise ValueError('oracle image hash mismatch')
    chunk = check / 'chunk-000'
    [trace] = jsonl(chunk / 'model/inputs.jsonl')
    if trace['id'] != trace_name:
        raise ValueError(f'wrong trace: {trace["id"]}')
    service_names = {'__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_cmp4',
                     '__sanitizer_cov_trace_const_cmp4', '__sanitizer_cov_trace_const_cmp1',
                     '__local_bh_enable_ip', 'write_comp_data'}
    functions = extract(ORACLE, service_names)
    f, = [f for f in functions if f['name'] == 'wg_index_hashtable_lookup']
    o = layouts(ORACLE)
    (out / 'layouts.json').write_text(json.dumps(o, indent=2)+'\n')
    entry, node, head, table = [o[n] for n in ('index_hashtable_entry', 'hlist_node', 'hlist_head', 'index_hashtable')]
    offsets = dict(tableSize=table['size'], buckets=table['members']['hashtable'],
                   headSize=head['size'], first=head['members']['first'], entrySize=entry['size'],
                   peer=entry['members']['peer'], hash=entry['members']['index_hash'],
                   next=node['members']['next'], pprev=node['members']['pprev'],
                   kind=entry['members']['type'], index=entry['members']['index'],
                   peerHandshake=o['wg_peer']['members']['handshake'],
                   handshakeEntry=o['noise_handshake']['members']['entry'],
                   keypairEntry=o['noise_keypair']['members']['entry'],
                   peerRefcount=o['wg_peer']['members']['refcount'] +
                     o['kref']['members']['refcount'] + o['refcount_struct']['members']['refs'])
    hooks, labels, instructions = {}, {}, []
    peer_get, = [g for g in functions if g['name'] == 'wg_peer_get_maybe_zero']
    if (f['entry'], f['size'], peer_get['entry'], peer_get['size']) != (
            0xffffffff813a0470, 0xd0, 0xffffffff81399610, 0xfa):
        raise ValueError('raw coverage filter ranges disagree with ELF')
    anchor_rows = f['instructions'] + peer_get['instructions']
    service_rows = [i for g in functions if g['name'] in service_names for i in g['instructions']]
    for i in anchor_rows + service_rows:
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
            if m[1] == 'call' and i in anchor_rows:
                name = re.search(r'<([^>]+)>', i['asm'])[1]
                hooks[target] = name
    allowed = {'__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_cmp4',
               '__sanitizer_cov_trace_const_cmp4', '__sanitizer_cov_trace_const_cmp1',
               '__local_bh_enable_ip', 'wg_peer_get_maybe_zero', 'refcount_warn_saturate'}
    if set(hooks.values()) != allowed:
        raise ValueError(f'call inventory drift: {hooks}')
    hooks = {pc: name for pc, name in hooks.items() if name != 'wg_peer_get_maybe_zero'}
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
    return path, [f, peer_get], chunk


def compare(path, functions, chunk):
    result = json.loads(run(str(ROOT / 'binary/.lake/build/bin/binary-probe'), 'run', str(path)))
    actual = json.loads(run(str(ROOT / 'binary/.lake/build/bin/binary-probe'), 'actual-services', str(path)))
    for key in ('result', 'coverage', 'comparisons', 'decisions', 'mirror_decisions'):
        if actual[key] != result[key]:
            raise ValueError(f'decoded service bodies disagree with summaries: {key}')
    result['actual_service_instructions_executed'] = actual['instructions_executed']
    def in_range(pc):
        return any(f['entry'] < pc <= f['entry'] + f['size'] for f in functions)
    raw = [json.loads(line.removeprefix('LEANUX_BINARY_PCS '))
           for line in (chunk / 'linux/boot.log').read_text().splitlines()
           if line.startswith('LEANUX_BINARY_PCS ')]
    if not raw:
        raise ValueError('raw coverage missing; run a fresh check with the probe guest')
    candidates = []
    for row in raw:
        if row['index'] != 3:
            continue
        pcs = [int(pc, 16) for pc in row['pcs']]
        if not all(in_range(pc) for pc in pcs):
            raise ValueError('raw coverage outside pinned ranges')
        starts = [n for n, pc in enumerate(pcs) if pc == functions[0]['entry'] + 0x19]
        for n in starts:
            # The final trace_pc call is common to every lookup exit. Keep
            # nested peer-get events, without merging task/remote streams.
            end = pcs.index(functions[0]['entry'] + 0x78, n)
            candidates.append(pcs[n:end+1])
    if len(candidates) != 1:
        raise ValueError(f'expected one lookup invocation at operation 3, got {len(candidates)}')
    [kernel_pcs] = candidates
    machine_pcs = result['coverage']
    if machine_pcs != kernel_pcs:
        raise ValueError(f'Kraken/kernel coverage disagreement: Kraken={machine_pcs}, kernel={kernel_pcs}')
    [model] = jsonl(chunk / 'model/model.stdout')
    branches = [b['label'] for b in model['branches'] if b['index'] == 3]
    first = branches.index('wg_index_hashtable_lookup.entry=1')
    decisions = branches[first:first + len(result['decisions'])]
    if decisions != result['decisions']:
        raise ValueError(f'prefix/full-mirror decision disagreement: {result["decisions"]} != {decisions}')
    # Comparison child is an independent execution; it confirms operand values,
    # not an additional ordering claim about the coverage child's execution.
    # Lean serializes a triple as a nested pair.
    machine_cmps = [(pc, a, b) for pc, (a, b) in result['comparisons']]
    cmp_rows = [json.loads(line.removeprefix('LEANUX_BINARY_CMP '))
                for line in (chunk / 'linux/boot.log').read_text().splitlines()
                if line.startswith('LEANUX_BINARY_CMP ')]
    candidates = []
    for row in cmp_rows:
        if row['index'] != 3:
            continue
        records = [(int(r[3], 16), int(r[1], 16), int(r[2], 16)) for r in row['records']]
        if not all(in_range(r[0]) for r in records):
            raise ValueError('raw comparison outside pinned ranges')
        starts = [n for n, r in enumerate(records) if r[0] == machine_cmps[0][0]]
        for first in starts:
            last = next(n for n in range(first, len(records)) if records[n][0] == machine_cmps[-1][0])
            candidates.append(records[first:last+1])
    if len(candidates) != 1:
        raise ValueError(f'expected one raw comparison invocation, got {len(candidates)}')
    [kernel_cmps] = candidates
    if machine_cmps != kernel_cmps:
        raise ValueError(f'Kraken/kernel operand disagreement: {machine_cmps} != {kernel_cmps}')
    result['kernel_coverage'] = kernel_pcs
    result['coverage_comparison'] = 'exact per-invocation sequence, including repetitions and decoded peer-get'
    result['kernel_memory_comparison'] = 'not recorded; memory checked against mirror under explicit entry relation'
    result['check_directory'] = str(chunk.parent)
    print(json.dumps(result, indent=2))
    (path.parent / 'comparison.json').write_text(json.dumps(result, indent=2)+'\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', type=Path, help='reuse a completed check; default makes a fresh recorded run')
    p.add_argument('--trace', choices=[TRACE, 'd1_second_response'], default=TRACE)
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
        shell = f'export PATH="{TOOLCHAIN}:$PATH"; exec python3 -m evaluator.check --suite wireguard --trace {args.trace} --out "$1"'
        checked_command([str(ROOT / 'scripts/in-bundle'), '/bin/sh', '-c', shell, 'binary-tv', str(check)], ROOT, env)
    out = ROOT / '.tmp/binary-tv'
    out.mkdir(parents=True, exist_ok=True)
    path, f, chunk = prepare(check, out, args.trace)
    compare(path, f, chunk)


if __name__ == '__main__':
    main()
