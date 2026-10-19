#!/usr/bin/env python3
"""Concrete allowedips three-way test; invoke through capped. No proof claim."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shlex

from target import verify_image, kernel_environment
from census import ROOT, ORACLE, extract, run
from layouts import layouts
from run import bootstrap, checked_command, jsonl, TOOLCHAIN

TRACE = 'b1_trie_routing'


def prepare(check, out, operation, budget):
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('requires one successful differential trace')
    verify_image()
    chunk = check / 'chunk-000'
    [trace] = jsonl(chunk / 'model/inputs.jsonl')
    if trace['id'] != TRACE or trace['ops'][operation]['op'] != 'wg_xmit':
        raise ValueError('wrong recorded allowedips trace/operation')
    services = {'__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_const_cmp1',
                '__sanitizer_cov_trace_const_cmp4', '__sanitizer_cov_trace_cmp1',
                '__sanitizer_cov_trace_cmp8', '__local_bh_enable_ip', 'write_comp_data'}
    functions = extract(ORACLE, services)
    # extract validates WireGuard DWARF attribution, distinguishing the two
    # local ELF symbols named lookup. No address is guessed from its name.
    anchors = []
    for name in ('lookup', 'common_bits', 'wg_peer_get_maybe_zero'):
        [function] = [f for f in functions if f['name'] == name]
        anchors.append(function)
    lookup, common, peer = anchors
    provenance = json.loads((chunk / 'linux/provenance.json').read_text())
    ranges = {(r['symbol'], r['lo'], r['hi']) for r in provenance.get('binary_coverage_ranges', [])}
    if ranges != {(f['name'], f['entry'], f['entry'] + f['size']) for f in anchors}:
        raise ValueError('recording does not have the allowedips ELF-derived capture profile')
    o = layouts(ORACLE)
    node = o['allowedips_node']
    fields = node['members']
    offsets = dict(nodeSize=node['size'], peer=fields['peer'], children=fields['bit'],
                   cidr=fields['cidr'], bitAtA=fields['bit_at_a'], bitAtB=fields['bit_at_b'],
                   bitlen=fields['bitlen'], bits=fields['bits'],
                   peerRefcount=o['wg_peer']['members']['refcount'] +
                     o['kref']['members']['refcount'] + o['refcount_struct']['members']['refs'])
    instructions, labels, hooks = [], {}, {}
    anchor_rows = [i for f in anchors for i in f['instructions']]
    rows = anchor_rows + [i for f in functions if f['name'] in services for i in f['instructions']]
    for i in rows:
        pc, raw, asm = i['pc'], bytes.fromhex(i['bytes']), i['normalized']
        instructions.append(dict(pc=pc, size=len(raw), asm=asm))
        if m := re.match(r'(j\w+|call)\s+L_([0-9a-f]+)$', asm):
            target = int(m[2], 16)
            labels['L_' + m[2]] = target
            width = 1 if len(raw) == 2 else 4
            if (pc + len(raw) + int.from_bytes(raw[-width:], 'little', signed=True)) % 2**64 != target:
                raise ValueError(f'branch displacement mismatch at {pc:x}')
            if m[1] == 'call' and i in anchor_rows:
                hooks[target] = re.search(r'<([^>]+)>', i['asm'])[1]
    expected_calls = (services - {'write_comp_data'}) | {'common_bits', 'wg_peer_get_maybe_zero', 'refcount_warn_saturate'}
    if set(hooks.values()) != expected_calls:
        raise ValueError(f'allowedips call inventory drift: {hooks}')
    hooks = {pc: name for pc, name in hooks.items() if name not in {'common_bits', 'wg_peer_get_maybe_zero'}}
    [preempt_row] = [i for i in lookup['instructions'] if '<pcpu_hot+0x8>' in i['asm']]
    preempt = int(re.search(r'#\s+([0-9a-f]+)', preempt_row['asm'])[1], 16)
    if o['pcpu_hot']['members']['preempt_count'] != 8:
        raise ValueError('preempt-count DWARF drift')
    data = dict(instructions=instructions, labels=list(labels.items()), hooks=list(hooks.items()),
                offsets=offsets, entry=lookup['entry'], commonEntry=common['entry'], preempt=preempt,
                entryPreempt=512, budget=budget, trace=trace, operation=operation)
    path = out / f'input-{operation}.json'
    path.write_text(json.dumps(data) + '\n')
    return path, anchors, chunk


def compare(path, anchors, chunk, operation):
    result = json.loads(run(str(ROOT / 'binary/.lake/build/bin/binary-probe'), 'allowedips', str(path)))
    lookup, _, peer = anchors
    def inside(pc):
        return any(f['entry'] < pc <= f['entry'] + f['size'] for f in anchors)
    lines = (chunk / 'linux/boot.log').read_text().splitlines()
    def records(prefix):
        rows = [json.loads(line.removeprefix(prefix)) for line in lines if line.startswith(prefix)]
        selected = [r for r in rows if r['id'] == TRACE and r['index'] == operation and r['stream'] == 'task']
        if len(selected) != 1:
            raise ValueError(f'expected exactly one task capture for operation {operation}, got {len(selected)}')
        return selected[0]
    pcs = [int(pc, 16) for pc in records('LEANUX_BINARY_PCS ')['pcs']]
    if not all(inside(pc) for pc in pcs):
        raise ValueError('coverage outside declared allowedips ranges')
    starts = [i for i, pc in enumerate(pcs) if pc == lookup['entry'] + 0x20]
    if len(starts) != 1:
        raise ValueError(f'expected one allowedips invocation, got {len(starts)}')
    start = starts[0]
    finish = pcs.index(lookup['entry'] + 0x12b, start)
    kernel_pcs = pcs[start:finish + 1]
    if result['coverage'] != kernel_pcs:
        raise ValueError(f'Kraken/kernel coverage mismatch: {result["coverage"]} != {kernel_pcs}')
    cmps = [(int(r[3], 16), int(r[1], 16), int(r[2], 16))
            for r in records('LEANUX_BINARY_CMP ')['records']]
    if not all(inside(pc) for pc, _, _ in cmps):
        raise ValueError('comparison outside declared allowedips ranges')
    machine_cmps = [(pc, a, b) for pc, (a, b) in result['comparisons']]
    # Both selected cases finish with one live peer-get. Its final compare
    # delimits this invocation in the independently captured comparison run.
    if not machine_cmps or machine_cmps[0][0] != lookup['entry'] + 0x3e or machine_cmps[-1][0] != peer['entry'] + 0x9d:
        raise ValueError('selected probe is not the expected live helper path')
    starts = [i for i, r in enumerate(cmps) if r[0] == lookup['entry'] + 0x3e]
    if len(starts) != 1:
        raise ValueError('comparison run has other than one allowedips invocation')
    start = starts[0]
    finish = next(i for i in range(start, len(cmps)) if cmps[i][0] == peer['entry'] + 0x9d)
    kernel_cmps = cmps[start:finish + 1]
    if machine_cmps != kernel_cmps:
        raise ValueError(f'Kraken/kernel comparison mismatch: {machine_cmps} != {kernel_cmps}')
    [model] = jsonl(chunk / 'model/model.stdout')
    branches = [b['label'] for b in model['branches'] if b['index'] == operation and not b.get('section', 0)]
    starts = [i for i, label in enumerate(branches) if label.startswith('swap_endian.bits_32=')]
    if len(starts) != 1:
        raise ValueError('source operation has other than one allowedips invocation')
    source = branches[starts[0]:starts[0] + len(result['decisions'])]
    if source != result['decisions'] or source[-1] != 'lookup.peer_gone=0':
        raise ValueError(f'prefix/full-source decision mismatch: {source} != {result["decisions"]}')
    result.update(kernel_coverage=kernel_pcs, kernel_comparisons=kernel_cmps,
                  check_directory=str(chunk.parent),
                  state_origin='recorded-prefix mirror read projection; synthetic addresses, stack and preempt baseline')
    (path.parent / f'comparison-{operation}.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(operation=operation, status='pass', result=result['result'],
                         instructions=result['instructions_executed'], decisions=len(source),
                         coverage=len(kernel_pcs), comparisons=len(kernel_cmps))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', type=Path, help='reuse an allowedips-profile differential recording')
    parser.add_argument('--operation', type=int, choices=[5, 8], action='append')
    parser.add_argument('--budget', type=int, default=10000)
    args = parser.parse_args()
    if not 0 < args.budget <= 100000:
        parser.error('budget must be 1..100000')
    bootstrap()
    checked_command([str(TOOLCHAIN / 'lake'), 'build', 'binary-probe'], ROOT / 'binary')
    if args.check:
        check = args.check.resolve()
    else:
        stamp = datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S-%f')
        check = ROOT / '.artifacts/check' / ('binary-allowedips-' + stamp)
        env = kernel_environment()
        shell = f'export PATH={shlex.quote(str(TOOLCHAIN))}:"$PATH"; exec python3 -m evaluator.check --suite wireguard --binary-coverage --binary-profile allowedips --trace {TRACE} --out "$1"'
        checked_command([str(ROOT / 'scripts/in-bundle'), '/bin/sh', '-c', shell, 'binary-allowedips', str(check)], ROOT, env)
    out = ROOT / '.tmp/binary-allowedips'
    out.mkdir(parents=True, exist_ok=True)
    for operation in args.operation or [5, 8]:
        path, anchors, chunk = prepare(check, out, operation, args.budget)
        compare(path, anchors, chunk, operation)


if __name__ == '__main__':
    main()
