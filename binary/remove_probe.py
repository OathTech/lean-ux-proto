#!/usr/bin/env python3
"""Paired removal calibration; run through capped after an index-remove check.

Entry heaps are materialized from the recorded prefix, not captured snapshots.
The independent kernel coverage and mirror decisions remain comparison channels.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import time

from target import verify_image, kernel_environment
from census import ROOT, ORACLE, extract
from layouts import layouts
from pin import verify_pin


def prepare(check, out, name='wg_index_hashtable_remove', operation=4,
            workload='c_remove_after_handshake'):
    verify_pin(ROOT)
    report = json.loads((check / 'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('requires one passing mutator-profile recording')
    verify_image()
    chunk = check / 'chunk-000'
    [trace] = [json.loads(s) for s in (chunk / 'model/inputs.jsonl').read_text().splitlines()]
    if trace['id'] != workload:
        raise ValueError('wrong mutator workload')
    services = {'__sanitizer_cov_trace_pc', '__local_bh_enable_ip'}
    if name == 'wg_index_hashtable_insert':
        services.add('__sanitizer_cov_trace_cmp4')
    service_bodies = services | ({'write_comp_data'} if name == 'wg_index_hashtable_insert' else set())
    functions = extract(ORACLE, service_bodies)
    [anchor] = [f for f in functions if f['name'] == name]
    if name == 'wg_index_hashtable_remove':
        if anchor['entry'] != 0xffffffff813a0600:
            raise ValueError('removal entry differs from the pinned Lean definition')
        stores = [i for i in anchor['instructions'] if i['pc'] - anchor['entry'] in (0x24, 0x28, 0x40)]
        if [(i['pc'] - anchor['entry'], bytes.fromhex(i['bytes']).hex()) for i in stores] != [
                (0x24, '4c8b6308'), (0x28, '4c896500'), (0x40, '48c7431000000000')]:
            raise ValueError('fresh symbolic removal regions differ from image bytes')
    elif name == 'wg_index_hashtable_replace':
        if anchor['entry'] != 0xffffffff813a0550 or len(anchor['instructions']) != 41:
            raise ValueError('replacement anchor differs from the pinned image')
    elif name == 'wg_index_hashtable_insert':
        if anchor['entry'] != 0xffffffff813a03a0 or len(anchor['instructions']) != 109:
            raise ValueError('insertion anchor differs from the pinned image')
    else:
        raise ValueError('unknown mutator anchor')
    provenance = json.loads((chunk / 'linux/provenance.json').read_text())
    if provenance['binary_coverage_ranges'] != [dict(symbol=anchor['name'], lo=anchor['entry'],
                                                    hi=anchor['entry'] + anchor['size'])]:
        raise ValueError('recording has a different coverage profile')
    o = layouts(ORACLE)
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
    instructions, labels = [], {}
    for function in [anchor] + [f for f in functions if f['name'] in service_bodies]:
        for insn in function['instructions']:
            raw, pc, asm = bytes.fromhex(insn['bytes']), insn['pc'], insn['normalized']
            instructions.append(dict(pc=pc, size=len(raw), asm=asm))
            if match := re.match(r'(j\w+|call)\s+L_([0-9a-f]+)$', asm):
                target = int(match[2], 16)
                width = 1 if len(raw) == 2 else 4
                if (pc + len(raw) + int.from_bytes(raw[-width:], 'little', signed=True)) % 2**64 != target:
                    raise ValueError('relative branch displacement differs')
                labels['L_' + match[2]] = target
    hooks = [(f['entry'], f['name']) for f in functions if f['name'] in services]
    [preempt] = {int(re.search(r'#\s+([0-9a-f]+)', i['asm'])[1], 16)
                 for i in anchor['instructions'] if '<pcpu_hot+0x8>' in i['asm']}
    out.mkdir(parents=True, exist_ok=True)
    path = out / 'input.json'
    path.write_text(json.dumps(dict(instructions=instructions, labels=list(labels.items()), hooks=hooks,
                                   offsets=offsets, preempt=preempt, trace=trace, operation=operation, query=0)) + '\n')
    return path, chunk


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', type=Path, required=True)
    args = parser.parse_args()
    out = ROOT / '.tmp/binary-remove'
    path, chunk = prepare(args.check.resolve(), out)
    started = time.monotonic()
    completed = subprocess.run([str(ROOT / 'binary/.lake/build/bin/binary-pair-remove'), str(path)],
                               capture_output=True, text=True, check=True)
    if completed.stderr:
        raise ValueError(completed.stderr)
    result = json.loads(completed.stdout)
    rows = [json.loads(line.removeprefix('LEANUX_BINARY_PCS '))
            for line in (chunk / 'linux/boot.log').read_text().splitlines()
            if line.startswith('LEANUX_BINARY_PCS ')]
    [kernel] = [r for r in rows if r['index'] == 4 and r['stream'] == 'task']
    kernel_pcs = [int(pc, 16) for pc in kernel['pcs']]
    [model] = [json.loads(s) for s in (chunk / 'model/model.stdout').read_text().splitlines()]
    decisions = [b['label'] for b in model['branches'] if b['index'] == 4 and
                 b['label'].startswith('wg_index_hashtable_remove.entry_hashed=')]
    for run in result['cases'][0]['runs']:
        actual = [pc for call in run['calls'] for pc in call['coverage']]
        source = [f'wg_index_hashtable_remove.entry_hashed={int(call["hashed"])}' for call in run['calls']]
        if actual != kernel_pcs or source != decisions:
            raise ValueError(f'three-way removal mismatch: {actual}, {kernel_pcs}, {source}, {decisions}')
    result.update(three_way='pass',
                  comparison_scope='selected removal calls; arguments derived from source call order, not captured; intervening callers are not executed',
                  kernel_coverage=kernel_pcs, mirror_decisions=decisions,
                  paired_seconds=round(time.monotonic() - started, 3))
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
