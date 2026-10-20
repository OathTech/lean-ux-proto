#!/usr/bin/env python3
"""Build and run the retained-heap allowed-IPs mutation experiment."""
import json
import re
import subprocess
import time

from census import extract
from layouts import layouts
from pin import verify_pin
from target import ROOT, ORACLE, verify_image


def prepare(path):
    verify_image()
    verify_pin(ROOT)
    names = ['wg_allowedips_insert_v4', 'wg_allowedips_insert_v6', 'add.isra.0',
             'lookup', 'common_bits', 'wg_peer_get_maybe_zero',
             '__sanitizer_cov_trace_pc', '__sanitizer_cov_trace_cmp1',
             '__sanitizer_cov_trace_const_cmp1', '__sanitizer_cov_trace_const_cmp4',
             '__sanitizer_cov_trace_cmp8', '__local_bh_enable_ip', 'write_comp_data']
    functions = extract(ORACLE, [name for name in names if name not in {'lookup','common_bits','wg_peer_get_maybe_zero'}])
    selected = {}
    for name in names:
        [selected[name]] = [f for f in functions if f['name'] == name]
    rows = [row for f in selected.values() for row in f['instructions']]
    labels = {}
    for row in rows:
        if branch := re.fullmatch(r'(j\w+|call) L_([0-9a-f]+)', row['normalized']):
            raw = bytes.fromhex(row['bytes'])
            width = 1 if len(raw) == 2 else 4
            target = int(branch[2], 16)
            if (row['pc']+len(raw)+int.from_bytes(raw[-width:],'little',signed=True)) % 2**64 != target:
                raise ValueError('branch displacement mismatch')
            labels['L_'+branch[2]] = target
    add = selected['add.isra.0']
    allocations = []
    targets = set()
    for row in add['instructions']:
        if '<kmem_cache_alloc_noprof>' not in row['asm']:
            continue
        [line] = [int(source.rsplit(':',1)[1]) for _,source in row['frames']
                  if '/wireguard/allowedips.c:' in source]
        site = {190:7,205:8,234:9}[line]
        allocations.append((row['pc']+len(bytes.fromhex(row['bytes'])),site))
        targets.add(int(row['normalized'].split('L_')[1],16))
    if len(allocations) != 3 or len(targets) != 1:
        raise ValueError('allocator call inventory changed')
    [alloc] = targets
    [free_row] = [r for r in add['instructions'] if '<kmem_cache_free>' in r['asm']]
    free = int(free_row['normalized'].split('L_')[1],16)
    cache = {int(re.search(r'#\s+([0-9a-f]+)', r['asm'])[1],16)
             for r in add['instructions'] if '<node_cache>' in r['asm']}
    [cache_word] = cache
    [preempt_row] = [r for r in selected['lookup']['instructions'] if '<pcpu_hot+0x8>' in r['asm']]
    preempt = int(re.search(r'#\s+([0-9a-f]+)',preempt_row['asm'])[1],16)
    records = layouts(ORACLE)
    node = records['allowedips_node']; fields = node['members']
    offsets = dict(nodeSize=node['size'],peer=fields['peer'],children=fields['bit'],
                   cidr=fields['cidr'],bitAtA=fields['bit_at_a'],bitAtB=fields['bit_at_b'],
                   bitlen=fields['bitlen'],bits=fields['bits'],
                   peerRefcount=records['wg_peer']['members']['refcount']+
                   records['kref']['members']['refcount']+records['refcount_struct']['members']['refs'])
    lookup = dict(instructions=[dict(pc=r['pc'],size=len(bytes.fromhex(r['bytes'])),asm=r['normalized']) for r in rows],
                  labels=list(labels.items()),hooks=[(f['entry'],name) for name,f in selected.items()
                    if name.startswith('__sanitizer') or name=='__local_bh_enable_ip'],
                  offsets=offsets,entry=selected['lookup']['entry'],commonEntry=selected['common_bits']['entry'],
                  preempt=preempt,entryPreempt=512,budget=100000,trace={},operation=0)
    data = dict(lookup=lookup,insert4=selected['wg_allowedips_insert_v4']['entry'],
                insert6=selected['wg_allowedips_insert_v6']['entry'],add=add['entry'],
                alloc=alloc,free=free,allocationReturns=allocations,
                freeReturn=free_row['pc']+len(bytes.fromhex(free_row['bytes'])),cacheWord=cache_word)
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data)+'\n')


def main():
    path = ROOT/'.tmp/allowedips/mutation.json'
    prepare(path)
    subprocess.run(['lake','-q','build','binary-allowedips-mutation'],cwd=ROOT/'binary',check=True)
    started = time.monotonic()
    result = subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-allowedips-mutation'),str(path)],
                            text=True,capture_output=True)
    (path.parent/'mutation-result.jsonl').write_text(result.stdout)
    if result.returncode:
        print(result.stderr)
        return result.returncode
    rows = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
    if len(rows) != 4 or not result.stdout.endswith('PASS: constructed insertion/lookup sequences; generic allocation/free returns supplied\n'):
        raise ValueError('missing case results or success marker')
    print(json.dumps(dict(status='pass',sequences=len(rows),
                         insertions=sum(len(r['calls']) for r in rows),
                         lookups=sum(len(r['calls']) for r in rows),
                         isolated_root_insertions=sum(len(r['isolatedRootCases']) for r in rows),
                         isolated_root_lookups=sum(len(r['isolatedRootCases']) for r in rows),
                         root_segments=sum(c['insert']['rootSegments'] for r in rows
                                           for c in r['calls']+r['isolatedRootCases']),
                         exact_segments=sum(c['insert']['exactSegments'] for r in rows for c in r['calls']),
                         child_segments=sum(c['insert']['childSegments'] for r in rows for c in r['calls']),
                         child_resources=sum(c['insert']['childResources'] for r in rows for c in r['calls']),
                         select_segments=sum(c['insert']['selectSegments'] for r in rows for c in r['calls']),
                         setup_entries=sum(c['insert']['setupEntries'] for r in rows for c in r['calls']),
                         setup_saves=sum(c['insert']['setupSaves'] for r in rows for c in r['calls']),
                         node_init_segments=sum(c['insert']['nodeInitSegments'] for r in rows for c in r['calls']),
                         return_segments=sum(c['insert']['returnSegments'] for r in rows
                                             for c in r['calls']+r['isolatedRootCases']),
                         seconds=round(time.monotonic()-started,3))))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
