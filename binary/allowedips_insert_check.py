#!/usr/bin/env python3
"""Three-way insertion comparison on b1_trie_routing's recorded configuration."""
import argparse
import json
from pathlib import Path
import subprocess
import time

from allowedips_mutation import prepare
from target import ROOT


def one_jsonl(path):
    [value] = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',type=Path,required=True)
    args = parser.parse_args()
    check = args.check.resolve()
    report = json.loads((check/'report.json').read_text())
    if report['status'] != 'pass' or report['traces'] != 1:
        raise ValueError('requires one successful full differential trace')
    chunk = check/'chunk-000'
    trace = one_jsonl(chunk/'model/inputs.jsonl')
    if trace['id'] != 'b1_trie_routing' or trace['ops'][0]['op'] != 'wg_set':
        raise ValueError('wrong trace/operation')
    provenance = json.loads((chunk/'linux/provenance.json').read_text())
    ranges = provenance['binary_coverage_ranges']
    if {r['symbol'] for r in ranges} != {'wg_allowedips_insert_v4','wg_allowedips_insert_v6','add.isra.0','common_bits'}:
        raise ValueError('wrong capture profile')
    out = ROOT/'.tmp/allowedips'
    prepare(out/'mutation.json')
    peers = trace['ops'][0]['config']['peers']
    calls = [[a['family'],[int(a['addr'],16),[a['cidr'],pid]]]
             for pid,p in enumerate(peers) for a in p['allowed_ips']]
    (out/'recorded.json').write_text(json.dumps(dict(trace=trace,calls=calls,peerCount=len(peers)))+'\n')
    subprocess.run(['lake','-q','build','binary-allowedips-mutation'],cwd=ROOT/'binary',check=True)
    start = time.monotonic()
    result = subprocess.run([str(ROOT/'binary/.lake/build/bin/binary-allowedips-mutation'),
                             str(out/'mutation.json'),str(out/'recorded.json')],text=True,capture_output=True)
    if result.returncode or result.stderr:
        raise RuntimeError(f'paired recorded execution failed: {result.returncode}: {result.stderr}')
    runs = [json.loads(line) for line in result.stdout.splitlines()]
    if len(runs) != 2 or any(len(r['calls']) != len(calls) for r in runs):
        raise ValueError('missing paired cases')
    log = (chunk/'linux/boot.log').read_text().splitlines()
    def captured(prefix):
        rows = [json.loads(line[len(prefix):]) for line in log if line.startswith(prefix)]
        [row] = [r for r in rows if r['id']==trace['id'] and r['index']==0 and r['stream']=='task']
        return row
    pcs = [int(p,16) for p in captured('LEANUX_BINARY_PCS ')['pcs']]
    cmps = [(int(r[3],16),int(r[1],16),int(r[2],16))
            for r in captured('LEANUX_BINARY_CMP ')['records']]
    if not all(any(r['lo'] < pc <= r['hi'] for r in ranges) for pc in pcs):
        raise ValueError('capture outside declared ranges')
    model = one_jsonl(chunk/'model/model.stdout')
    prefixes = ('add.','node_placement.','common_bits.','fls128.')
    decisions = [b['label'] for b in model['branches'] if b['index']==0 and not b.get('section',0)
                 and b['label'].startswith(prefixes)]
    for run in runs:
        actual = [pc for call in run['calls'] for pc in call['coverage']]
        actual_cmps = [(pc,a,b) for call in run['calls'] for pc,(a,b) in call['comparisons']]
        source = [d for call in run['calls'] for d in call['decisions']]
        if actual != pcs:
            raise ValueError(f'Kraken/kernel coverage differs: {actual} != {pcs}')
        if actual_cmps != cmps:
            raise ValueError(f'Kraken/kernel comparison operands differ: {actual_cmps} != {cmps}')
        if source != decisions:
            raise ValueError(f'paired/full mirror decisions differ: {source} != {decisions}')
    (out/'recorded-result.json').write_text(json.dumps(runs)+'\n')
    print(json.dumps(dict(status='pass',three_way='pass',calls=len(calls),seeds=len(runs),
                         coverage=len(pcs),comparisons=len(cmps),decisions=len(decisions),
                         seconds=round(time.monotonic()-start,3),
                         origin='recorded call arguments/outcomes; constructed empty table and peers',
                         services='supplied allocator/free interface returns')))


if __name__ == '__main__':
    main()
