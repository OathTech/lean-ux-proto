#!/usr/bin/env python3
"""Compare completed-operation source boundaries with a captured replacement.

This deliberately cannot admit the source cut: the existing mirror runner has
no observer for that intermediate world. Exit 2 means the diagnostic completed
but source-cut admission remains unresolved; other failures exit nonzero too.
Run after capture_index_mutator.py --finish-workload, under the bundle and cap.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'binary'))
from pair_capture import source_prefix
from pin import verify_pin
from target import pins, verify_image


class CompletedPrefixLog:
    """Select original complete record rows; do not synthesize record values."""
    def __init__(self, path, trace, count):
        self.lines = []
        for line in path.read_text().splitlines():
            for tag in ('LEANUX_HIDDEN ', 'LEANUX_RHIDDEN '):
                if line.startswith(tag):
                    row = json.loads(line[len(tag):])
                    if row['id'] != trace or row['mode'] not in ('pc', 'cmp'):
                        raise ValueError('unexpected record trace or mode in completed capture')
                    # The guest later runs a separate comparison-mode trial.
                    # This capture stopped in the earlier PC-mode trial.
                    if row['mode'] == 'pc' and row['index'] < count:
                        self.lines.append(line)

    def read_text(self):
        return '\n'.join(self.lines)


def read_word(blocks, address, size=8):
    found = [bytes(block['bytes'][address-block['address']:address-block['address']+size])
             for block in blocks
             if block['address'] <= address and address+size <= block['address']+len(block['bytes'])]
    if not found:
        raise ValueError(f'missing captured word at {address:#x}, size {size}')
    if any(value != found[0] for value in found[1:]):
        raise ValueError(f'inconsistent overlapping capture blocks at {address:#x}')
    return int.from_bytes(found[0], 'little')


def captured_table(snapshot, endpoint, offsets, layout):
    blocks = snapshot[endpoint]['blocks']
    peers = snapshot['initial']['peers']
    owners = {p['address'] + offsets['peerHandshake'] + offsets['handshakeEntry']:
              ('handshake', bytes(p['publicKey']).hex()) for p in peers}
    internal = layout['noise_keypair']['members']['internal_id']
    keypairs = []
    for address in snapshot['initial']['keypairs']:
        identity = read_word(blocks, address + internal)
        keypairs.append(identity)
        entry = address + offsets['keypairEntry']
        if entry in owners:
            raise ValueError('captured owner allocations alias')
        owners[entry] = ('keypair', identity)
    table = snapshot['initial']['registers']['rdi']
    count = (offsets['tableSize'] - offsets['buckets']) // offsets['headSize']
    if count != 8192:
        raise ValueError('unexpected pinned index table size')
    result, visited = [], set()
    for bucket in range(count):
        link = read_word(blocks, table + offsets['buckets'] + bucket*offsets['headSize'] + offsets['first'])
        while link:
            entry = link - offsets['hash']
            if entry in visited or entry not in owners:
                raise ValueError('cyclic or unidentified captured index owner')
            visited.add(entry)
            kind, owner = owners[entry]
            if read_word(blocks, entry + offsets['kind'], 4) != (1 if kind == 'handshake' else 2):
                raise ValueError('captured owner kind differs from allocation identity')
            index = read_word(blocks, entry + offsets['index'], 4)
            if index % count != bucket:
                raise ValueError('captured index is in the wrong bucket')
            result.append(dict(index=index, kind=kind, owner=owner))
            link = read_word(blocks, entry + offsets['hash'] + offsets['next'])
    return dict(index_table=result, keypair_internal_ids=keypairs)


def source_table(view):
    peers = {p['id']: bytes(p['public_key']).hex() for p in view['peers']}
    keypairs = {k['id']: k['internal_id'] for k in view['keypairs']}
    owners = dict(handshake=peers, keypair=keypairs)
    result = [dict(index=e['index'], kind=e['kind'],
                   owner=owners[e['kind']][e['id']])
              for e in view['index_table']]
    return sorted(result, key=lambda e: e['index'] % 8192)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--capture', type=Path, required=True)
    args = parser.parse_args()
    capture = args.capture.resolve()
    snapshot = json.loads((capture / 'snapshot.json').read_text())
    probe = json.loads(args.input.read_text())
    if snapshot['anchor'] != 'replace' or snapshot['executionMode'] != 'sequential':
        raise ValueError('requires a sequential replacement capture')
    if snapshot['trace'] != probe['trace']['id']:
        raise ValueError('capture and input trace differ')
    completion = snapshot.get('postCaptureCompletion')
    if completion != dict(completedOperations=list(range(len(probe['trace']['ops']))), qemuReturncode=0):
        raise ValueError('capture must finish its workload after preserving the selected return')
    if snapshot['image_sha256'] != verify_image() or snapshot['kraken'] != verify_pin(ROOT):
        raise ValueError('capture image or semantics pin differs')
    if snapshot['kernel'].get('checked') is not True or any(
            snapshot['kernel'][field] != pins()[0] for field in ('expected', 'actual')):
        raise ValueError('capture kernel identity differs')
    operation = snapshot['operation']
    if snapshot['completedOperations'] != list(range(operation)):
        raise ValueError('captured entry has a noncontiguous operation prefix')
    prefix = dict(probe, operation=operation+1)
    prefix = source_prefix(prefix, CompletedPrefixLog(capture / 'boot.log', snapshot['trace'], operation+1))
    with tempfile.TemporaryDirectory(prefix='source-prefix-', dir=capture) as temporary:
        path = Path(temporary) / 'input.json'
        path.write_text(json.dumps(prefix) + '\n')
        run = subprocess.run(['lake', '-d', 'binary', 'env', 'lean', '--run',
                              'binary/remediation/ReplacementPrefixes.lean', str(path), str(operation)],
                             cwd=ROOT, capture_output=True, text=True, check=True)
        if run.stderr:
            raise ValueError(f'source prefix diagnostic wrote stderr: {run.stderr}')
        source = json.loads(run.stdout)
    layout = json.loads((capture / 'layouts.json').read_text())
    entry = captured_table(snapshot, 'initial', probe['offsets'], layout)
    returned = captured_table(snapshot, 'returned', probe['offsets'], layout)
    before, after = source_table(source['before']), source_table(source['after'])
    report = dict(status='unresolved-source-cut', source_cut_observed=False,
                  captured_operation=operation, original_identity_prefix_operation=probe['operation'],
                  source_before=source['before'], source_after=source['after'],
                  captured_entry=entry, captured_return=returned,
                  comparisons=dict(entry_equals_before=entry['index_table'] == before,
                                   entry_equals_after=entry['index_table'] == after,
                                   return_equals_after=returned['index_table'] == after),
                  scope='index projection at completed-operation boundaries; not an observed caller cut or complete source-entry predicate')
    print(json.dumps(report, indent=2))
    return 2


if __name__ == '__main__':
    raise SystemExit(main())
