#!/usr/bin/env python3
"""Match a replacement source observation to its same-boot native record cut.

This bounded pilot rejects suspended or nested dispatch contexts. Its input
frontier check never drops passive records or repairs an observed source state.
Run under the project bundle and a memory cap; captures remain ephemeral.
"""
import argparse
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'binary'))
from remediation.replacement_prefix_diagnostic import CompletedPrefixLog, read_word

SECTION_START, SECTION_STOP, RESCHED = 300, 301, 302
CHOICE_MAGIC = 0x4c5a
RECEIVE_WORKER = 'wg_packet_handshake_receive_worker'


def natural(value, label, upper=2**64):
    if type(value) is not int or not 0 <= value < upper:
        raise ValueError(f'{label}: invalid unsigned integer')
    return value


def raw_record(value):
    if type(value) is not list or len(value) != 5:
        raise ValueError('malformed raw hidden record')
    kind, ip, seq, length, payload = value
    natural(kind, 'record kind', 2**16)
    natural(seq, 'record sequence')
    natural(length, 'record length', 2**16)
    if not seq or not isinstance(ip, str) or not re.fullmatch(r'0x[0-9a-f]{1,16}', ip):
        raise ValueError('invalid raw record address or sequence')
    if not isinstance(payload, str) or not re.fullmatch(r'[0-9a-f]*', payload):
        raise ValueError('invalid raw record payload')
    if len(payload) != 2 * min(length, 40):
        raise ValueError('raw record payload length differs')
    return [kind, hex(int(ip, 16)), seq, length, payload]


def section_identity(record):
    if record[0] != SECTION_START or record[3] != 16:
        raise ValueError('invalid dispatch start record')
    payload = bytes.fromhex(record[4])
    return dict(function=int.from_bytes(payload[:8], 'little'),
                unit=int.from_bytes(payload[8:], 'little'), start_sequence=record[2])


def record_provenance(log, trace, count):
    """Retain stream and area-block identities before sorting by sequence."""
    rows = {}
    for line in log.read_text().splitlines():
        for tag, stream in [('LEANUX_HIDDEN ', 'task'), ('LEANUX_RHIDDEN ', 'remote')]:
            if not line.startswith(tag):
                continue
            row = json.loads(line[len(tag):])
            if set(row) != {'id', 'index', 'mode', 'records'} or row['id'] != trace or row['mode'] != 'pc':
                raise ValueError('unexpected provenance record row')
            index = natural(row['index'], 'operation index', count)
            key = index, stream
            if key in rows or type(row['records']) is not list:
                raise ValueError('duplicate or malformed provenance row')
            rows[key] = [raw_record(r) for r in row['records']]
    if set(rows) != {(i, stream) for i in range(count) for stream in ('task', 'remote')}:
        raise ValueError('provenance lacks complete task/remote rows')
    operations = []
    for index in range(count):
        records = []
        for stream in ('task', 'remote'):
            active = None
            for record in rows[index, stream]:
                if record[0] == SECTION_START:
                    if stream != 'remote' or active is not None:
                        raise ValueError('nested or task-stream dispatch block')
                    active = section_identity(record)
                records.append(dict(record=record, stream=stream, dispatch=active))
                if record[0] == SECTION_STOP:
                    if active is None or record[3] != 8 or int.from_bytes(bytes.fromhex(record[4]), 'little'):
                        raise ValueError('unpaired dispatch stop or dropped records')
                    active['stop_sequence'] = record[2]
                    if active['stop_sequence'] <= active['start_sequence']:
                        raise ValueError('dispatch stop precedes its start')
                    active = None
            if active is not None:
                raise ValueError('incomplete dispatch block')
        records.sort(key=lambda row: row['record'][2])
        if len({row['record'][2] for row in records}) != len(records):
            raise ValueError('duplicate operation record sequence')
        operations.append(records)
    return operations


def decode_pc_records(words):
    """Decode the actual KCOV PC-area prefix, retaining every choice record."""
    records, index = [], 0
    while index < len(words):
        header = words[index]
        if header >> 48 != CHOICE_MAGIC:
            index += 1
            continue
        width, length = header & 0xffff, (header >> 32) & 0xffff
        if width > 5 or width != (min(length, 40) + 7) // 8 or index + 3 + width > len(words):
            raise ValueError('malformed native KCOV choice header')
        data = b''.join(word.to_bytes(8, 'little') for word in words[index + 3:index + 3 + width])
        if any(data[min(length, 40):]):
            raise ValueError('nonzero native choice padding')
        records.append(raw_record([(header >> 16) & 0xffff, hex(words[index + 1]),
                                   words[index + 2], length, data[:min(length, 40)].hex()]))
        index += 3 + width
    if any(a[2] >= b[2] for a, b in zip(records, records[1:])):
        raise ValueError('native active-area sequences are not strictly increasing')
    return records


def read_bytes(blocks, address, size):
    values = [bytes(block['bytes'][address - block['address']:address - block['address'] + size])
              for block in blocks if block['address'] <= address and
              address + size <= block['address'] + len(block['bytes'])]
    if not values or any(value != values[0] for value in values[1:]):
        raise ValueError('missing or inconsistent native byte range')
    return values[0]


def native_frontier(snapshot, probe, layout, recording_layout):
    initial, position = snapshot['initial'], snapshot['sourceRecording']
    blocks = initial['blocks']
    pcpu = probe['preempt'] - layout['pcpu_hot']['members']['preempt_count']
    task = read_word(blocks, pcpu + layout['pcpu_hot']['members']['current_task'])
    if task != initial['task'] or not task:
        raise ValueError('native task metadata differs from current_task')
    if not isinstance(position, dict) or set(position) != {'sequenceAddress', 'sequence', 'droppedAddress', 'dropped'}:
        raise ValueError('native entry lacks its recording frontier')
    if position['sequenceAddress'] != recording_layout['sequenceAddress'] or position['droppedAddress'] != task + recording_layout['taskDropped']:
        raise ValueError('native recording addresses differ from pinned layout')
    seq = natural(position['sequence'], 'native sequence')
    if read_word(blocks, position['sequenceAddress']) != seq:
        raise ValueError('native sequence metadata differs from captured bytes')
    if position['dropped'] != 0 or read_word(blocks, position['droppedAddress'], 4) != 0:
        raise ValueError('native entry dropped input records')
    # These task KCOV offsets are the existing pinned capture/decoder ABI.
    if read_word(blocks, task + 0x6e0, 4) != 2:
        raise ValueError('native entry is not in KCOV_TRACE_PC mode')
    capacity, area = read_word(blocks, task + 0x6e4, 4), read_word(blocks, task + 0x6e8)
    used = read_word(blocks, area)
    if not 1 < capacity <= 2**26 or not 0 < used < capacity or not area:
        raise ValueError('invalid native KCOV area bounds')
    if (initial['coverage'], initial['capacity'], initial['coverageUsed'], initial['coverageCapturedWords']) != (area, capacity, used, capacity):
        raise ValueError('native KCOV metadata differs or capture is partial')
    data = read_bytes(blocks, area + 8, used * 8)
    records = decode_pc_records([word[0] for word in struct.iter_unpack('<Q', data)])
    if not records or records[0][0] != SECTION_START:
        raise ValueError('native active area lacks its dispatch start')
    if any(r[0] in (SECTION_START, SECTION_STOP, RESCHED) for r in records[1:]):
        raise ValueError('native active area contains nested, ended or suspended dispatch')
    if records[-1][2] != seq:
        raise ValueError('native active area does not reach the global record frontier')
    return dict(sequence=seq, records=records, dispatch=section_identity(records[0]))


def match_frontier(native, provenance, resolved, observed, dispatch_symbols, operation, ordinal):
    """Match exact suffix and native area; no passive-record normalization."""
    if len(provenance) != len(resolved):
        raise ValueError('resolved records lost raw provenance')
    for raw, source in zip(provenance, resolved):
        if type(source) is not list or len(source) != 2:
            raise ValueError('malformed resolved source record')
        natural(source[0], 'resolved source site')
        payload = raw['record'][4]
        if source[1] != payload + '0' * (-len(payload) % 16):
            raise ValueError('resolved record payload differs from raw provenance')
    consumed = sum(row['record'][2] <= native['sequence'] for row in provenance)
    if not consumed or provenance[consumed - 1]['record'][2] != native['sequence']:
        raise ValueError('native frontier absent from same-boot operation records')
    dispatch = native['dispatch']
    symbol = dispatch_symbols.get(dispatch['function'])
    if symbol != RECEIVE_WORKER or not dispatch['unit']:
        raise ValueError('replacement is outside the bounded receive-worker dispatch')
    active = [row for row in provenance if row['record'][0] == SECTION_START and
              row['dispatch']['start_sequence'] <= native['sequence'] < row['dispatch']['stop_sequence']]
    if len(active) != 1:
        raise ValueError('ambiguous suspended or nested native dispatch context')
    expected = active[0]['dispatch']
    if any(expected[key] != value for key, value in dispatch.items()):
        raise ValueError('native dispatch identity differs from completed boot')
    interval = [row for row in provenance[:consumed] if row['record'][2] >= dispatch['start_sequence']]
    if any(row['dispatch'] != expected or row['record'][0] == RESCHED for row in interval):
        raise ValueError('nested or suspended context within the selected dispatch prefix')
    if [row['record'] for row in interval] != native['records']:
        raise ValueError('captured active-area records differ from same-boot dispatch prefix')
    identity = dict(status='observed', operation=operation, ordinal=ordinal, observation_count=1,
                    unchanged_checkpoints=operation + 1, suspended_count=0, net_rx_section=0)
    if ordinal != 0 or any(observed.get(key) != value for key, value in identity.items()):
        raise ValueError('source observation identity, equality check or dispatch scope differs')
    suffix = [dict(site=row[0], bytes=list(bytes.fromhex(row[1]))) for row in resolved[consumed:]]
    if observed['remaining_records'] != suffix:
        raise ValueError(f'source hidden remainder differs at native frontier after {consumed} records')
    if observed['record_cursor'] != consumed:
        raise ValueError('source record cursor differs from exact native frontier')
    # Worker index 1 is the receive worker; its work unit belongs to the device.
    if [pair for pair in observed['unit_peers'] if pair[0] == dispatch['unit']] != [[dispatch['unit'], [1, 0]]]:
        raise ValueError('source work-unit identity differs from native dispatch')
    return dict(consumed_records=consumed, remaining_records=len(resolved) - consumed,
                native_sequence=native['sequence'], dispatch=dict(dispatch, symbol=symbol),
                active_area_records=len(native['records']))


def validate_capture(snapshot, probe, operation, ordinal, boot):
    natural(operation, 'selected operation', len(probe['trace']['ops']))
    natural(ordinal, 'selected invocation ordinal')
    expected = dict(anchor='replace', executionMode='sequential', recordingMode='pc',
                    selection='operation ordinal', operation=operation, operationCallIndex=ordinal,
                    trace=probe['trace']['id'], completedOperations=list(range(operation)))
    if any(snapshot.get(key) != value for key, value in expected.items()):
        raise ValueError('capture operation, all-call ordinal, trace or trial differs')
    completion = dict(completedOperations=list(range(len(probe['trace']['ops']))), qemuReturncode=0)
    if snapshot.get('postCaptureCompletion') != completion:
        raise ValueError('capture did not finish its complete workload')
    from capture_index_mutator import completed_operations
    lines = boot.read_text().splitlines()
    complete = completed_operations(boot, probe['trace']['id']) == completion['completedOperations']
    batches = [line for line in lines if line.startswith('LEANUX_BATCH_DONE ')]
    exits = [line for line in lines if line.startswith('LEANUX_GUEST_EXIT=')]
    if not complete or batches != ['LEANUX_BATCH_DONE traces=1 failures=0'] or exits != ['LEANUX_GUEST_EXIT=0']:
        raise ValueError('same-boot log lacks successful complete workload')


def run_json(command):
    run = subprocess.run([str(arg) for arg in command], cwd=ROOT, capture_output=True, text=True)
    if run.returncode:
        raise ValueError(f'{Path(command[0]).name} exited {run.returncode}: {run.stderr.strip() or run.stdout.strip()}')
    if run.stderr:
        raise ValueError(f'checker wrote diagnostics: {run.stderr}')
    return json.loads(run.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--capture', type=Path, required=True)
    parser.add_argument('--operation', type=int, required=True)
    parser.add_argument('--call-index', type=int, required=True)
    args = parser.parse_args()
    from pair_capture import source_prefix
    from generate_random_layout import layout_values
    from harness.linux import DISPATCH_SYMBOLS, dispatch_addresses
    from target import ORACLE, pins, verify_image
    from pin import verify_pin
    capture = args.capture.resolve()
    snapshot_path, layout_path = capture / 'snapshot.json', capture / 'layouts.json'
    snapshot = json.loads(snapshot_path.read_text())
    probe = json.loads(args.input.read_text())
    validate_capture(snapshot, probe, args.operation, args.call_index, capture / 'boot.log')
    if snapshot['image_sha256'] != verify_image() or snapshot['kraken'] != verify_pin(ROOT):
        raise ValueError('capture image or semantics pin differs')
    if snapshot['kernel'].get('checked') is not True or any(snapshot['kernel'][key] != pins()[0] for key in ('expected', 'actual')):
        raise ValueError('capture kernel identity differs')
    log = CompletedPrefixLog(capture / 'boot.log', snapshot['trace'], args.operation + 1)
    provenance = record_provenance(log, snapshot['trace'], args.operation + 1)
    replay = source_prefix(dict(probe, operation=args.operation + 1), log)
    native = native_frontier(snapshot, probe, json.loads(layout_path.read_text()), layout_values())
    dispatch = dict(zip(dispatch_addresses(ORACLE.parent), DISPATCH_SYMBOLS))
    # The temporary input is a record-derived source execution, never a heap-derived state.
    with tempfile.TemporaryDirectory(prefix='replacement-source-', dir=capture) as directory:
        path = Path(directory) / 'input.json'
        path.write_text(json.dumps(replay) + '\n')
        binary = ROOT / 'binary/.lake/build/bin'
        observed = run_json([binary / 'binary-replacement-observe', path, args.operation, args.call_index])
        frontier = match_frontier(native, provenance[args.operation],
                                  replay['trace']['hidden'][args.operation], observed, dispatch,
                                  args.operation, args.call_index)
        admitted = run_json([binary / 'binary-replacement-admit', path, snapshot_path,
                             layout_path, args.operation, args.call_index])
        if admitted.get('status') != 'predicate-and-replay-pass':
            raise ValueError('replacement admission did not pass')
    print(json.dumps(dict(status='pass', scope='same-boot replacement entry; sequential native call; WG slice',
                         frontier=frontier, observation=observed, admission=admitted), indent=2))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        raise SystemExit(1)
