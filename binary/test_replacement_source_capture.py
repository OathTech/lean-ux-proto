"""A native record cut must match independently observed source execution."""
import copy
import json
import unittest

from remediation.replacement_source_capture import (
    CHOICE_MAGIC, RECEIVE_WORKER, decode_pc_records, match_frontier,
    native_frontier, record_provenance, section_identity,
)


def record(kind, seq, values):
    payload = b''.join(value.to_bytes(8, 'little') for value in values)
    return [kind, '0x1234', seq, len(payload), payload.hex()]


def words(raw):
    kind, ip, seq, length, data = raw
    payload = bytes.fromhex(data)
    return [(CHOICE_MAGIC << 48) | (length << 32) | (kind << 16) | (length // 8),
            int(ip, 16), seq] + [int.from_bytes(payload[i:i+8], 'little') for i in range(0, length, 8)]


class Log:
    def __init__(self, task, remote):
        self.rows = [('LEANUX_HIDDEN ', task), ('LEANUX_RHIDDEN ', remote)]

    def read_text(self):
        return '\n'.join(tag + json.dumps(dict(id='sample', index=0, mode='pc', records=rows))
                         for tag, rows in self.rows)


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.start = record(300, 10, [0x5000, 0x6000])
        self.draw = record(1, 11, [17])
        self.tail = record(200, 12, [42])
        self.stop = record(301, 13, [0])
        self.raw = [self.start, self.draw, self.tail, self.stop]
        self.provenance = record_provenance(Log([], self.raw), 'sample', 1)[0]
        self.resolved = [[site, raw[4]] for site, raw in enumerate(self.raw)]
        self.native = dict(sequence=11, records=self.raw[:2], dispatch=section_identity(self.start))
        self.observed = dict(status='observed', operation=0, ordinal=0, observation_count=1,
                             unchanged_checkpoints=1, suspended_count=0, net_rx_section=0,
                             record_cursor=2, unit_peers=[[0x6000, [1, 0]]],
                             remaining_records=[dict(site=site, bytes=list(bytes.fromhex(payload)))
                                                for site, payload in self.resolved[2:]])

    def match(self):
        return match_frontier(self.native, self.provenance, self.resolved, self.observed,
                              {0x5000: RECEIVE_WORKER}, 0, 0)

    def test_exact_frontier(self):
        result = self.match()
        self.assertEqual((result['consumed_records'], result['remaining_records']), (2, 2))
        self.assertEqual(result['dispatch']['start_sequence'], 10)

    def test_suffix_is_not_repaired_or_passive_records_dropped(self):
        self.observed['remaining_records'] = self.observed['remaining_records'][1:]
        with self.assertRaisesRegex(ValueError, 'hidden remainder differs'):
            self.match()

    def test_same_length_changed_suffix_rejected(self):
        self.observed['remaining_records'][0]['bytes'][0] += 1
        with self.assertRaisesRegex(ValueError, 'hidden remainder differs'):
            self.match()

    def test_changed_frontier_or_unit_rejected(self):
        self.native['sequence'] = 9
        with self.assertRaisesRegex(ValueError, 'frontier absent'):
            self.match()
        self.native['sequence'] = 11
        self.observed['unit_peers'][0][0] += 1
        with self.assertRaisesRegex(ValueError, 'work-unit identity'):
            self.match()

    def test_active_bytes_must_match_boot_log(self):
        self.native['records'] = copy.deepcopy(self.native['records'])
        self.native['records'][1][4] = '00' * 8
        with self.assertRaisesRegex(ValueError, 'active-area records differ'):
            self.match()

    def test_resolved_payload_keeps_its_raw_provenance(self):
        self.resolved[0][1] = '00' * 16
        with self.assertRaisesRegex(ValueError, 'payload differs from raw provenance'):
            self.match()

    def test_suspended_source_rejected(self):
        self.observed['suspended_count'] = 1
        with self.assertRaisesRegex(ValueError, 'dispatch scope'):
            self.match()

    def test_overlapping_dispatch_rejected(self):
        other = [record(300, 8, [0x7000, 0x8000]), record(301, 14, [0])]
        self.provenance = record_provenance(Log([], self.raw + other), 'sample', 1)[0]
        self.resolved = [[i, row['record'][4]] for i, row in enumerate(self.provenance)]
        with self.assertRaisesRegex(ValueError, 'ambiguous suspended or nested'):
            self.match()

    def test_duplicate_sequences_and_dropped_stop_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate operation record'):
            record_provenance(Log([self.draw], self.raw), 'sample', 1)
        with self.assertRaisesRegex(ValueError, 'dropped records'):
            record_provenance(Log([], self.raw[:-1] + [record(301, 13, [1])]), 'sample', 1)

    def test_native_decoder_skips_pcs_but_preserves_records(self):
        self.assertEqual(decode_pc_records([0xffffffff813a0000] + words(self.start) +
                                          [0xffffffff813a0008] + words(self.draw)), self.raw[:2])

    def test_native_decoder_rejects_truncated_or_wrong_width(self):
        with self.assertRaisesRegex(ValueError, 'malformed native'):
            decode_pc_records(words(self.start)[:-1])
        bad = words(self.start)
        bad[0] += 1
        with self.assertRaisesRegex(ValueError, 'malformed native'):
            decode_pc_records(bad)

    def test_native_frontier_comes_from_pinned_addresses_and_bytes(self):
        def block(address, value, width=8):
            return dict(address=address, bytes=list(value.to_bytes(width, 'little')))
        area = words(self.start) + words(self.draw)
        snapshot = dict(sourceRecording=dict(sequenceAddress=0x9000, sequence=11,
                                             droppedAddress=0x2704, dropped=0),
                        initial=dict(task=0x2000, coverage=0x4000, capacity=100,
                                     coverageUsed=len(area), coverageCapturedWords=100,
                                     blocks=[block(0x1000, 0x2000), block(0x9000, 11), block(0x2704, 0, 4),
                                             block(0x26e0, 2, 4), block(0x26e4, 100, 4), block(0x26e8, 0x4000),
                                             dict(address=0x4000, bytes=list(b''.join(
                                                 value.to_bytes(8, 'little') for value in [len(area)] + area)))]))
        probe, layout = dict(preempt=0x1000), dict(pcpu_hot=dict(members=dict(preempt_count=0, current_task=0)))
        rec = dict(sequenceAddress=0x9000, taskDropped=0x704)
        self.assertEqual(native_frontier(snapshot, probe, layout, rec), self.native)
        snapshot['sourceRecording']['sequence'] = 12
        with self.assertRaisesRegex(ValueError, 'metadata differs from captured bytes'):
            native_frontier(snapshot, probe, layout, rec)
        snapshot['sourceRecording']['sequence'] = 11
        snapshot['sourceRecording']['sequenceAddress'] = 0x9008
        with self.assertRaisesRegex(ValueError, 'addresses differ'):
            native_frontier(snapshot, probe, layout, rec)
        snapshot['sourceRecording']['sequenceAddress'] = 0x9000
        snapshot['sourceRecording']['dropped'] = 1
        with self.assertRaisesRegex(ValueError, 'dropped input records'):
            native_frontier(snapshot, probe, layout, rec)


if __name__ == '__main__':
    unittest.main()
