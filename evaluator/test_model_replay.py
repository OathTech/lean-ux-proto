"""Replays of recorded hidden inputs through the built mirror (no guest).

Run after `lake build leanux-model` (the check builds it):
    scripts/in-bundle python3 -B -m unittest evaluator.test_model_replay
A missing binary fails the tests; it does not skip them.

The decrypt worker's NAPI poll placement (Leanux/Env.lean, `napiIrqExit`): a
poll the records place right after the enqueue may have run inside it, holding
the enqueue's peer reference; the mirror reports such polls and takes the
placement as an input, which the check enumerates.

The loopback NET_RX rule (Leanux/WG/State.lean, `loopbackSend`): a transmission
over loopback raises NET_RX, whose section runs nested at the send's
`local_bh_enable`, exactly once. It replaced a cut that consumed any number
(zero or more) of NET_RX start/stop records at the send, and that stopped at an
ambient record between them.
"""
import copy
import json
from pathlib import Path
import subprocess
import unittest

from evaluator.check import MODEL

# b1_other_endpoint as recorded on a contended host (load average 50-80,
# 2026-10-06; .worktrees/e-a mutant-E-M3 run, chunk-000a). Operation 3's
# handshake initiation goes to 127.0.0.1:1234; its NET_RX section holds an
# ambient start_dl_timer record (site 30) between the flow-hash draw and the
# section stop. The old cut failed: "expected retransmit_jitter (site 14), the
# record is site 49".
CONTENDED_B1 = json.loads(r'''{"hidden":[[[5,"5b31367705000000"],[5,"5b31367705000000"]],[],[[6,"7559868a05000000"],[40,"f05e3981ffffffff"],[6,"7559868a05000000"],[7,"7559868a05000000"],[1,"c316ce75497d83af1b4c84fab0f4e43799218ff3d33f5a1c7e9c132db661f306"],[3,"ba42c46a000000003825442500000000"],[4,"5943036600000000"],[8,"7559868a05000000"],[21,"3fb20f6a799beedd9f6e0b1ce0f0a413"],[20,"70894b4c00000000"],[48,"e0b33f81ffffffff"],[20,"d421a3fb00000000"],[49,"0000000000000000"],[14,"f600000000000000"],[41,"0000000000000000"]],[[6,"4356af9605000000"],[40,"f05e3981ffffffff"],[6,"4356af9605000000"],[7,"4356af9605000000"],[1,"886624c57b7b843a16108557b069e52653c4d396e35fe5bdaf4651ee71e8c338"],[3,"ba42c46a0000000006226d3100000000"],[4,"8ca6bb5500000000"],[8,"4356af9605000000"],[48,"e0b33f81ffffffff"],[23,"63c72430cf336ef60e363a07e859538a"],[30,"4356af9605000000"],[49,"0000000000000000"],[14,"be00000000000000"],[41,"0000000000000000"]],[],[]],"id":"b1_other_endpoint","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":1234},"public_key":"2222222222222222222222222222222222222222222222222222222222222222"},{"allowed_ips":[{"addr":"fd000000000000000000000000000000","cidr":8,"family":6}],"endpoint":{"addr":"00000000000000000000000000000001","family":6,"port":1234},"public_key":"3333333333333333333333333333333333333333333333333333333333333333"}],"private_key":"0100000000000000000000000000000000000000000000000000000000000000"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_xmit","packet":{"dst":"0a000001","family":4}},{"op":"wg_xmit","packet":{"dst":"fd000000000000000000000000000001","family":6}},{"op":"wg_observe"},{"op":"wg_get"}],"version":1}''')

# A wg_xmit to 224.0.0.1 without a peer (generated-wg-20260920-00136, recorded
# 2026-10-05): the fixture's sendto loops a multicast copy back before wg_xmit
# (one NET_RX section), and the ENOKEY error sends no ICMP (no icmp_global_consume
# draw). The old error-path cut absorbed that section.
MULTICAST = json.loads(r'''{"hidden":[[[5,"a0579b4b04000000"]],[],[[48,"e0b33f81ffffffff"],[49,"0000000000000000"]],[],[]],"id":"generated-wg-20260920-00136","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"20010db9000000000000000000000000","cidr":32,"family":6}],"endpoint":{"addr":"00000000000000000000000000000001","family":6,"port":51999},"public_key":"2222222222222222222222222222222222222222222222222222222222222222"}],"replace_peers":true},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_xmit","packet":{"dst":"e0000001","family":4}},{"op":"wg_observe"},{"op":"wg_get"}],"version":1}''')

# rx_roam_v6's comparison child as recorded on a contended host (load average
# 50-80, 2026-10-06, .worktrees/flake before-3 chunk-000b): operation 4's NAPI
# poll is a NET_RX section right after the decrypt worker's enqueue, with no
# resched record. Linux's kref_get_unless_zero operands were 1, 1, 3: the poll
# ran at the interrupt exit inside wg_queue_enqueue_per_peer_rx, holding its
# peer reference (Env.napiIrqExit); the placement after it gives 1, 1, 2.
CONTENDED_ROAM_CMP = json.loads(r'''{"hidden":[[[5,"a152759a1e000000"]],[[6,"9909f3a41e000000"],[40,"f05e3981ffffffff"],[6,"9909f3a41e000000"],[7,"9909f3a41e000000"],[1,"8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],[3,"803bb16a00000000b168de3a00000000"],[4,"0d0c0b0a00000000"],[8,"9909f3a41e000000"],[21,"23496d285f2d34c75cb861a51ec9230c"],[20,"01b25d3c00000000"],[48,"e0b33f81ffffffff"],[49,"0000000000000000"],[14,"3d00000000000000"],[41,"0000000000000000"]],[],[[48,"e0b33f81ffffffff"],[49,"0000000000000000"],[42,"807c3981ffffffff"],[13,"a99501cd1e000000"],[15,"8560c46a000000005316763a00000000"],[6,"a99501cd1e000000"],[60,"0000000000000000"],[44,"c0643981ffffffff"],[45,"0000000000000000"],[46,"00623981ffffffff"],[20,"7000000000000000"],[48,"e0b33f81ffffffff"],[49,"0000000000000000"],[6,"a99501cd1e000000"],[47,"0000000000000000"],[43,"0000000000000000"]],[[48,"e0b33f81ffffffff"],[49,"0000000000000000"],[50,"008c3981ffffffff"],[6,"a39cc3eb1e000000"],[48,"e0b33f81ffffffff"],[6,"9da600ec1e000000"],[49,"0000000000000000"],[63,"0000000000000000"],[51,"0000000000000000"]],[],[]],"id":"rx_roam_v6","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_observe"},{"family":4,"message":"02000000040302010d0c0b0aff2ee45601ec1b67310c7790404585ae697331eee1c1f8cf2419731c1fff3e6bc50a223d86b8a86bf41a2bd3a1ab84f892fd9bacbc45bda46dc025e6cac665a500000000000000000000000000000000","op":"wg_inject","port":51820},{"family":6,"message":"040000000d0c0b0a0000000000000000973bf9043cd64074998eeaaf05b9f8acd9ac555ca8099f9adfd3b40e88941a5d98b87fb01b15950d9b40eed7d7f7e394ee18c53077613a5d3e5a2bb979c5a98e","op":"wg_inject","port":51820},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["init_ephemeral","8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],["tai64n_now","803bb16a00000000b168de3a00000000"],["index_draw","0d0c0b0a"]],"version":1}''')


def widen(trace):
    """Dispatch order (docs/2026-10-11-dispatch-order.md): a section start
    record is {func, unit} and an arm record {jiffies, expires, timer} since
    2026-10-11. The captures above predate the identity word; a zero unit is
    "no identity", under which the mirror keeps the queue-order rule, so the
    captures stay replayable as recorded. Site ids from the built mirror."""
    from evaluator.check import load_hidden_sites
    sites = load_hidden_sites()
    starts = {e['id'] for (kind, consumer), e in sites.items() if kind == 'section' and consumer.endswith(':0')}
    arms = {e['id'] for (kind, _), e in sites.items() if kind == 'timer'}
    out = copy.deepcopy(trace)
    for op in out['hidden']:
        for rec in op:
            if (rec[0] in starts and len(rec[1]) == 16) or (rec[0] in arms and len(rec[1]) == 32):
                rec[1] += '0' * 16
    # W9 (docs/2026-10-06-w8-w9-netns-routing.md 4.1): the captures predate
    # the kind-306 dst-cache jiffies; without them the mirror keeps the pre-W9
    # rule (the cache always misses, no record consumed). A live run never
    # sets this: the check leaves it true and the kernel writes the records.
    out['dst_cache_records'] = False
    return out


def run(trace):
    result = subprocess.run([MODEL], input=json.dumps(widen(trace)).encode(), capture_output=True, timeout=120)
    return result.returncode, result.stdout.decode(), result.stderr.decode()


def replay(trace):
    if not MODEL.is_file():
        raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
    result = subprocess.run([MODEL], input=json.dumps(widen(trace)).encode(), capture_output=True, timeout=120)
    out = (result.stdout + result.stderr).decode()
    return None if result.returncode == 0 and out.startswith('{') and not result.stderr else out.strip()


def sites(op):
    return [r[0] for r in op]


class LoopbackNetRx(unittest.TestCase):
    def mutated(self, trace, index, change):
        trace = copy.deepcopy(trace)
        trace['hidden'][index] = change(trace['hidden'][index])
        return trace

    def test_contended_record_order_agrees(self):
        self.assertIsNone(replay(CONTENDED_B1))

    def test_multicast_loop_section_agrees(self):
        self.assertIsNone(replay(MULTICAST))

    def test_send_without_its_section_is_rejected(self):
        # the old cut accepted zero sections
        trace = self.mutated(CONTENDED_B1, 2, lambda op: [r for r in op if r[0] not in (48, 49)])
        self.assertIn('raised NET_RX: expected its section', replay(trace) or '')

    def test_two_sections_at_one_send_are_rejected(self):
        # the old cut accepted any number of sections
        def twice(op):
            stop = sites(op).index(49)
            return op[:stop + 1] + [[48, 'e0b33f81ffffffff'], [49, '0000000000000000']] + op[stop + 1:]
        self.assertIn('the record is site 48', replay(self.mutated(CONTENDED_B1, 2, twice)) or '')

    def test_section_after_the_send_is_rejected(self):
        # not a placement Linux takes: the raise runs at the send's local_bh_enable
        def late(op):
            start, stop = sites(op).index(48), sites(op).index(49)
            rest = op[:start] + op[stop + 1:]
            jitter = sites(rest).index(14)
            return rest[:jitter + 1] + op[start:stop + 1] + rest[jitter + 1:]
        self.assertIn('raised NET_RX: expected its section', replay(self.mutated(CONTENDED_B1, 2, late)) or '')

    def test_mirror_record_inside_the_section_is_rejected(self):
        def foreign(op):
            stop = sites(op).index(49)
            return op[:stop] + [[4, '0102030400000000']] + op[stop:]
        self.assertIn('expected section_stop:net_rx_action', replay(self.mutated(CONTENDED_B1, 2, foreign)) or '')

    def test_multicast_without_its_section_is_rejected(self):
        self.assertIn('raised NET_RX: expected its section', replay(self.mutated(MULTICAST, 2, lambda op: [])) or '')


class NapiPlacement(unittest.TestCase):
    def lookups(self, trace):
        if not MODEL.is_file():
            raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
        code, out, err = run(trace)
        self.assertEqual((code, err), (0, ''))
        result = json.loads(out)
        return result.get('napi_irq_ambiguous'), [b['operands'] for b in result['branches']
                                                  if b['index'] == 4 and b['label'] == '__refcount_add_not_zero.old_zero=0']

    def test_open_placement_is_reported(self):
        self.assertEqual(self.lookups(CONTENDED_ROAM_CMP), (1, [[1, 0], [1, 0], [2, 0]]))

    def test_placement_inside_the_enqueue_holds_its_reference(self):
        self.assertEqual(self.lookups(dict(CONTENDED_ROAM_CMP, napi_irq_before_put=[True])),
                         (1, [[1, 0], [1, 0], [3, 0]]))

    def test_a_choice_for_a_poll_that_does_not_exist_fails(self):
        code, _, err = run(dict(CONTENDED_ROAM_CMP, napi_irq_before_put=[True, True]))
        self.assertEqual(code, 4)
        self.assertIn('names more NAPI polls than the trace has', err)


# s2_index_collision as recorded on the dispatch-order oracle (identity
# bb3e577d, task/dispatch-order 57d56b7, 2026-10-11, the coordinator's
# single-trace run 1 of 10; copied from .artifacts/runs/evidence/dispatch-order/
# s2-captures/s2-1-chunk-000/model/inputs.jsonl, with Linux's wg_observe
# datagrams from that chunk's LEANUX_WGOBS row). wg_up queues both peers'
# handshake work (the kind-307 queue records at site 300: peer A's item
# 3002f803..., then peer B's 2008f803...); handshake_send_wq, unbound, ran
# B's item first: the first send-worker section (site 40) names unit
# 2008f803..., the second 3002f803.... In nine of the ten runs B ran first.
S2_B_FIRST = json.loads(r'''{"arm_records":true,"expect":["wg_index_hashtable_insert.unlocked_collision=1"],"hidden":[[[5,"97325b8200000000"],[5,"97325b8200000000"]],[[6,"cb85768a00000000"],[300,"3002f8038088ffff70703981ffffffff"],[6,"cb85768a00000000"],[300,"2008f8038088ffff70703981ffffffff"],[40,"70703981ffffffff2008f8038088ffff"],[6,"c58fb38a00000000"],[7,"c58fb38a00000000"],[1,"5f8a25b53de4fbceef4b9c6c2d39f9bd3caa552f6915029659920b642b3a8efc"],[3,"63cccb6a000000000882b00b00000000"],[4,"0d0c0b0a00000000"],[100,"2dddfeff0000000097f5feff00000000d009f8038088ffff"],[8,"c58fb38a00000000"],[21,"149ff99a11d2fcce512981cd4279ce13"],[20,"d9c684bc00000000"],[48,"60c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[14,"2900000000000000"],[100,"2eddfeff000000001de2feff000000003009f8038088ffff"],[41,"0000000000000000"],[40,"70703981ffffffff3002f8038088ffff"],[6,"b9a32d8b00000000"],[7,"b9a32d8b00000000"],[1,"200aaa8d4cd565455aa8e08777a2db4b5e99d00f734902fb6f0152c2cfd6ea11"],[3,"63cccb6a00000000fc952a0c00000000"],[4,"0d0c0b0a00000000"],[4,"4433221100000000"],[100,"2fddfeff0000000099f5feff00000000e003f8038088ffff"],[8,"b9a32d8b00000000"],[20,"0100000000000000"],[48,"60c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[14,"0800000000000000"],[100,"2fddfeff0000000013e2feff000000004003f8038088ffff"],[41,"0000000000000000"]],[],[]],"id":"s2_index_collision","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":16,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"},{"allowed_ips":[{"addr":"0a010000","cidr":16,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"ff2ee45601ec1b67310c7790404585ae697331eee1c1f8cf2419731c1fff3e6b"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["index_draw","0d0c0b0a"],["index_draw","0d0c0b0a"],["index_draw","44332211"]],"version":1}''')
# What the fixture's listener received at wg_observe (family, length, type,
# tos, bytes; the tos field is W5+W6's, 136 = HANDSHAKE_DSCP 0x88 for an
# initiation): B's initiation first (sender index 0d0c0b0a, the steered first
# draw), then A's (44332211, the redraw after the collision).
S2_B_FIRST_DATAGRAMS = [
    [4, 148, 1, 136, "010000000d0c0b0a73d88b66e8165fda3724a27657b9dce798d7ff733893e1e6196115ae53d867565304e0a005391d78d1bb2c7cd4f02518bde16bb6dfdd47a0647c13fa124dea6aefb275a7232ebcf2280c4367a19657ee9c423d849138478c86c590e738ee8b8c361b84f40cef3db78e52c1d98bb15c6557087e7bee4ed8892efd0e3600000000000000000000000000000000"],
    [4, 148, 1, 136, "010000004433221152c98894d07a768ddf4d05d5afd6033f71c6bc39e1f8a27288c50ba4f181ba352099812d628ac67576a02a445af0e835072a06e1975997311ada3fa5d6c1fc674017f3fa0129d1ece540e9f1934abcd211a83de17d71d29d83c6a8287e80ee9e8a400aff09aa4cf0a3f8682195fc5a21b0d602b955ccc49ecb19b22b00000000000000000000000000000000"],
]


class DispatchOrder(unittest.TestCase):
    """Dispatch order (docs/2026-10-11-dispatch-order.md): the mirror runs the
    queued unit the dispatch record names. Mutant Q-M1 (scripts/wg-mutants.py)
    runs the queue head instead; the test emulates it exactly by blanking the
    unit word of the send-worker section starts, which makes `peekUnit` return
    none and `runOneSendWorker` take the head, the one path Q-M1 forces. The
    real mutant builds that mirror and runs the s2_* traces live:
    `scripts/in-bundle python3 scripts/wg-mutants.py Q-M1-dispatch-order-ignored`."""

    def datagrams(self, trace):
        if not MODEL.is_file():
            raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
        code, out, err = run(trace)
        self.assertEqual((code, err), (0, ''), err)
        return json.loads(out)['observations'][2]['datagrams']

    @staticmethod
    def with_sections(change):
        trace = copy.deepcopy(S2_B_FIRST)
        trace['hidden'][1] = [change(r) if r[0] == 40 else r for r in trace['hidden'][1]]
        return trace

    def test_b_first_capture_agrees(self):
        # the mirror follows the records: B's initiation first, A's second, as the listener saw them
        self.assertEqual(self.datagrams(S2_B_FIRST), S2_B_FIRST_DATAGRAMS)

    def test_queue_order_rule_is_rejected_on_the_capture(self):
        # Q-M1's behaviour: without the identity the mirror runs A's item first.
        # Each message's index and ephemeral (bytes 0-40) still agree with Linux's,
        # consumed in record order; the encrypted static and timestamp (40-116),
        # built for the other remote static, do not: the semantic mismatch.
        legacy = self.datagrams(self.with_sections(lambda r: [r[0], r[1][:16] + '0' * 16]))
        self.assertNotEqual(sorted(legacy), sorted(S2_B_FIRST_DATAGRAMS))
        for linux in S2_B_FIRST_DATAGRAMS:
            same_head = [d for d in legacy if d[-1][:80] == linux[-1][:80]]
            self.assertEqual(len(same_head), 1, linux[-1][:16])
            self.assertNotEqual(same_head[0][-1][80:232], linux[-1][80:232])

    def test_a_unit_never_queued_is_a_hidden_mismatch(self):
        # the first section names a unit no queue record announced
        out = replay(self.with_sections(lambda r: [r[0], r[1][:16] + 'f1f1f1f1f1f1f1f1'] if r[1].endswith('2008f8038088ffff') else r))
        self.assertIn('was never queued', out or '')

    def test_missing_queue_records_are_a_hidden_mismatch(self):
        # a queue without its record: the mirror consumes one where the C queues
        trace = copy.deepcopy(S2_B_FIRST)
        trace['hidden'][1] = [r for r in trace['hidden'][1] if r[0] != 300]
        self.assertIn('expected queued:wg_packet_handshake_send_worker', replay(trace) or '')


if __name__ == '__main__':
    unittest.main()
