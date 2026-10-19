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

# rx_roam_v6's comparison child, as recorded on a contended host (load 50-80,
# 2026-10-06), showed the NAPI poll at the interrupt exit inside
# wg_queue_enqueue_per_peer_rx (placement (c'), Env.napiIrqExit) and carried
# the NapiPlacement tests. Retired 2026-10-13: the capture predates the
# dst-cache records (kind 306) and the 16-byte section-start records of the
# dispatch-order capture, and the (c') placement did not recur in two
# single-trace runs on the s2 oracle (the poll ran at the worker's yield).
# The placement machinery is exercised live by the W7 tier's
# w7_ring_rx_1025 (about a thousand open placements, selected by the check).


# w7_multi_tx_8's coverage child as recorded on the W9 oracle (2026-10-12,
# task/w7p2, run p2-w7_multi_tx_8-2): at operation 4 the tx worker yielded below
# the open encrypt worker while its ring still held items, and the kernel
# resumed the encrypt worker before the tx worker's rest (docs/2026-10-06-
# w4-w7-transmit-bulk.md 17.15). Phase 1 stops it fail-closed; a phase 2 on
# suspended activations must agree on it, and its one-off mutant ("ignore the
# resumption, continue the yielding activation") must not.
W7_RESUMED_OUTER = json.loads(r'''{"arm_records":true,"expect":["wg_receive_handshake_packet.response=1","wg_noise_handshake_begin_session.initiator=1","add_new_keypair.initiator=1","wg_packet_send_staged_packets.no_keypair=0","wg_packet_create_data_done.data_sent=1","encrypt_packet.checksum_partial=1","wg_prev_queue_dequeue.more_remain=1"],"hidden":[[[150,"12ddfeff00000000"],[5,"4a27188400000000"],[150,"13ddfeff00000000"]],[[6,"7e7a338c00000000"],[300,"3002f9038088ffffb0703981ffffffff"],[40,"b0703981ffffffff3002f9038088ffff"],[6,"7884708c00000000"],[7,"7884708c00000000"],[1,"8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],[3,"803bb16a00000000b168de3a00000000"],[4,"0d0c0b0a00000000"],[100,"37ddfeff0000000019e2feff00000000e003f9038088ffff"],[8,"728ead8c00000000"],[151,"37ddfeff00000000"],[21,"722619326876b643c912fef4ee152ed6"],[20,"e9d3e45c00000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[14,"c700000000000000"],[100,"38ddfeff000000005ae2feff000000004003f9038088ffff"],[41,"0000000000000000"]],[],[[48,"e0c53f81ffffffff0000000000000000"],[301,"78d5e50f8088ffff408e3981ffffffff"],[49,"0000000000000000"],[42,"408e3981ffffffff78d5e50f8088ffff"],[150,"d1ddfeff00000000"],[13,"d68e65b100000000"],[100,"d1ddfeff0000000029ed000001000000b803f9038088ffff"],[15,"221ccd6a0000000036e5ca3200000000"],[6,"d68e65b100000000"],[302,"28d5e50f8088ffff80763981ffffffff"],[100,"d1ddfeff00000000b3e2feff00000000e003f9038088ffff"],[60,"0000000000000000"],[43,"0000000000000000"],[44,"80763981ffffffff28d5e50f8088ffff"],[23,"da34fa28d245882ff4e89bd85ed378fd"],[303,"7002f9038088ffffc0733981ffffffff"],[45,"0000000000000000"],[46,"c0733981ffffffff7002f9038088ffff"],[100,"d1ddfeff00000000b3e2feff00000000e003f9038088ffff"],[151,"d1ddfeff00000000"],[20,"2a00000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"d68e65b100000000"],[47,"0000000000000000"]],[[6,"0c32c5cd00000000"],[302,"28d5e50f8088ffff80763981ffffffff"],[6,"0c32c5cd00000000"],[6,"0c32c5cd00000000"],[6,"0c32c5cd00000000"],[6,"0c32c5cd00000000"],[6,"063c02ce00000000"],[6,"063c02ce00000000"],[6,"063c02ce00000000"],[44,"80763981ffffffff28d5e50f8088ffff"],[303,"7002f9038088ffffc0733981ffffffff"],[61,"0000000000000000"],[46,"c0733981ffffffff7002f9038088ffff"],[100,"4adefeff000000002ce3feff00000000e003f9038088ffff"],[151,"4adefeff00000000"],[20,"7800000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[16,"af00000000000000"],[100,"4bdefeff0000000029edfeff000000009003f9038088ffff"],[6,"fa4f7cce00000000"],[62,"0000000000000000"],[303,"7002f9038088ffffc0733981ffffffff"],[45,"0000000000000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[20,"0000000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[100,"4bdefeff000000002de3feff00000000e003f9038088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"fa4f7cce00000000"],[47,"0000000000000000"],[46,"c0733981ffffffff7002f9038088ffff"],[47,"0000000000000000"]],[],[]],"id":"w7_multi_tx_8","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4},{"addr":"20010db8000000000000000000000000","cidr":32,"family":6}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":5,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_observe"},{"family":4,"message":"02000000040302010d0c0b0aff2ee45601ec1b67310c7790404585ae697331eee1c1f8cf2419731c1fff3e6bc50a223d86b8a86bf41a2bd3a1ab84f892fd9bacbc45bda46dc025e6cac665a500000000000000000000000000000000","op":"wg_inject","port":51820},{"items":[{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f16"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a71787f868d949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"949ba2a9b0b7bec5ccd3dae1e8eff6fd040b121920272e353c434a51585f666d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b62"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"b3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc030a11181f262d343b424950575e656c737a8188"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"d2d9e0e7eef5fc030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7ae"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"f1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3cad1d8dfe6edf4fb020910171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4"}},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"10171e252c333a41484f565d646b727980878e959ca3aab1b8bfc6cdd4dbe2e9f0f7fe050c131a21282f363d444b525960676e757c838a91989fa6adb4bbc2c9d0d7dee5ecf3fa"}}],"op":"wg_batch","wait_ms":400},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["init_ephemeral","8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],["tai64n_now","803bb16a00000000b168de3a00000000"],["index_draw","0d0c0b0a"]],"version":1}''')


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


def run_raw(trace):
    """`run` without `widen`, for a capture made on the current kernel (its
    section starts and arms already carry their identity words; `widen` would
    mis-pad them)."""
    result = subprocess.run([MODEL], input=json.dumps(with_wheel_records(with_timer_caller_jiffies(with_jiffies_end(trace)))).encode(), capture_output=True,
                            timeout=120)
    return result.returncode, result.stdout.decode(), result.stderr.decode()


# The operations whose wait the mirror ends with the end-of-wait jiffies read
# (review item 7, kind 310, Leanux/Syscalls.lean): the captures above predate
# the instrument, so the replays append the record the guest now writes at the
# end of each such wait, with the operation's last recorded jiffies (the arm
# records' first word, the dst-cache stamps, an advance's `after`) carried
# forward: no timer the capture did not show fires, and jiffies never goes
# back. A fixture of the replay, not a mirror rule.
JIFFIES_END_OPS = ('wg_set', 'wg_inject', 'wg_up', 'wg_xmit', 'wg_batch', 'wg_observe', 'wg_advance')
JIFFIES_END_SITE = 128
JIFFIES_SITES = {100: 0, 150: 0, 151: 0, 101: 8}   # site -> byte offset of its jiffies word


# Pre-release review finding 2 (kind 311, Leanux/WG/State.lean `callerJiffies`):
# the mirror consumes a peer timer caller's own jiffies read before each arm
# record. The captures above predate the instrument, so the replays insert,
# before every arm record not already preceded by one, the caller-read record
# the kernel now writes, with the value the capture determines: the arm's
# published expiry minus the delay of the timer the arm fits (the five
# timers' delays are the C's constants; a jittered one takes the jitter from
# the last accepted draw record in the operation, the C's `(83 * r) >> 8`),
# the fit being the one whose implied caller read is within a tick of
# mod_timer's. A fixture of the replay, not a mirror rule: a capture made on
# a kernel with the instrument carries the record itself and is left alone.
# Sites 422-426 are the ordinary callers; the two expired-callback re-arms
# (420, 421) do not occur in these captures.
TIMER_ARM_SITE = 100
TIMER_CALLER_SITE_IDS = {420, 421, 422, 423, 424, 425, 426}
JITTER_SITES = {'retransmit': 14, 'new_handshake': 16}
HZ = 250
MASK64 = (1 << 64) - 1


def with_timer_caller_jiffies(trace):
    trace = copy.deepcopy(trace)
    if 'hidden' not in trace:
        return trace
    # a capture made on a kernel with the instrument (s3 and later) carries the
    # reads itself, before the jitter draws on the jittered arms, and is left alone
    if any(site in TIMER_CALLER_SITE_IDS for records in trace['hidden'] for site, _ in records):
        return trace
    keepalive = max((peer.get('keepalive', 0) for op in trace['ops'] if op.get('op') == 'wg_set'
                     for peer in op.get('config', {}).get('peers', [])), default=0)
    for records in trace['hidden']:
        out, jitter, draw_at = [], {}, {}
        for site, value in records:
            for name, draw_site in JITTER_SITES.items():
                if site == draw_site:
                    # the compiled argument reads jiffies before the jitter draw (measured on
                    # s3), so the synthetic caller read goes before the first draw of the
                    # rejection loop, not right before the arm
                    draw_at.setdefault(name, len(out))
                    r = int(value[:2], 16)
                    if (83 * r) % 256 >= 256 % 83:
                        jitter[name] = 83 * r // 256
            if site == TIMER_ARM_SITE and not (out and out[-1][0] in TIMER_CALLER_SITE_IDS):
                jm = int.from_bytes(bytes.fromhex(value[:16]), 'little')
                e = int.from_bytes(bytes.fromhex(value[16:32]), 'little')
                # a jittered timer is armed right after its draw in the same operation, so
                # it is a candidate only while an unconsumed draw precedes the arm
                candidates = [(425, 540 * HZ), (423, 10 * HZ), (426, keepalive * HZ)]
                if 'new_handshake' in jitter:
                    candidates.append((422, 15 * HZ + jitter['new_handshake']))
                if 'retransmit' in jitter:
                    candidates.append((424, 5 * HZ + jitter['retransmit']))
                fits = [(caller, (e - delay) & MASK64) for caller, delay in candidates
                        if delay and ((jm - ((e - delay) & MASK64)) & MASK64) <= 1]
                if not fits:
                    raise AssertionError(f'replay fixture: arm {value} fits no timer delay within a tick of {jm:#x}')
                caller, jc = fits[-1]   # the jittered fit, when its draw is present, over a coincident constant
                name = {422: 'new_handshake', 424: 'retransmit'}.get(caller, '')
                jitter.pop(name, None)
                at = draw_at.pop(name, len(out))
                out.insert(at, [caller, jc.to_bytes(8, 'little').hex()])
            out.append([site, value])
        records[:] = out
    return trace


# B3 (docs/2026-10-15-design-b3-timer-wheel.md, section 3.2; Leanux/WG/State.lean
# `armTimer`): the mirror consumes, after every arm record that locks the base
# (a pending timer re-armed with the same expires does not), the base-clock
# record (kind 313, site 428, {clk, timer}) and, when the C enqueues (a fresh
# arm or a slot change; not a same-slot re-arm), the enqueue record (kind 314,
# site 429, {idx, bucket_expiry, timer}). The captures above predate both, so
# the replays insert them with the values the capture determines: the clock
# as mod_timer's own read (the no-lag case, which the s4 measurement found
# for every arm of the corpus) and the slot and bucket expiry by the C's
# arithmetic (timer.c:567-620) on that clock, tracking each timer's slot and
# expiry across the trace. A fixture of the replay, not a mirror rule; a
# capture made on the s5 pair or later carries the records and is left alone.
TIMER_CLK_SITE, TIMER_ENQUEUE_SITE = 428, 429
TIMER_SECTION_START_SITES = {102, 104, 106, 108, 112}   # the five callbacks (Worker.sectionId: indices 6-9, 11)
LVL_START = [None] + [63 << (3 * (n - 1)) for n in range(1, 10)]


def wheel_index(expires, clk):
    """`calc_wheel_index` (timer.c:584-620) at HZ 250 (LVL_DEPTH 9): (slot, bucket expiry)."""
    delta = (expires - clk) & MASK64
    for lvl in range(0, 8):
        if delta < LVL_START[lvl + 1]:
            break
    else:
        if delta >> 63:
            return clk & 63, clk
        lvl = 8
        if delta >= LVL_START[9]:
            expires = (clk + LVL_START[9] - (1 << 24)) & MASK64
    e = ((expires >> (3 * lvl)) + 1) & MASK64
    return 64 * lvl + (e & 63), (e << (3 * lvl)) & MASK64


def with_wheel_records(trace):
    trace = copy.deepcopy(trace)
    if 'hidden' not in trace:
        return trace
    if any(site in (TIMER_CLK_SITE, TIMER_ENQUEUE_SITE) for records in trace['hidden'] for site, _ in records):
        return trace
    timers = {}   # timer address -> (expires, slot); cleared by a firing (its section names the timer)
    for op, records in zip(trace['ops'], trace['hidden']):
        if op['op'] in ('wg_down', 'wg_delete', 'wg_netns_close'):
            timers.clear()   # wg_timers_stop (device.c:124, peer.c:106)
        out, caller = [], None
        for site, value in records:
            out.append([site, value])
            if site in TIMER_CALLER_SITE_IDS:
                caller = site
            if site == TIMER_ARM_SITE:
                jm = int.from_bytes(bytes.fromhex(value[:16]), 'little')
                e = int.from_bytes(bytes.fromhex(value[16:32]), 'little')
                addr = int.from_bytes(bytes.fromhex(value[32:48]), 'little') if len(value) >= 48 else 0
                # the sites whose timer is not pending at the arm, by the C's guard
                # (timers.c:147, :157) or the callback's detach (:60, :84): a fresh
                # enqueue, whatever the capture showed before (a deletion the records
                # do not carry, timers.c:170 and :178, lies between)
                old = None if caller in (420, 421, 422, 423) else timers.get(addr)
                if old is not None and old[0] == e:
                    continue   # __mod_timer :1085-1088: no lock, no records
                out.append([TIMER_CLK_SITE, jm.to_bytes(8, 'little').hex() + addr.to_bytes(8, 'little').hex()])
                slot, bexp = wheel_index(e, jm)
                if old is not None and old[1] == slot:
                    timers[addr] = (e, slot)   # :1123-1130: the slot kept, no enqueue record
                    continue
                timers[addr] = (e, slot)
                out.append([TIMER_ENQUEUE_SITE, slot.to_bytes(8, 'little').hex() + bexp.to_bytes(8, 'little').hex()
                            + addr.to_bytes(8, 'little').hex()])
            elif site in TIMER_SECTION_START_SITES and len(value) >= 32:
                timers.pop(int.from_bytes(bytes.fromhex(value[16:32]), 'little'), None)
        records[:] = out
    return trace


def with_jiffies_end(trace):
    trace = copy.deepcopy(trace)
    if 'hidden' not in trace:
        return trace
    jiffies = 0
    for op, records in zip(trace['ops'], trace['hidden']):
        for site, value in records:
            if site in JIFFIES_SITES and site != JIFFIES_END_SITE:
                offset = JIFFIES_SITES[site]
                jiffies = max(jiffies, int.from_bytes(bytes.fromhex(value[2 * offset:2 * offset + 16]), 'little'))
        if op['op'] in JIFFIES_END_OPS and not any(site == JIFFIES_END_SITE for site, _ in records):
            records.append([JIFFIES_END_SITE, jiffies.to_bytes(8, 'little').hex()])
    return trace


def replay(trace):
    if not MODEL.is_file():
        raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
    result = subprocess.run([MODEL], input=json.dumps(with_wheel_records(with_timer_caller_jiffies(with_jiffies_end(widen(trace))))).encode(), capture_output=True,
                            timeout=120)
    out = (result.stdout + result.stderr).decode()
    return None if result.returncode == 0 and out.startswith('{') and not result.stderr else out.strip()

def replay_raw(trace):
    """`replay` without `widen`: a capture made on the current kernel (the identity words, the kind-306 records)."""
    if not MODEL.is_file():
        raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
    result = subprocess.run([MODEL], input=json.dumps(with_wheel_records(with_timer_caller_jiffies(with_jiffies_end(trace)))).encode(), capture_output=True, timeout=120)
    out = (result.stdout + result.stderr).decode()
    return None if result.returncode == 0 and out.startswith('{') and not result.stderr else out.strip()


def sites(op):
    return [r[0] for r in op]


# W7_RESUMED_OUTER's operation 4 rearranged to the schedule the audit wave's
# claim point met under seven guests (2026-10-13, w7_ring_fresh_1024 in the
# tier group): the encrypt worker yields after two items; the tx worker,
# dispatched at that yield, sends both (two record groups) and stops at the
# uncrypted third; the encrypt worker resumes, re-queues the tx work at its
# third enqueue and finishes; the tx worker's second run sends items 3 to 8.
# Every record value is the capture's own.
def _crypt_ahead_instance():
    trace = copy.deepcopy(W7_RESUMED_OUTER)
    h = W7_RESUMED_OUTER['hidden'][4]
    head, item1, item2, rest = h[:13], h[13:21], h[24:29], h[29:53]
    tx_stop, queued_tx, enc_stop, tx_start = h[53], h[22], h[23], h[54]
    trace['hidden'][4] = head + item1 + item2 + [tx_stop, queued_tx, enc_stop, tx_start] + rest + [tx_stop]
    trace['id'] = 'w7_crypt_ahead'
    return trace


W7_CRYPT_AHEAD = _crypt_ahead_instance()


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


# The NapiPlacement tests went with CONTENDED_ROAM_CMP (above).


# s2_index_collision as recorded on the s2 oracle (identity cea1e9a3,
# task/robustness, 2026-10-13, the coverage child of a single-trace run,
# .artifacts/check/cap-s2-1/chunk-000/model/inputs.jsonl, with Linux's
# wg_observe datagrams from that chunk's LEANUX_WGOBS row; three runs alone
# gave B first; the earlier capture, on the dispatch-order oracle of
# 2026-10-11, predated the dst-cache records and the 16-byte section
# starts). wg_up queues both peers' handshake work (the kind-307 queue
# records at site 300: peer A's item 3002e706..., then peer B's
# 2008e706...); handshake_send_wq, unbound, ran B's item first: the first
# send-worker section (site 40) names unit 2008e706..., the second
# 3002e706....
S2_B_FIRST = json.loads(r'''{"arm_records":true,"expect":["wg_index_hashtable_insert.unlocked_collision=1"],"hidden":[[[150,"3bddfeff00000000"],[5,"e932c68e00000000"],[150,"3cddfeff00000000"],[150,"3cddfeff00000000"],[5,"e932c68e00000000"],[150,"3cddfeff00000000"],[128,"55ddfeff00000000"]],[[6,"f9c14f9800000000"],[300,"3002e7068088fffff0ab3981ffffffff"],[6,"f9c14f9800000000"],[300,"2008e7068088fffff0ab3981ffffffff"],[40,"f0ab3981ffffffff2008e7068088ffff"],[6,"edd5c99800000000"],[7,"edd5c99800000000"],[1,"35371410366587f25a8ba3a4bf4ce1699ed42450d47b8ba792e15baf0324ae27"],[3,"a197ce6a00000000cab6471900000000"],[4,"0d0c0b0a00000000"],[100,"66ddfeff00000000d0f5feff00000000d009e7068088ffff"],[8,"edd5c99800000000"],[151,"66ddfeff00000000"],[21,"7527a079b9d49f0917c84d8139a00f7e"],[20,"f934cb2f00000000"],[48,"20014081ffffffff0000000000000000"],[49,"0000000000000000"],[14,"f300000000000000"],[100,"68ddfeff0000000098e2feff000000003009e7068088ffff"],[41,"0000000000000000"],[40,"f0ab3981ffffffff3002e7068088ffff"],[6,"dbf3809900000000"],[7,"dbf3809900000000"],[1,"ef6e87ef491a6ca1198e214d24d0c19c61039e3887483fb7fad157042a2d83c7"],[3,"a197ce6a00000000b8d4fe1900000000"],[4,"0d0c0b0a00000000"],[4,"4433221100000000"],[100,"69ddfeff00000000d3f5feff00000000e003e7068088ffff"],[8,"dbf3809900000000"],[151,"69ddfeff00000000"],[20,"0100000000000000"],[48,"20014081ffffffff0000000000000000"],[49,"0000000000000000"],[14,"8200000000000000"],[100,"69ddfeff0000000075e2feff000000004003e7068088ffff"],[41,"0000000000000000"],[128,"7dddfeff00000000"]],[[128,"08defeff00000000"]],[]],"id":"s2_index_collision","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":16,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"},{"allowed_ips":[{"addr":"0a010000","cidr":16,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"ff2ee45601ec1b67310c7790404585ae697331eee1c1f8cf2419731c1fff3e6b"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["index_draw","0d0c0b0a"],["index_draw","0d0c0b0a"],["index_draw","44332211"]],"version":1}''')
# What the fixture's listener received at wg_observe (family, length, type,
# tos, bytes; the tos field is W5+W6's, 136 = HANDSHAKE_DSCP 0x88 for an
# initiation): B's initiation first (sender index 0d0c0b0a, the steered first
# draw), then A's (44332211, the redraw after the collision).
# the unit the first send-worker section names (peer B's work item)
S2_B_UNIT = next(v[16:32] for site, v in S2_B_FIRST['hidden'][1] if site == 40)

S2_B_FIRST_DATAGRAMS = [
    [4, 148, 1, 136, "010000000d0c0b0a9df254beb83fa776c4cff00b66fec10a3c38d4e7c1e70690d0f42dea2ab9a12fc013832213c18ff988b8753d64de72b3f9b2c76dd9e52916f1d05ad17128d088830461c86674faa158c29b3a1c79e0275577801ed1492bc4e6073c69940634d282f051b79938b7cdf64015347405e26899108db7b09f5e6725f5711200000000000000000000000000000000"],
    [4, 148, 1, 136, "01000000443322117f39d6d6b2b98c2b1ddc9072217e4699f34609bc7046d94d30a6c27e91deaa20991601efe334ebf5ad9f6b914589efa1a4ccf5c97e4c91ef97f9c8ec109d718d7b5c589f557fa864e454a70e7bff3cc913ac82a47c2365399fcdc6c365a8c03e7e3f529d02692a857721045b8b46e4edb71fda4dbf21c6da0a14789800000000000000000000000000000000"],
]


# W8 under load (the integration record c047e64's named follow-on): the live
# capture of w8_down_exit_up on s4 with one kind-302 record inserted in the
# netns-close operation at `default_device_exit_batch`'s cond_resched
# (net/core/dev.c:12174, site 427, ambient), between cleanup_net's own
# yields (site 152), every other value the capture's own. The old model:
# "expected section_stop:cleanup_net (site 115), the record is site 427".
W8_DEFAULT_DEVICE_EXIT = json.loads(r'''{"arm_records":true,"hidden":[[[150,"3addfeff00000000"],[5,"d2720f8f00000000"],[150,"3addfeff00000000"],[128,"53ddfeff00000000"]],[[312,"40e4cb81ffffffff408c3e81ffffffff"],[114,"408c3e81ffffffff40e4cb81ffffffff"],[150,"7dddfeff00000000"],[150,"7fddfeff00000000"],[427,"0000000000000000"],[152,"0000000000000000"],[152,"0000000000000000"],[152,"0000000000000000"],[115,"0000000000000000"]],[[128,"c1defeff00000000"]],[],[[128,"30dffeff00000000"]]],"id":"w8_default_device_exit_resched","net_fixture":"foreign-creator","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":25,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_netns_close"},{"op":"wg_up"},{"op":"wg_get"},{"op":"wg_observe"}],"version":1}''')


class NetnsExitYield(unittest.TestCase):
    def test_default_device_exit_resched_is_ambient(self):
        # the yield inside cleanup_net's section is passed over, like site 152
        self.assertIsNone(replay_raw(W8_DEFAULT_DEVICE_EXIT))

    def test_a_record_the_mirror_does_not_declare_still_fails(self):
        # the same stream with an undeclared site in that position
        trace = json.loads(json.dumps(W8_DEFAULT_DEVICE_EXIT))
        trace['hidden'][1] = [[999 if r[0] == 427 else r[0], r[1]] for r in trace['hidden'][1]]
        self.assertIn('the record is site 999', replay_raw(trace) or '')


# Campaign 2's batch-backlog witness (.worktrees/proofs-campaign-2/docs/
# 2026-10-14-campaign-2-mirror-requests.md, section 1; its typed form in the
# campaign's Leanux/Proofs/WG/Progress/BatchBacklog.lean): a constructed record
# stream, not a capture. `wg_up` with an all-zero port draw (32768) and
# jiffies-end 100; then a `wg_batch` of one 64-byte cookie-shaped injection
# whose records are a NET_RX section with the receive worker's queue record
# and jiffies-end 101, and no receive-worker section. The batch's completion
# guard (Env.afterBatch) omitted the handshake receive queue, so the mirror
# accepted the operation with a packet queued and its worker pending, where
# the injection path's drain check refuses it. Refused since 2026-10-15 (the
# environment's completion rule; the mirror modules untouched). A guest run
# cannot host this witness: the kernel always dispatches the worker.
def _word(n, width=8):
    return n.to_bytes(width, 'little').hex()


BATCH_BACKLOG = {
    "version": 1, "id": "campaign2-pending-handshake",
    "ops": [{"op": "wg_up"},
            {"op": "wg_batch", "wait_ms": 100,
             "items": [{"kind": "inject", "family": 4, "port": 32768, "message": "03000000" + "00" * 60}]}],
    "hidden": [[[125, _word(0)], [128, _word(100)]],
               [[48, _word(0) + _word(0)], [301, _word(1) + _word(0)], [49, _word(0)], [128, _word(101)]]],
    "arm_records": True}


class BatchBacklog(unittest.TestCase):
    def test_queued_receive_worker_without_its_section_is_refused(self):
        self.assertIn("work the batch queued outlived the guest's wait", replay_raw(BATCH_BACKLOG) or '')


# Campaign 2's requests 2 and 4 (.worktrees/proofs-campaign-2/docs/
# 2026-10-14-campaign-2-mirror-requests.md, sections 2 and 4; the typed forms
# in its Progress/QueueRefill.lean and Progress/RecordedPending.lean): the
# corpus trace w6_rst_syn's first four operations (the peer configured, wg_up,
# an observe, the handshake response injected), then a wg_batch of the
# corpus's authenticated SYN and one transmit, with constructed records in
# the legacy mode (no arm records, no dst-cache records), not a capture.
# Operation 4: the decrypt worker's dispatch yields after one iteration; the
# encrypt worker's dispatch runs its ring poll, whose NET_RX section delivers
# the SYN and the stack's reply transmits into the encrypt ring it is
# draining (a requeue during the unit's own run, send.c:293, queueing.h:174).
# - QUEUE_REFILL ends its records at the encrypt worker's stop. Until
#   2026-10-19 the activation's bound (the ring's occupancy at the start plus
#   one) stopped the run as an invariant, "consumed more items than its queue
#   held (1)", where the C's loop re-reads the ring and drains the refill; the
#   bound now counts the refills a run can take, and the trace ends outside
#   the domain where its records end (the tx worker's work undrained).
# - RECORDED_PENDING yields the encrypt worker after its first item, resumes
#   it to drain the refill, and completes the operation. The requeue set the
#   encrypt unit's PENDING bit again, so the kernel runs the function once
#   more after the run returns (kernel/workqueue.c:2322-2325, 2374, 3230), a
#   dispatch with its own section whose ring poll finds nothing; the stream
#   omits it and was accepted with the identity dangling (request 4). Refused
#   since 2026-10-19 by the batch's completion guard.
# - EMPTY_REDISPATCH is that stream with the redispatch's section present:
#   the empty-ring dispatch guard refused it before ("expected jiffies_end
#   (site 128), the record is site 44"); it is the C's schedule and is
#   accepted since 2026-10-19.
def _c(n):
    return _word(n * 1000000000)


def _j(n):
    return [128, _word(100000 + n)]


_SEC = dict(sendWorker=(40, 41), receiveWorker=(42, 43), encryptWorker=(44, 45), txWorker=(46, 47), netRx=(48, 49), decryptWorker=(50, 51))


def _start(w):
    return [_SEC[w][0], _word(0) + _word(0)]


def _stop(w):
    return [_SEC[w][1], _word(0)]


_RST_SYN = json.loads((Path(__file__).resolve().parents[1] / 'corpus/wireguard/w6_rst_syn.json').read_text())
_REFILL_ROWS = [
    [[5, _c(100)], _j(0)],
    [[6, _c(101)], _start('sendWorker'), [6, _c(101)], [7, _c(101)], [1, bytes(129 + n for n in range(32)).hex()],
     [3, bytes([128, 59, 177, 106, 0, 0, 0, 0, 177, 104, 222, 58, 0, 0, 0, 0]).hex()],
     [4, bytes([13, 12, 11, 10, 0, 0, 0, 0]).hex()], [8, _c(101)],
     _start('netRx'), _stop('netRx'), [14, bytes([200, 0, 0, 0, 0, 0, 0, 0]).hex()], _stop('sendWorker'), _j(1)],
    [_j(2)],
    [_start('netRx'), _stop('netRx'), _start('receiveWorker'), [13, _c(102)], [15, _word(102) + _word(0)], [6, _c(102)],
     _stop('receiveWorker'), _start('encryptWorker'), _stop('encryptWorker'), _start('txWorker'),
     _start('netRx'), _stop('netRx'), [6, _c(102)], _stop('txWorker'), _j(3)],
    [_start('netRx'), _stop('netRx'), [6, _c(103)], _start('decryptWorker'), [6, _c(103)], [63, _word(0)],
     _start('encryptWorker'), _start('netRx'), [6, _c(103)], [6, _c(103)], _stop('netRx'), _stop('encryptWorker')]]
_REFILL_OPS = _RST_SYN['ops'][:4] + [{"op": "wg_batch", "wait_ms": 100, "items": [
    {"kind": "inject", "family": 4, "port": 51820, "message": _RST_SYN['ops'][4]['message']},
    {"kind": "xmit", "packet": {"family": 4, "dst": "0a000001", "payload": "01"}}]}]
QUEUE_REFILL = {"version": 1, "id": "campaign2-encrypt-refill", "ops": _REFILL_OPS, "hidden": _REFILL_ROWS, "dst_cache_records": False}
_PENDING_ROW = _REFILL_ROWS[4][:11] + [[61, _word(0)], _stop('encryptWorker'), _stop('decryptWorker'), _start('txWorker'),
                                       _start('netRx'), _stop('netRx'), [16, _word(1)], [6, _c(103)],
                                       _start('netRx'), _stop('netRx'), [6, _c(103)], _stop('txWorker'), _j(4)]
RECORDED_PENDING = dict(QUEUE_REFILL, id="campaign2-recorded-encrypt-requeue", hidden=_REFILL_ROWS[:4] + [_PENDING_ROW])
EMPTY_REDISPATCH = dict(RECORDED_PENDING, id="campaign2-empty-redispatch",
                        hidden=_REFILL_ROWS[:4] + [_PENDING_ROW[:-1] + [_start('encryptWorker'), _stop('encryptWorker'), _j(4)]])


class EncryptRequeue(unittest.TestCase):
    def test_a_refill_during_the_run_is_drained_by_the_run(self):
        out = replay_raw(QUEUE_REFILL) or ''
        self.assertNotIn('consumed more items than its queue held', out)
        self.assertIn("work the batch queued outlived the guest's wait", out)

    def test_a_requeued_unit_without_its_redispatch_is_refused(self):
        self.assertIn('wg_packet_encrypt_worker is pending at the end of the wait', replay_raw(RECORDED_PENDING) or '')

    def test_the_redispatch_with_an_empty_ring_is_the_schedule(self):
        self.assertIsNone(replay_raw(EMPTY_REDISPATCH))


def _replay_prepared(trace):
    """Run the model on a trace whose caller reads are already in place (no second synthesis)."""
    if not MODEL.is_file():
        raise AssertionError(f'{MODEL} is missing: run `lake build leanux-model` first')
    result = subprocess.run([MODEL], input=json.dumps(with_wheel_records(with_jiffies_end(trace))).encode(), capture_output=True, timeout=120)
    out = (result.stdout + result.stderr).decode()
    return None if result.returncode == 0 and out.startswith('{') and not result.stderr else out.strip()


def _s2_keepalive_arm():
    """S2_B_FIRST with its caller reads synthesised once; the index of the keepalive
    arm (site 426, 25 s, the first arm of wg_up) and of its read in operation 1."""
    trace = with_timer_caller_jiffies(S2_B_FIRST)
    records = trace['hidden'][1]
    read = next(i for i, r in enumerate(records) if r[0] == 426)
    arm = read + 1
    assert records[arm][0] == TIMER_ARM_SITE
    return trace, read, arm


class TimerArmMessages(unittest.TestCase):
    """The three verdicts of `armTimer` with the caller's read (kind 311) present
    (review finding 2; the mutation campaign noted the pre-311 model reported a
    wrong delay as a stall)."""

    def test_prepared_capture_agrees(self):
        trace, _, _ = _s2_keepalive_arm()
        self.assertIsNone(_replay_prepared(trace))

    def test_a_wrong_delay_names_the_expiry_mismatch(self):
        # the caller's read one tick earlier: expires = jc + delay no longer equals the published e
        trace, read, _ = _s2_keepalive_arm()
        jc = int.from_bytes(bytes.fromhex(trace['hidden'][1][read][1]), 'little')
        trace['hidden'][1][read][1] = ((jc - 1) & MASK64).to_bytes(8, 'little').hex()
        out = _replay_prepared(trace) or ''
        self.assertIn('timer expiry differs from Linux', out)
        self.assertIn("the mirror's delay 6250 gives", out)
        self.assertNotIn('a stall between', out)

    def test_a_gap_above_one_tick_is_a_stall(self):
        # mod_timer's own read two ticks after the caller's, the published expiry unchanged
        trace, read, arm = _s2_keepalive_arm()
        jc = int.from_bytes(bytes.fromhex(trace['hidden'][1][read][1]), 'little')
        value = trace['hidden'][1][arm][1]
        trace['hidden'][1][arm][1] = ((jc + 2) & MASK64).to_bytes(8, 'little').hex() + value[16:]
        out = _replay_prepared(trace) or ''
        self.assertIn("a stall between a timer's two jiffies reads (the mirror's delay matches the published expiry)", out)
        self.assertNotIn('timer expiry differs', out)

    def test_mod_timer_behind_the_caller_is_a_hidden_mismatch(self):
        trace, read, arm = _s2_keepalive_arm()
        jc = int.from_bytes(bytes.fromhex(trace['hidden'][1][read][1]), 'little')
        value = trace['hidden'][1][arm][1]
        trace['hidden'][1][arm][1] = ((jc - 1) & MASK64).to_bytes(8, 'little').hex() + value[16:]
        self.assertIn("is behind the caller's read", _replay_prepared(trace) or '')


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
        code, out, err = run_raw(trace)
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
        out = replay_raw(self.with_sections(lambda r: [r[0], r[1][:16] + 'f1f1f1f1f1f1f1f1'] if r[1].endswith(S2_B_UNIT) else r))
        self.assertIn('was never queued', out or '')

    def test_missing_queue_records_are_a_hidden_mismatch(self):
        # a queue without its record: the mirror consumes one where the C queues
        trace = copy.deepcopy(S2_B_FIRST)
        trace['hidden'][1] = [r for r in trace['hidden'][1] if r[0] != 300]
        self.assertIn('expected queued:wg_packet_handshake_send_worker', replay_raw(trace) or '')


class SuspendedActivation(unittest.TestCase):
    """W7 phase 2 (docs/2026-10-06-w4-w7-transmit-bulk.md 17.15): the capture
    where the tx worker yielded below the encrypt worker, which still had
    seven items. The encrypt worker is a suspended activation; the records
    resume it (its tx re-queue record), then the tx worker (its sends), then
    the re-queued tx run finds the queue empty. Phase 1 stopped here ("a
    worker yielded below an open worker with queued work")."""

    def test_resumed_outer_capture_replays(self):
        self.assertIsNone(replay_raw(W7_RESUMED_OUTER))

    def test_crypt_ahead_replays(self):
        """The encrypt worker's yield position by elimination (Env/Batch.lean
        `cryptAhead`, claim-point robustness 2026-10-13). The audit wave's
        claim point failed w7_ring_fresh_1024 in its tier group under seven
        guests with "expected section_stop:wg_packet_tx_worker (site 47), the
        record is site 100": the kernel dispatched the tx worker at an encrypt
        yield and it sent more items than the mirror's encrypt activation,
        which yields at its first item, had crypted. The instance is
        W7_RESUMED_OUTER's operation 4 rearranged to that schedule: the
        encrypt worker yields after two items, the tx worker sends both and
        stops at the uncrypted third, the encrypt worker resumes, re-queues
        the tx work at its third item and finishes, and the tx worker's second
        run sends the rest. Without the rule the replay fails as the claim
        point did; with it the replay agrees."""
        self.assertIsNone(replay_raw(W7_CRYPT_AHEAD))


if __name__ == '__main__':
    unittest.main()


# w7_mixed's comparison child as recorded in the int-r claim point under eight
# guests (2026-10-12, .artifacts/check/int-r-wireguard, the wireguard group):
# at operation 4 (a batch: inject, xmit, inject, xmit) the decrypt worker
# yields at its cond_resched after item 1 and the kernel switches to the
# encrypt kworker before the NAPI poll the decrypt worker raised has run; the
# poll then runs at the encrypt worker's first ptr_ring_consume_bh, nested in
# the encrypt worker's section before its queued-tx record (records 44, 48,
# ..., 49, 303, 45), where six other runs had it before the section (48, ...,
# 49, 44, 303, 45). Design 17.17.
INT_R_W7_MIXED_CMP = json.loads(r'''{"arm_records":true,"expect":["wg_receive_handshake_packet.response=1","wg_noise_handshake_begin_session.initiator=1","add_new_keypair.initiator=1","wg_packet_send_staged_packets.no_keypair=0","wg_packet_receive.data=1","validate_header_len.data=1","wg_packet_consume_data.no_keypair=0","wg_packet_create_data_done.data_sent=1","encrypt_packet.checksum_partial=1","wg_prev_queue_dequeue.more_remain=1"],"hidden":[[[150,"7edffeff00000000"],[5,"e1d5161801000000"],[150,"7edffeff00000000"]],[[6,"2d013e1f01000000"],[300,"3002e7068088ffffb0703981ffffffff"],[40,"b0703981ffffffff3002e7068088ffff"],[6,"270b7b1f01000000"],[7,"270b7b1f01000000"],[1,"8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],[3,"803bb16a00000000b168de3a00000000"],[4,"0d0c0b0a00000000"],[100,"9ddffeff000000007fe4feff00000000e003e7068088ffff"],[8,"270b7b1f01000000"],[151,"9ddffeff00000000"],[21,"2956f652c4ee0d779ffa455c1b7abe42"],[20,"ee546bc400000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[14,"2500000000000000"],[100,"9ddffeff000000008ae4feff000000004003e7068088ffff"],[41,"0000000000000000"]],[],[[48,"e0c53f81ffffffff0000000000000000"],[301,"78d5e50f8088ffff408e3981ffffffff"],[30,"093a313f01000000"],[49,"0000000000000000"],[42,"408e3981ffffffff78d5e50f8088ffff"],[150,"22e0feff00000000"],[13,"093a313f01000000"],[100,"22e0feff000000007aef000001000000b803e7068088ffff"],[15,"4d66cd6a000000004aa45e0d00000000"],[6,"093a313f01000000"],[302,"28d5e50f8088ffff80763981ffffffff"],[100,"22e0feff0000000004e5feff00000000e003e7068088ffff"],[60,"0000000000000000"],[44,"80763981ffffffff28d5e50f8088ffff"],[303,"7002e7068088ffffc0733981ffffffff"],[45,"0000000000000000"],[46,"c0733981ffffffff7002e7068088ffff"],[100,"22e0feff0000000004e5feff00000000e003e7068088ffff"],[151,"22e0feff00000000"],[20,"1000000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"093a313f01000000"],[47,"0000000000000000"],[43,"0000000000000000"]],[[48,"e0c53f81ffffffff0000000000000000"],[305,"50d5e50f8088ffffc09d3981ffffffff"],[49,"0000000000000000"],[6,"9f3dc05701000000"],[302,"28d5e50f8088ffff80763981ffffffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"9f3dc05701000000"],[50,"c09d3981ffffffff50d5e50f8088ffff"],[6,"9f3dc05701000000"],[63,"0000000000000000"],[44,"80763981ffffffff28d5e50f8088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[6,"9f3dc05701000000"],[100,"89e0feff000000006be5feff00000000e003e7068088ffff"],[100,"89e0feff000000004deafeff000000006803e7068088ffff"],[49,"0000000000000000"],[303,"7002e7068088ffffc0733981ffffffff"],[45,"0000000000000000"],[46,"c0733981ffffffff7002e7068088ffff"],[100,"89e0feff000000006be5feff00000000e003e7068088ffff"],[151,"89e0feff00000000"],[20,"2300000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[16,"a000000000000000"],[100,"89e0feff0000000062effeff000000009003e7068088ffff"],[6,"9f3dc05701000000"],[100,"89e0feff000000006be5feff00000000e003e7068088ffff"],[48,"e0c53f81ffffffff0000000000000000"],[49,"0000000000000000"],[6,"9f3dc05701000000"],[47,"0000000000000000"],[6,"9f3dc05701000000"],[63,"0000000000000000"],[48,"e0c53f81ffffffff0000000000000000"],[6,"9f3dc05701000000"],[100,"89e0feff000000006be5feff00000000e003e7068088ffff"],[100,"89e0feff000000004deafeff000000006803e7068088ffff"],[49,"0000000000000000"],[51,"0000000000000000"]],[],[]],"id":"w7_mixed","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4},{"addr":"20010db8000000000000000000000000","cidr":32,"family":6}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"keepalive":5,"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_observe"},{"family":4,"message":"02000000040302010d0c0b0aff2ee45601ec1b67310c7790404585ae697331eee1c1f8cf2419731c1fff3e6bc50a223d86b8a86bf41a2bd3a1ab84f892fd9bacbc45bda46dc025e6cac665a500000000000000000000000000000000","op":"wg_inject","port":51820},{"items":[{"family":4,"kind":"inject","message":"040000000d0c0b0a0000000000000000973bf9003cd64074998ee8a105b8faadd9ac555c88a29f9adfcfbfec838f0d009ad4f052d7c619152641ab1e69b5ce80","port":51820},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"6d747b828990979ea5acb3bac1c8cfd6dde4ebf2f900070e151c232a31383f464d545b626970777e858c939aa1a8afb6bdc4cbd2d9e0e7eef5fc030a11181f26"}},{"family":4,"kind":"inject","message":"040000000d0c0b0a01000000000000007f7ee2dd92df1a56bb173dcac9921476ffcea61fd7d42d770c282e9d0e709499eff6ee04e219cee7b6e8e592d5658184","port":51820},{"kind":"xmit","packet":{"dst":"0a000001","family":4,"payload":"8c939aa1a8afb6bdc4cbd2d9e0e7eef5fc030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c"}}],"op":"wg_batch","wait_ms":400},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["init_ephemeral","8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],["tai64n_now","803bb16a00000000b168de3a00000000"],["index_draw","0d0c0b0a"]],"version":1}''')


class EncryptWorkerRingPoll(unittest.TestCase):
    def test_pending_poll_runs_at_the_encrypt_workers_ring_poll(self):
        self.assertIsNone(replay_raw(INT_R_W7_MIXED_CMP))

    def test_the_poll_before_the_section_still_runs(self):
        t = copy.deepcopy(INT_R_W7_MIXED_CMP)
        op = t['hidden'][4]
        self.assertEqual([r[0] for r in op[11:18]], [44, 48, 6, 100, 100, 49, 303])
        t['hidden'][4] = op[:11] + op[12:17] + [op[11]] + op[17:]   # the order of the other runs
        self.assertIsNone(replay_raw(t))

    def test_a_net_rx_section_with_no_poll_pending_is_a_mismatch(self):
        t = copy.deepcopy(INT_R_W7_MIXED_CMP)
        op = t['hidden'][4]
        t['hidden'][4] = op[:17] + op[12:17] + op[17:]   # the poll's section a second time: nothing is pending
        self.assertIn('hidden-input records disagree', replay_raw(t))


# B3 (docs/2026-10-15-design-b3-timer-wheel.md, sections 3.4 and 9): a capture
# from the s5 oracle (the kind-313 and kind-314 records in place, sites 428 and
# 429): d3_retransmit, whose advance (operation 4) fires the retransmit timer
# (site 102) and whose send worker re-arms it. The controls of E1's must-fire
# direction and E2's lookahead (mutant B3-M4: `requireNothingDue` a no-op
# passes both altered captures, so this is its evaluator control).
D3_RETRANSMIT_S5 = json.loads(r'''{"arm_records":true,"expect":["fired:wg_expired_retransmit_handshake","wg_packet_send_staged_packets.no_keypair=1","wg_packet_send_queued_handshake_initiation.not_retry=0","wg_expired_retransmit_handshake.give_up=0"],"hidden":[[[150,"799c030001000000"],[5,"2d6b575022010000"],[150,"799c030001000000"],[128,"929c030001000000"]],[[128,"b99c030001000000"]],[[6,"35b15e6422010000"],[300,"3002e7068088ffffe0ae3981ffffffff"],[40,"e0ae3981ffffffff3002e7068088ffff"],[6,"35b15e6422010000"],[7,"35b15e6422010000"],[1,"8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],[3,"803bb16a00000000b168de3a00000000"],[4,"0d0c0b0a00000000"],[8,"35b15e6422010000"],[151,"cd9c030001000000"],[21,"41b1978a567734d9b0148c37798e38ae"],[20,"e0c9020000000000"],[48,"10044081ffffffff0000000000000000"],[49,"0000000000000000"],[424,"cd9c030001000000"],[14,"a900000000000000"],[100,"cd9c030001000000e5a10300010000004003e7068088ffff"],[428,"cd9c0300010000004003e7068088ffff"],[429,"880000000000000000a20300010000004003e7068088ffff"],[41,"0000000000000000"],[128,"e69c030001000000"]],[[128,"609d030001000000"]],[[101,"639d0300010000000da3030001000000"],[102,"709c3981ffffffff4003e7068088ffff"],[150,"0ea3030001000000"],[6,"af151ae223010000"],[300,"3002e7068088ffffe0ae3981ffffffff"],[103,"0000000000000000"],[40,"e0ae3981ffffffff3002e7068088ffff"],[6,"af151ae223010000"],[7,"af151ae223010000"],[1,"3994534fa7d1a028726cae767b2d59a14aea8ddd263dfd0cc2d7e5273dddc87c"],[3,"8043d06a00000000da86821c00000000"],[4,"3901019f00000000"],[8,"af151ae223010000"],[151,"0ea3030001000000"],[20,"0d01000000000000"],[48,"10044081ffffffff0000000000000000"],[49,"0000000000000000"],[424,"0ea3030001000000"],[14,"5800000000000000"],[100,"0ea30300010000000ca80300010000004003e7068088ffff"],[428,"0ea30300010000004003e7068088ffff"],[429,"a10000000000000040a80300010000004003e7068088ffff"],[41,"0000000000000000"],[128,"26a3030001000000"]],[[128,"95a3030001000000"]],[]],"id":"d3_retransmit","ops":[{"config":{"listen_port":51820,"peers":[{"allowed_ips":[{"addr":"0a000000","cidr":8,"family":4},{"addr":"20010db8000000000000000000000000","cidr":32,"family":6}],"endpoint":{"addr":"7f000001","family":4,"port":51999},"public_key":"0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20"}],"private_key":"1111111111111111111111111111111111111111111111111111111111111111"},"op":"wg_set"},{"op":"wg_up"},{"op":"wg_xmit","packet":{"dst":"0a000001","family":4,"payload":"20272e353c434a51585f666d747b828990"}},{"op":"wg_observe"},{"op":"wg_advance","ticks":1450},{"op":"wg_observe"},{"op":"wg_get"}],"steer":[["init_ephemeral","8182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0"],["tai64n_now","803bb16a00000000b168de3a00000000"],["index_draw","0d0c0b0a"],["init_ephemeral","draw"],["tai64n_now","draw"],["index_draw","draw"]],"version":1}''')


class TimerWheelFiring(unittest.TestCase):
    def test_s5_capture_replays(self):
        self.assertIsNone(replay_raw(D3_RETRANSMIT_S5))

    def test_a_due_timer_whose_section_never_appears_is_a_mismatch(self):
        t = copy.deepcopy(D3_RETRANSMIT_S5)
        op = t['hidden'][4]
        # keep the advance (site 101) and the end-of-wait read (128): the firing and the work it queued are gone
        t['hidden'][4] = [r for r in op if r[0] in (101, 128)]
        out = replay_raw(t)
        self.assertIsNotNone(out, 'a due timer without its section was accepted (E1 item 3)')
        self.assertIn('hidden-input records disagree', out)
        self.assertIn('did not fire', out)

    def test_a_due_timer_whose_section_appears_later_is_the_deferral(self):
        t = copy.deepcopy(D3_RETRANSMIT_S5)
        op = t['hidden'][4]
        block = [r for r in op if r[0] not in (101, 128)]
        t['hidden'][4] = [r for r in op if r[0] in (101, 128)]
        t['hidden'][5] = block + t['hidden'][5]   # the pass ran after the read, in the next operation's wait
        out = replay_raw(t)
        self.assertIsNotNone(out, 'a deferred timer softirq was accepted (E2)')
        self.assertIn('unsupported', out)
        self.assertIn('deferred past the end-of-wait read', out)

class FibBoot(unittest.TestCase):
    """Lane C: the mirror's boot trie (built by the C's own inserts at `lo` up)
    is the shape the guest reads back from /proc/net/fib_trie at every
    trace's start (harness/linux.py EXPECTED_FIB_TRIE_BOOT)."""

    def test_boot_shape_matches_the_fixture_fact(self):
        from harness.linux import EXPECTED_FIB_TRIE_BOOT
        result = subprocess.run([MODEL, '--fib-boot'], capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(json.loads(result.stdout.decode()), EXPECTED_FIB_TRIE_BOOT)

