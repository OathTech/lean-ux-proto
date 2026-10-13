"""Reconstruct small proof-campaign witnesses from tracked fixtures.

Print one runner JSON input; no guest, kernel run, or retained run artifact.
"""
import argparse
import ast
import copy
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def recorded_fixture(name):
    tree = ast.parse((ROOT / "evaluator/test_model_replay.py").read_text())
    for node in tree.body:
        if (isinstance(node, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)):
            call = node.value
            if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
                    and isinstance(call.func.value, ast.Name)
                    and call.func.value.id == "json" and call.func.attr == "loads"
                    and len(call.args) == 1):
                raise ValueError(f"fixture {name} is no longer a literal json.loads call")
            return json.loads(ast.literal_eval(call.args[0]))
    raise ValueError(f"missing recorded fixture {name}")


def add_wait_bounds(trace, operation_indices):
    """Synthetic monotone wait bounds, site 128 (record kind 310).

    These are reconstructed inputs, not clock words from the Linux capture.
    No timer section occurs in these witnesses; the bounds precede every
    placeholder-armed expiry.
    """
    for bound, index in enumerate(operation_indices, 1):
        records = trace["hidden"][index]
        if any(record[0] == 128 for record in records):
            raise ValueError(f"operation {index} already contains an end-of-wait record")
        records.append([128, bound.to_bytes(8, "little").hex()])


def inclusive_floor():
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    window = json.loads((ROOT / "corpus/wireguard/rx_window.json").read_text())
    data_records = trace["hidden"][4]
    trace["id"] = "r1_inclusive_floor"
    trace["ops"] = trace["ops"][:4] + window["ops"][4:6]
    trace["hidden"] = trace["hidden"][:4] + [copy.deepcopy(data_records) for _ in range(2)]
    clocks = iter(["dde80fec1e000000", "1d2b1fec1e000000"])
    for record in trace["hidden"][5]:
        if record[0] == 6:
            record[1] = next(clocks)
    if next(clocks, None) is not None:
        raise ValueError("recorded data path no longer has exactly two clock reads")
    for records in trace["hidden"]:
        for record in records:
            if record[0] in {40, 42, 44, 46, 48, 50} and len(record[1]) == 16:
                record[1] += "0000000000000000"
    trace.pop("steer")
    trace["dst_cache_records"] = False
    trace["arm_records"] = False
    add_wait_bounds(trace, range(len(trace["ops"])))
    return trace


def stale_dump_cursor():
    """Exact synthetic choice records; this is not a Linux capture."""
    def peers(first, count):
        return {"op": "wg_set", "config": {"peers": [
            {"public_key": bytes([n]).hex() + "00" * 31}
            for n in range(first, first + count)
        ]}}

    def zero(site, size=8):
        return [site, "00" * size]

    trace = {
        "version": 1,
        "id": "r2_stale_dump_cursor",
        "dst_cache_records": False,
        "ops": [peers(1, 14), peers(15, 14), {"op": "wg_get_start"},
                {"op": "wg_delete"}, {"op": "wg_create"},
                peers(101, 14), peers(115, 13), {"op": "wg_get_recv"}],
        "hidden": [
            [zero(5) for _ in range(14)],
            [zero(5) for _ in range(14)],
            [zero(170)], [zero(124)],
            [zero(120), zero(121, 32), zero(122, 16), zero(123, 16),
             zero(126), zero(126)],
            [zero(5) for _ in range(14)],
            [zero(5) for _ in range(13)], [],
        ],
    }
    add_wait_bounds(trace, [0, 1, 5, 6])
    return trace


def stale_dump_cursor_orphan():
    """Retain a trie owner after the stale cursor releases its replacement peer."""
    trace = stale_dump_cursor()
    trace["id"] = "r2_stale_dump_cursor_orphan"
    trace["ops"][6]["config"]["peers"][-1]["allowed_ips"] = [
        {"family": 4, "addr": "0a000000", "cidr": 8}]
    return trace


def fixture_session():
    """Derive the tracked D1 session with the harness's actual Noise helper."""
    sys.path.insert(0, str(ROOT))
    from harness import noise
    device, peer = bytes([0x11]) * 32, bytes([0x22]) * 32
    initiation = noise.steered_initiation(noise.public_key(peer), device,
        bytes(range(0x81, 0xa1)), 1790000000, 987654321, 0x0a0b0c0d)
    return noise.response(initiation, peer, bytes([0x44]) * 32, None, 0x01020304)


def receive_wire_limit(strict=False):
    """Reconstructed records with the existing R packet or generated R+1 packet."""
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    limit = json.loads((ROOT / "corpus/wireguard/d2_rx_reject_after_messages.json").read_text())
    records = copy.deepcopy(trace["hidden"][4])
    clocks = [i for i, record in enumerate(records) if record[0] == 6]
    if len(clocks) != 2:
        raise ValueError("recorded data path no longer has exactly two clock reads")
    # Replay rejection skips receive completion and its second age-test read.
    del records[clocks[1]]
    trace["id"] = "r5_rx_wire_limit"
    trace["ops"] = trace["ops"][:4] + [limit["ops"][4]]
    if strict:
        response = fixture_session()
        from harness import noise
        if response.message.hex() != trace["ops"][3]["message"]:
            raise ValueError("derived Noise session differs from tracked response")
        reject_after_messages = (2**64 - 1) - (8192 - 64) - 1
        counter = reject_after_messages + 1
        trace["id"] = "r5_rx_wire_past_limit"
        trace["ops"][4]["message"] = noise.data_message(
            response.initiator_receiving, response.initiator_index, counter, b"").hex()
    trace["hidden"] = trace["hidden"][:4] + [records]
    for operation in trace["hidden"]:
        for record in operation:
            if record[0] in {40, 42, 44, 46, 48, 50} and len(record[1]) == 16:
                record[1] += "0000000000000000"
    trace.pop("steer")
    trace["dst_cache_records"] = False
    trace["arm_records"] = False
    add_wait_bounds(trace, range(len(trace["ops"])))
    return trace


def post_clear_transport():
    """Synthetic timer ordering with deliberately incoherent coarse/jiffies clocks."""
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    response = copy.deepcopy(trace["hidden"][3])
    if [r[0] for r in response] != [48, 49, 42, 13, 15, 6, 60, 44, 45, 46, 20, 48, 49, 6, 47, 43]:
        raise ValueError("recorded response operation no longer matches the source recipe")
    def zero(site, words=1):
        return [site, "00" * (8 * words)]
    tail = [zero(112, 2), copy.deepcopy(response[5]), zero(113),
            zero(108, 2), zero(109), zero(110, 2), zero(111)]
    tail += copy.deepcopy(response[7:13] + [response[14]])
    trace["id"] = "r5_post_clear_transport"
    trace["ops"] = trace["ops"][:4] + [{"op": "wg_observe"}]
    trace["hidden"] = trace["hidden"][:4] + [tail]
    for operation in trace["hidden"]:
        for record in operation:
            if record[0] in {40, 42, 44, 46, 48, 50} and len(record[1]) == 16:
                record[1] += "0000000000000000"
    trace.pop("steer")
    trace["dst_cache_records"] = False
    trace["arm_records"] = False
    add_wait_bounds(trace, range(4))
    trace["hidden"][4].append([128, (135005).to_bytes(8, "little").hex()])
    return trace


def delayed_encryption(clear=False):
    """Generated coherent coarse/jiffies inputs, not a captured kernel run."""
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    data = json.loads((ROOT / "corpus/wireguard/d3_keepalive_rearm_deleted.json").read_text())
    initial_jiffies = 2**32 - 75000
    after_expiry = 673 if clear else 322
    wait_end = after_expiry + 1
    jiffies = lambda seconds: initial_jiffies + seconds * 250
    def record(site, *words):
        return [site, b"".join(word.to_bytes(8, "little") for word in words).hex()]
    def clock(seconds):
        return record(6, seconds * 10**9)
    arm_delays = {17: 1000 * 250, 18: 1250, 19: 135000, 20: 2500}
    def arm(seconds, timer, extra=0):
        now = jiffies(seconds)
        delay = arm_delays[timer] + extra
        result = record(100, now, now + delay, timer)
        return result
    def retime(records, seconds):
        result = copy.deepcopy(records)
        for r in result:
            if r[0] in {5, 6, 7, 8, 13}:
                r[1] = (seconds * 10**9).to_bytes(8, "little").hex()
            if r[0] in {40, 42, 44, 46, 48, 50} and len(r[1]) == 16:
                r[1] += "0000000000000000"
        return result
    setup = retime(trace["hidden"][0], 130)
    up = []
    for r in retime(trace["hidden"][1], 131):
        if r[0] == 8:
            up.append(arm(131, 17))
        up.append(r)
        if r[0] == 14:
            up.append(arm(131, 18, 83 * bytes.fromhex(r[1])[0] // 256))
    response, clocks = [], 0
    for r in retime(trace["hidden"][3], 132):
        response.append(r)
        if r[0] == 13:
            response.append(arm(132, 19))
        if r[0] == 6:
            clocks += 1
            if clocks == 1:
                response.append(arm(132, 17))
        if r[0] == 46:
            response.append(arm(132, 17))
    receives = []
    for seconds in [133, 134]:
        records, clocks = [], 0
        for r in retime(trace["hidden"][4], seconds):
            records.append(r)
            if r[0] == 6:
                clocks += 1
                if clocks == 2:
                    records.append(arm(seconds, 17))
                    if seconds == 133:
                        records.append(arm(seconds, 20))
        if clocks != 2:
            raise ValueError("receive fixture no longer has two age reads")
        receives.append(records)
    tail = [record(101, jiffies(134), jiffies(311)),
            record(104, 0, 20), clock(311), arm(311, 20), record(105, 0),
            record(104, 0, 20), clock(after_expiry), clock(after_expiry), record(105, 0),
            record(44, 0, 0), record(45, 0), record(46, 0, 0), arm(after_expiry, 17),
            record(20, 0), record(48, 0, 0), record(49, 0), record(47, 0)]
    # The old keypair occupies the original index. The new handshake uses
    # a fresh draw and runs only after the old packet's encryption/transmit.
    for r in retime(trace["hidden"][1][1:], after_expiry):
        if r[0] == 1:
            r[1] = bytes(range(0xc1, 0xe1)).hex()
        if r[0] == 3:
            r = record(3, 1790000000 + after_expiry - 131, 987654321)
        if r[0] == 4:
            r = record(4, 0x11223344)
        if r[0] == 14:
            r = record(14, 1)
        if r[0] == 21:
            continue
        if r[0] == 8:
            tail.append(arm(after_expiry, 17))
        tail.append(r)
        if r[0] == 14:
            tail.append(arm(after_expiry, 18))
    # ARM_RECORDS also requires queue-work records. Each work unit keeps
    # one identity across queueing and dispatch; timer identities are separate.
    def before(records, site, queued, occurrence=1):
        indices = [i for i, r in enumerate(records) if r[0] == site]
        if len(indices) < occurrence:
            raise ValueError(f"missing insertion boundary {site}/{occurrence}")
        records.insert(indices[occurrence - 1], queued)
    before(up, 40, record(300, 1, 0))
    before(response, 49, record(301, 2, 0))
    before(response, 100, record(302, 3, 0), 2)
    before(response, 45, record(303, 4, 0))
    for records in receives:
        before(records, 49, record(305, 5, 0))
    before(tail, 100, record(302, 3, 0))
    before(tail, 105, record(300, 1, 0), 2)
    before(tail, 45, record(303, 4, 0))
    if clear:
        crypt_start = next(i for i, r in enumerate(tail) if r[0] == 44)
        tail[crypt_start:crypt_start] = [record(108, 0, 19), record(310, 6, 0),
            record(109, 0), record(110, 0, 6), record(111, 0)]
    units = {40: 1, 42: 2, 44: 3, 46: 4, 50: 5}
    for records in [up, response, *receives, tail]:
        for r in records:
            if r[0] in units:
                r[1] = r[1][:16] + units[r[0]].to_bytes(8, "little").hex()
    trace["id"] = "r5_coherent_post_clear" if clear else "r5_delayed_encryption"
    trace["ops"] = trace["ops"][:4] + copy.deepcopy(data["ops"][4:6]) + [
        {"op": "wg_advance", "ticks": (311 - 134) * 250}]
    trace["ops"][0]["config"]["peers"][0]["keepalive"] = 1000
    trace["hidden"] = [setup, up, [], response, *receives, tail]
    for records, seconds in zip(trace["hidden"], [130, 131, 131, 132, 133, 134, wait_end]):
        records.append(record(128, jiffies(seconds)))
    trace.pop("steer")
    trace["arm_records"] = True
    trace["dst_cache_records"] = False
    # Check the generated clock discipline and every explicit arm. These
    # arithmetic checks do not establish that Linux produced this schedule.
    def check_clock(condition, message):
        if not condition:
            raise ValueError(message)
    last_ns, last_jiffies = 0, initial_jiffies
    for records in trace["hidden"]:
        for site, encoded in records:
            raw = bytes.fromhex(encoded)
            words = [int.from_bytes(raw[n:n+8], "little") for n in range(0, len(raw), 8)]
            if site in {5, 6, 7, 8, 13}:
                check_clock(words[0] >= last_ns, "coarse clock moved backward")
                last_ns = words[0]
            if site == 100:
                now, expiry, timer = words
                check_clock(now >= last_jiffies, "timer-arm jiffies moved backward")
                check_clock(expiry - now in ({1250, 1269} if timer == 18 else {arm_delays[timer]}),
                    "timer arm has the wrong delay")
                check_clock(now == initial_jiffies + last_ns // 4000000,
                    "timer-arm jiffies disagree with the preceding coarse clock")
                last_jiffies = now
            if site == 101:
                check_clock(words[0] >= last_jiffies and words[1] - words[0] == 44250,
                    "advance record has the wrong start or duration")
                last_jiffies = words[1]
            if site == 128:
                check_clock(words[0] >= last_jiffies, "end-of-wait jiffies moved backward")
                check_clock(words[0] >= initial_jiffies + last_ns // 4000000,
                    "end-of-wait precedes the last coarse clock")
                last_jiffies = words[0]
    return trace


def gro_reorder():
    """Generated explicit schedule, not a Linux capture: held ACK then normal SYN."""
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    response = fixture_session()
    from harness import noise
    if response.message.hex() != trace["ops"][3]["message"]:
        raise ValueError("derived Noise session differs from tracked response")
    src = bytes.fromhex("0a000002")
    held = noise.ipv4_tcp(src, noise.WG0_ADDR4, 40001, 80, 7, 0x55667788, 16, b"H")
    normal = noise.ipv4_tcp(src, noise.WG0_ADDR4, 40002, 443, 0x11223344, 0, 2)
    items = [{"kind": "inject", "family": 4, "port": 51820,
              "message": noise.data_message(response.initiator_receiving,
                  response.initiator_index, nonce, packet).hex()}
             for nonce, packet in enumerate([held, normal])]
    def record(site, value=0):
        size = 16 if site in {40, 42, 44, 46, 48, 50} else 8
        return [site, value.to_bytes(size, "little").hex()]
    sites = [48, 49, 48, 49, 50, 6, 6, 48, 6, 6, 6, 6, 49,
             51, 44, 45, 46, 48, 49, 16, 6, 48, 49, 6, 47]
    records = [record(site, 133000000000 if site == 6 else 160 if site == 16 else 0)
               for site in sites]
    trace["id"] = "r4_gro_reorder"
    trace["ops"] = trace["ops"][:4] + [{"op": "wg_batch", "items": items,
                                               "wait_ms": 400}, {"op": "wg_observe"}]
    trace["hidden"] = trace["hidden"][:4] + [records, []]
    for operation in trace["hidden"]:
        for r in operation:
            if r[0] in {40, 42, 44, 46, 48, 50} and len(r[1]) == 16:
                r[1] += "0000000000000000"
    trace.pop("steer")
    trace["dst_cache_records"] = False
    trace["arm_records"] = False
    add_wait_bounds(trace, range(len(trace["ops"])))
    return trace


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    cases = {"r1-inclusive-floor": inclusive_floor,
             "r2-stale-dump-cursor": stale_dump_cursor,
             "r2-stale-dump-cursor-orphan": stale_dump_cursor_orphan,
             "r4-gro-reorder": gro_reorder,
             "r5-rx-wire-limit": receive_wire_limit,
             "r5-rx-wire-past-limit": lambda: receive_wire_limit(True),
             "r5-delayed-encryption": delayed_encryption,
             "r5-coherent-post-clear": lambda: delayed_encryption(True),
             "r5-post-clear-transport": post_clear_transport}
    parser.add_argument("case", choices=cases)
    args = parser.parse_args()
    print(json.dumps(cases[args.case](), separators=(",", ":")))
