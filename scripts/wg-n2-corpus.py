#!/usr/bin/env python3
"""Writes workstream W2's traces (multi-message netlink dumps,
docs/2026-10-06-w1-w2-netlink.md sections 4.4, 4.7 and 4.8) into
corpus/wireguard as n2_*.json, and measures their label counts against the
mirror's per-trace cap (4.7: measure before raising MAX_BRANCHES).

Every trace configures a down wg0 (no wg_up) and reads it back with the
stepped dump (`wg_get_start` / `wg_get_recv` on the fixture's second
generic-netlink socket), so one dump call runs per operation and the
per-message observation shows each chunk as Linux built it; `wg_get` (op 9)
at the end reads the same state coalesced. Two families:

- boundary traces (4.4 rows 2-4, 4.8): filler peers consume the first chunk's
  room so that a chosen put of the target peer fails with a chosen room
  before it. The put model of section 2.5 is replicated here (`emulate`); a
  wrong table makes a trace miss its `expect` label, not pass falsely;
- interleaving traces (4.4 rows 1, 5-13): a `wg_set` between two dump calls
  (the consistency flag, a changed allowed-IPs sequence, the two stale-cursor
  shapes, the dead cursor), the repeated device part, 256 allowed IPs
  accumulated 32 per set (4.7), the DONE that does not fit its chunk, a start
  error. `-EBUSY`, `-EAGAIN` and the receive of a lone DONE are outside the
  mirror's domain [AGENT, coordinator 2026-10-12] and have no trace.

The output is deterministic.
"""
import importlib.util
import itertools
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from evaluator.protocol import MAX_BRANCHES  # noqa: E402
from harness import noise  # noqa: E402
from harness.trace import validate_trace  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

KEY = d1.key(d1.DEVICE)
V4 = {"family": 4, "addr": "7f000001", "port": 51999}
V6 = {"family": 6, "addr": "00000000000000000000000000000001", "port": 51999}
ENDPOINT = {None: None, 4: V4, 6: V6}


def pub(k):
    """The public key of the private key k repeated; distinct per peer."""
    return d1.key(noise.public_key(bytes([k]) * 32))


# --- the put model (2.5): nla_total_size(len) = NLA_ALIGN(4 + len) ---------
def nla(n):
    return (4 + n + 3) // 4 * 4


ROOM = 3776                     # NLMSG_GOODSIZE: a fresh chunk's room
HEADER = 20                     # genlmsg_put: nlmsghdr + genlmsghdr
DEVICE = 4 * 8                  # listen_port, fwmark, ifindex, ifname "wg0"
IDENTITY = 2 * nla(32)          # private and public key
NEST = nla(0)
FIRST = [("preshared_key", nla(32)), ("last_handshake", nla(16)), ("keepalive", nla(2)),
         ("tx_bytes", nla(8)), ("rx_bytes", nla(8)), ("protocol_version", nla(4))]
EP = {None: 0, 4: nla(16), 6: nla(28)}
IP = {4: NEST + nla(1) + nla(2) + nla(4), 6: NEST + nla(1) + nla(2) + nla(16)}
DONE = 20
PEER_FIXED = NEST + nla(32) + sum(size for _, size in FIRST)   # 136 without an endpoint


def peer_size(p):
    """A peer's whole dump size on a fresh cursor."""
    ips = p["ips"]
    return PEER_FIXED + EP[p["ep"]] + (NEST + sum(IP[f] for f in ips) if ips else 0)


def get_peer(p, ctx, room):
    """get_peer (netlink.c:105-197) without interleaving: (room after, outcome,
    IPs put, the decision labels of the failed put)."""
    r0 = room
    if room < NEST:
        return r0, "cancelled", 0, ["get_peer.no_nest=1"]
    room -= NEST
    if room < nla(32):
        return r0, "cancelled", 0, ["get_peer.put_public_key_failed=1"]
    room -= nla(32)
    node = ctx["ip"]
    if node is None:
        for name, size in FIRST:
            if room < size:
                return r0, "cancelled", 0, [f"get_peer.put_{name}_failed=1"]
            room -= size
        if p["ep"] is not None:
            if room < EP[p["ep"]]:
                return r0, "cancelled", 0, ["get_peer.put_endpoint_failed=1"]
            room -= EP[p["ep"]]
        if not p["ips"]:
            return room, "complete", 0, ["get_peer.no_allowedips=1"]
        node = 0
    if room < NEST:
        return r0, "cancelled", 0, ["get_peer.allowedips_nest_failed=1"]
    room -= NEST
    put = 0
    for j in range(node, len(p["ips"])):
        family = p["ips"][j]
        if room < IP[family]:
            if room < NEST:
                label = "get_allowedips.no_nest=1"
            elif room - NEST < nla(1):
                label = "get_allowedips.put_cidr_failed=1"
            elif room - NEST - nla(1) < nla(2):
                label = "get_allowedips.put_family_failed=1"
            else:
                label = "get_allowedips.put_addr_failed=1"
            ctx["ip"] = j
            return room, "split", put, [label, f"get_allowedips.inet6_length={int(family == 6)}",
                                        "get_peer.get_allowedips_failed=1"]
        room -= IP[family]
        put += 1
    ctx["ip"] = None
    return room, "complete", put, []


def emulate(peers, identity=True):
    """The chunks of one uninterrupted dump: per chunk, whether the device
    part is present, the peers (index, outcome, IPs put), the labels of the
    puts that failed, and whether the DONE fit."""
    ctx = {"peer": None, "ip": None}
    chunks = []
    while True:
        room = ROOM - HEADER
        chunk = {"device": ctx["peer"] is None, "peers": [], "labels": []}
        if chunk["device"]:
            room -= DEVICE + (IDENTITY if identity else 0)
        room -= NEST
        done = True
        start = 0 if ctx["peer"] is None else ctx["peer"] + 1
        for i in range(start, len(peers)):
            room, outcome, put, labels = get_peer(peers[i], ctx, room)
            chunk["labels"] += labels
            if outcome == "complete":
                chunk["peers"].append((i, outcome, put))
                ctx["peer"] = i
            else:
                if outcome == "split":
                    chunk["peers"].append((i, outcome, put))
                done = False
                break
        chunk["done"] = done and room >= DONE
        chunk["room"] = room
        chunks.append(chunk)
        if done:
            return chunks


def fillers(consume, kinds=(None, 4, 6)):
    """Peers consuming exactly `consume` bytes of a fresh chunk: at most three,
    each with at most 32 allowed IPs (one wg_set), the fewest IPs first."""
    best = None
    for count in (1, 2, 3):
        for eps in itertools.product(kinds, repeat=count):
            for with_ips in itertools.product((0, 1), repeat=count):
                fixed = sum(PEER_FIXED + EP[ep] + NEST * w for ep, w in zip(eps, with_ips))
                slots = sum(with_ips)
                rest = consume - fixed
                if rest < 0 or (slots == 0 and rest != 0):
                    continue
                for v6 in range(0, 32 * slots + 1):
                    rest4 = rest - IP[6] * v6
                    if rest4 < 0 or rest4 % IP[4]:
                        continue
                    v4 = rest4 // IP[4]
                    if v4 + v6 > 32 * slots or (slots and v4 + v6 < slots):
                        continue
                    score = (v4 + v6, count, v6)
                    if best is None or score < best[0]:
                        best = (score, eps, with_ips, v4, v6)
    if best is None:
        raise ValueError(f"no filler for {consume} bytes")
    _, eps, with_ips, v4, v6 = best
    pool, slots = [6] * v6 + [4] * v4, sum(with_ips)
    peers = []
    for ep, w in zip(eps, with_ips):
        ips = []
        if w:
            n = min(32, len(pool) - (slots - 1))   # at least one each, at most 32
            ips, pool, slots = pool[:n], pool[n:], slots - 1
        peers.append({"ep": ep, "ips": ips})
    assert not pool and sum(peer_size(p) for p in peers) == consume, (consume, peers)
    return peers


# --- trace construction ------------------------------------------------------
class Addresses:
    """Distinct prefixes: 10.x.y.0/24 and 2001:db8:n::/48 (an insert of an
    existing prefix moves it instead of adding it)."""

    def __init__(self):
        self.count = 0

    def ip(self, family):
        n = self.count
        self.count += 1
        if family == 4:
            return {"family": 4, "addr": bytes([10, n >> 8, n & 0xff, 0]).hex(), "cidr": 24}
        return {"family": 6, "addr": "20010db8" + f"{n:04x}" + "0" * 20, "cidr": 48}


def wg_set(config, device=None):
    op = {"op": "wg_set", "config": config}
    if device is not None:
        op["device"] = device
    return op


def start(device=None):
    op = {"op": "wg_get_start"}
    if device is not None:
        op["device"] = device
    return op


RECV = {"op": "wg_get_recv"}
GET = {"op": "wg_get"}


def materialize(peers, addresses, first_key=0x40):
    """Peer configurations for one wg_set: keys 0x40.., endpoints, IPs."""
    configs = []
    for k, p in enumerate(peers):
        config = {"public_key": pub(first_key + k)}
        if p["ep"] is not None:
            config["endpoint"] = ENDPOINT[p["ep"]]
        if p["ips"]:
            config["allowed_ips"] = [addresses.ip(f) for f in p["ips"]]
        configs.append(config)
    return configs


def stepped(chunks):
    """The receives of a dump: one per data chunk; the DONE that did not fit
    stays queued (its receive is outside the domain)."""
    return [start()] + [RECV] * len(chunks)


def boundary(name, consume, target, label, extra=()):
    """Fillers consuming `consume` bytes, then the target peer; the emulator
    confirms the first failed put is `label`."""
    peers = fillers(consume) + [target]
    chunks = emulate(peers)
    failed = [l for c in chunks for l in c["labels"]]
    assert failed and failed[0] == label, (name, failed[:3], chunks)
    assert len(chunks) == 2 and chunks[1]["done"], (name, chunks)
    addresses = Addresses()
    config = {"private_key": KEY, "listen_port": d1.PORT, "peers": materialize(peers, addresses)}
    expect = [label, "wg_get_device_dump.get_peer_failed=1", "wg_get_device_dump.done=1", *extra]
    return name, {"ops": [wg_set(config), *stepped(chunks), GET], "expect": expect}


def accumulate(first_key, count, family, addresses, ep=6):
    """`count` allowed IPs on one peer, 32 per wg_set (4.7); the first set
    carries the identity."""
    ops, remaining = [], count
    while remaining > 0:
        n = min(32, remaining)
        peer = {"public_key": pub(first_key), "allowed_ips": [addresses.ip(family) for _ in range(n)]}
        if not ops:
            peer["endpoint"] = ENDPOINT[ep]
            ops.append(wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": [peer]}))
        else:
            ops.append(wg_set({"peers": [peer]}))
        remaining -= n
    return ops


def traces():
    out = []
    room_after_device = ROOM - HEADER - DEVICE - IDENTITY - NEST   # 3648
    # 4.4 row 2: each get_allowedips put failing, by the room before the IP
    # (the target peer's first-visit part and nest fit, its first IP does not)
    target = {"ep": 4, "ips": [4, 4, 4]}
    for room, label in [(0, "no_nest"), (4, "put_cidr_failed"), (8, "put_cidr_failed"), (12, "put_family_failed"),
                        (16, "put_family_failed"), (20, "put_addr_failed"), (24, "put_addr_failed")]:
        consume = room_after_device - (PEER_FIXED + EP[4] + NEST) - room
        out.append(boundary(f"n2_aip_room{room}_v4", consume, target, f"get_allowedips.{label}=1",
                            ["get_allowedips.inet6_length=0"]))
    target6 = {"ep": 4, "ips": [6, 6, 6]}
    for room in (28, 32, 36):
        consume = room_after_device - (PEER_FIXED + EP[4] + NEST) - room
        out.append(boundary(f"n2_aip_room{room}_v6", consume, target6, "get_allowedips.put_addr_failed=1",
                            ["get_allowedips.inet6_length=1"]))
    # 4.4 row 3: each first-visit put failing, by the room before the peer
    # (the peer is absent from chunk 1, complete in chunk 2)
    firsts = [("no_nest", 0, 4), ("put_public_key_failed", 20, 4), ("put_preshared_key_failed", 56, 4),
              ("put_last_handshake_failed", 84, 4), ("put_keepalive_failed", 96, 4), ("put_tx_bytes_failed", 108, 4),
              ("put_rx_bytes_failed", 120, 4), ("put_protocol_version_failed", 128, 4),
              ("put_endpoint_failed", 144, 4), ("put_endpoint_failed", 160, 6)]
    for label, room, ep in firsts:
        name = f"n2_first_{label.replace('put_', '').replace('_failed', '')}" + ("_v6" if ep == 6 else "")
        out.append(boundary(name, room_after_device - room, {"ep": ep, "ips": [4, 4]}, f"get_peer.{label}=1"))
    # 4.4 row 4: the allowed-IPs nest failing with the fixed part fitting exactly
    out.append(boundary("n2_first_allowedips_nest", room_after_device - PEER_FIXED, {"ep": None, "ips": [4, 4]},
                        "get_peer.allowedips_nest_failed=1"))

    # 4.4 rows 1, 6-13: interleaving. Four peers of 32 IPv4 IPs: the fourth
    # splits in chunk 1 (3 x 1056 fit in 3648, the fourth does not)
    def four(addresses):
        peers = [{"ep": 4, "ips": [4] * 32} for _ in range(4)]
        chunks = emulate(peers)
        assert [p[1] for p in chunks[0]["peers"]] == ["complete"] * 3 + ["split"] and len(chunks) == 2, chunks
        return peers, wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": materialize(peers, addresses)})

    a = Addresses()
    peers, setup = four(a)
    out.append(("n2_split_peer", {"ops": [setup, start(), RECV, RECV, GET],
                                  "expect": ["get_peer.get_allowedips_failed=1", "get_peer.first_part=0",
                                             "get_peer.seq_unset=0", "wg_get_device_dump.has_cursor=1"]}))
    # the consistency flag: any wg_set between two dump calls (flags 18 on chunk 2)
    a = Addresses()
    peers, setup = four(a)
    out.append(("n2_dump_intr", {"ops": [setup, start(), wg_set({"fwmark": 7}), RECV, RECV, GET],
                                 "expect": ["get_peer.first_part=0", "get_peer.seq_changed=0"]}))
    # seq_changed: an allowed IP inserted on another peer between the calls:
    # the split peer continues as {public_key} only
    a = Addresses()
    peers, setup = four(a)
    out.append(("n2_seq_changed", {"ops": [setup, start(), wg_set({"peers": [{"public_key": pub(0x40), "allowed_ips": [a.ip(4)]}]}),
                                           RECV, RECV, GET],
                                   "expect": ["get_peer.seq_changed=1", "get_peer.first_part=0"]}))
    # stale cursor, next live peer (2.4 a): Q1-Q3 complete, P splits, then R
    # and S; P removed between the calls: R is {public_key} only, S completes
    a = Addresses()
    peers = [{"ep": 4, "ips": [4] * 32} for _ in range(4)] + [{"ep": 4, "ips": [4, 4]}, {"ep": 6, "ips": [6]}]
    chunks = emulate(peers)
    assert [p[1] for p in chunks[0]["peers"]] == ["complete"] * 3 + ["split"], chunks
    setup = wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": materialize(peers, a)})
    out.append(("n2_stale_cursor_next_live", {"ops": [setup, start(), wg_set({"peers": [{"public_key": pub(0x43), "remove": True}]}),
                                                      RECV, RECV, GET],
                                              "expect": ["get_peer.first_part=0", "get_peer.seq_changed=1",
                                                         "get_peer.first_part=1", "wg_get_device_dump.cursor_dead=0"]}))
    # stale cursor, empty list (2.4 b): the sole peer, 128 IPs over 4 sets,
    # splits; removed between the calls: the device part again, no peers
    a = Addresses()
    sets = accumulate(0x40, 128, 4, a)
    chunks = emulate([{"ep": 6, "ips": [4] * 128}])
    assert chunks[0]["peers"] == [(0, "split", 124)] and chunks[1]["device"], chunks
    out.append(("n2_stale_cursor_empty", {"ops": [*sets, start(), wg_set({"peers": [{"public_key": pub(0x40), "remove": True}]}),
                                                  RECV, RECV, GET],
                                          "expect": ["wg_get_device_dump.peer_list_empty=1", "wg_get_device_dump.first_part=1",
                                                     "wg_get_device_dump.cursor_set=0"]}))
    # the dead cursor: P1-P3 complete (cursor P3), Q splits; P3 removed between
    # the calls: chunk 2 is a data message without attributes, then the DONE
    a = Addresses()
    peers, setup = four(a)
    out.append(("n2_dead_cursor", {"ops": [setup, start(), wg_set({"peers": [{"public_key": pub(0x42), "remove": True}]}),
                                           RECV, RECV, GET],
                                   "expect": ["wg_get_device_dump.cursor_set=1", "wg_get_device_dump.cursor_dead=1",
                                              "wg_get_device_dump.peer_list_empty=0"]}))
    # the device part repeated (row 5): the first peer over 3648 bytes
    a = Addresses()
    sets = accumulate(0x40, 128, 4, a)
    chunks = emulate([{"ep": 6, "ips": [4] * 128}])
    assert len(chunks) == 2 and chunks[1]["device"] and chunks[1]["done"], chunks
    out.append(("n2_device_part_repeated", {"ops": [*sets, GET, *stepped(chunks)],
                                            "expect": ["wg_get_device_dump.first_part=1", "get_peer.first_part=0",
                                                       "wg_get_device_dump.has_cursor=0"]}))
    # 256 allowed IPs accumulated (4.7), IPv4 and IPv6: three chunks
    for family in (4, 6):
        a = Addresses()
        sets = accumulate(0x40, 256, family, a)
        chunks = emulate([{"ep": 6, "ips": [family] * 256}])
        out.append((f"n2_aips_256_v{family}", {"ops": [*sets, GET, *stepped(chunks)],
                                              "expect": ["get_peer.get_allowedips_failed=1", "get_peer.get_allowedips_failed=0",
                                                         "wg_get_device_dump.first_part=1"]}))
    # the DONE in its own skb (row 11): the last peer leaves under 20 bytes;
    # the receive of chunk 1 runs the dump call that appends the DONE to a
    # fresh skb and wg_get_device_done; that DONE's receive is not in the domain
    for room in (0, 8, 16):
        peers = fillers(room_after_device - room)
        chunks = emulate(peers)
        assert len(chunks) == 1 and not chunks[0]["done"] and chunks[0]["room"] == room, (room, chunks)
        a = Addresses()
        setup = wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": materialize(peers, a)})
        out.append((f"n2_done_separate_room{room}", {"ops": [setup, start(), RECV, GET],
                                                     "expect": ["wg_get_device_done.has_wg=1", "wg_get_device_dump.done=1"]}))
    # a start error (row 12): the acknowledgement is the receive's message;
    # the socket then dumps normally (one chunk, the DONE fitting)
    a = Addresses()
    setup = wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": materialize([{"ep": 4, "ips": [4]}], a)})
    out.append(("n2_start_error", {"ops": [setup, start({"ifname": "sit0"}), RECV, start(), RECV, GET],
                                   "expect": ["wg_get_device_start.lookup_error=1", "wg_get_device_start.lookup_error=0"]}))
    return out


def measure(traces_by_id):
    """`leanux-model --domain` on the traces (no hidden-input records: the
    reads return placeholders): each must be in the domain; its label count
    is measured against the check's cap (4.7)."""
    model = ROOT / ".lake" / "build" / "bin" / "leanux-model"
    payload = "".join(json.dumps(t, separators=(",", ":"), sort_keys=True) + "\n" for t in traces_by_id.values())
    result = subprocess.run([str(model), "--domain"], input=payload.encode(), capture_output=True, timeout=600)
    if result.returncode or result.stderr.strip():
        raise SystemExit(f"leanux-model failed ({result.returncode}): {result.stderr.decode(errors='replace')[-2000:]}")
    counts = {}
    for line in result.stdout.decode().splitlines():
        verdict = json.loads(line)
        if not verdict["in_domain"]:
            raise SystemExit(f"{verdict['id']} outside the domain at operation {verdict['index']}: {verdict['site']}: {verdict['what']}")
        counts[verdict["id"]] = verdict["branches"]
    return counts


def main():
    out = ROOT / "corpus" / "wireguard"
    written = {}
    for name, body in traces():
        trace = {"version": 1, "id": name, "ops": body["ops"], "expect": body["expect"]}
        validate_trace(trace)
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
        written[name] = trace
    print(f"wrote {len(written)} traces to {out}")
    if "--measure" in sys.argv:
        counts = measure(written)
        for name, count in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"{count:6d} labels  {name}")
        worst = max(counts.values())
        print(f"max {worst} of MAX_BRANCHES {MAX_BRANCHES}" + ("" if worst <= MAX_BRANCHES else "  OVER THE CAP"))


if __name__ == "__main__":
    main()
