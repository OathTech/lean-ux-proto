#!/usr/bin/env python3
"""Writes the stage E-B under-load traces (docs/2026-10-05-e-dos.md §6.B) into
corpus/wireguard/e_underload_*.json, and the merged-injection negative control
into corpus/underload-controls/.

Each trace creates wg0 in-window (L's wg_create, so the cookie secret is
captured as `.cookieSecret`), configures its private key (so the cookie
encryption key `blake2s("cookie--" || wg0_public)` is precomputed) and listen
port, and brings it up. A `wg_flood` of invalid-MAC1 initiations via io_uring
crosses the `handshake_queue_len >= 512` under_load threshold and sets the
kernel-global `last_under_load`; every flood packet is dropped at the MAC1 check
(reply-free). Within the one-second decay, N valid-MAC1 initiations are injected:
each is under load (via the decay), takes the VALID_MAC_BUT_NO_COOKIE arm and
makes wg0 send exactly one cookie reply, built from the captured secret and the
recorded nonce. `wg_observe` then sees N byte-exact cookie replies at the sender.

The merged-injection control bundles a valid initiation into the flood's
io_uring batch, so the kernel processes it in the flood's (discarded) receive-
worker section: the mirror's section-bracket discard then meets a modeled record
inside the flood section and fails closed (the two-distinct-sections assertion,
§4.1).

Deterministic: rerunning reproduces the files.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

DEVICE, PEER, PORT = d1.DEVICE, d1.PEER, d1.PORT
BARE = {"net_fixture": "bare"}
CREATE = {"op": "wg_create"}
UP = {"op": "wg_up"}
DOWN = {"op": "wg_down"}
OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}
# Just above the 512 threshold: io_uring runs the sends inline in the trace task
# (KCOV on), so a larger count overflows the task and remote KCOV areas. All
# `count` packets queue before the single-CPU receive worker runs (io_uring_enter
# does not sleep), so the queue reaches `count` and crosses 512.
FLOOD_COUNT = 520


def configure():
    # the private key precomputes mac1_key and cookie_encryption_key; no peer
    # is needed (the cookie-reply path never consumes the initiation)
    return {"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT, "peers": []}}


# arm C (ratelimiter): the cookie secret is steered, so the fixture computes
# make_cookie and a valid MAC2 to reach the ratelimiter; wg0's responses are
# steered (D1).
RL_SECRET = bytes(range(0x90, 0xb0))
RESP_EPHEMERAL_2 = bytes(range(0x21, 0x41))
RL_INDEX_1, RL_INDEX_2 = 0x11223344, 0x55667788
SENDER_SADDR = bytes([127, 0, 0, 1])
SENDER_SPORT = 51998


def configure_peer():
    return {"op": "wg_set", "config": {"private_key": d1.key(DEVICE), "listen_port": PORT,
            "peers": [{"public_key": d1.key(noise.public_key(d1.PEER)),
                       "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}]}}


def rl_initiation(ephemeral, sec, index):
    """A real Noise initiation (peer -> wg0) with a valid MAC1 and a valid MAC2
    (from make_cookie under the steered secret), so wg0 under load reaches the
    ratelimiter; an allow makes wg0 consume it and send a handshake response."""
    cookie = noise.make_cookie(RL_SECRET, SENDER_SADDR, SENDER_SPORT)
    init = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, ephemeral, noise.tai64n(sec, 0), index)
    return noise.with_mac2(init, cookie)


def valid_initiation(index, ephemeral):
    """A valid-MAC1 initiation to wg0 (MAC1 keyed by blake2s('mac1----' ||
    wg0_public)); its body is not consumed (the under-load path sends a cookie
    and returns before consume_initiation)."""
    return noise.initiation(noise.public_key(DEVICE), PEER, ephemeral, noise.tai64n(1, 0), index)


def flood(leading=(), control=None, **extra):
    op = {"op": "wg_flood", "count": FLOOD_COUNT, "port": PORT}
    if leading:
        op["messages"] = [m.hex() for m in leading]
    if control is not None:
        op["control"] = control.hex()
    op.update(extra)
    return op


def base_ops():
    return [CREATE, configure(), UP]


def traces():
    # corpus/wireguard (default suite). The queue-depth design (docs/2026-10-05-
    # e-dos.md §4.1 appendix): the valid-MAC1 initiation(s) are submitted FIRST in
    # the flood's io_uring batch, so the worker processes them while the whole
    # batch is still queued (handshake_queue_len >= 512 -> under_load via the
    # queue depth, deterministic on both guest children, no 1-second decay). The
    # mirror checks each leading packet's records and its byte-exact cookie reply,
    # then discards the invalid flood. No injection, so nothing depends on the
    # decay.
    v1, v2 = valid_initiation(0x1111_1111, b"\x51" * 32), valid_initiation(0x2222_2222, b"\x52" * 32)
    return {
        # the flood crosses under_load with no leading valid: no cookie reply,
        # the whole section discarded (robust under_load + discard check)
        "e_underload_flood": base_ops() + [flood(), OBSERVE, GET],
        # one leading valid under load -> exactly one byte-exact cookie reply
        "e_underload_cookie": base_ops() + [flood(leading=[v1]), OBSERVE, GET],
        # B1 (docs/2026-10-15-design-b1-handshake-ring.md, section 7): the
        # handshake ring's capacity. A fresh 4096-slot ring takes 4096 of the
        # 4097 sends; the worker's first packet reads the counter at 4096, and
        # the tail is 4095 packets (the mirror's per-packet contract predicts
        # it). The trace ends at the flood: the 4.5 s bound counts to the end
        # of the last operation, and the comparison child is at 0.67 s there.
        "e_ring_full": base_ops() + [flood(leading=[v1], count=4096)],
        # the batch rule and the carry across wg_stop: 537 packets consumed
        # leave slots 528 to 536 occupied (537 = 33 * 16 + 9; at a batch of 32
        # the last 25 would be carried), a wg_down/wg_up leaves the cursors as
        # they are (device.c:130 polls an empty ring once), and the second
        # flood takes 4087 of its 4088 sends (4071 at batch 32; 4088 at batch
        # 1). The first stage crosses the threshold (537, not 25): the
        # comparison child reruns the trace in the coverage child's boot, and
        # the kernel-global `last_under_load` (receive.c:100) the coverage
        # child's second flood left behind makes a below-threshold first
        # packet read the decay clock in that child only (receive.c:117), a
        # record the mirror cannot predict (the same leak chunk isolation
        # keeps between traces, here between the two children of one trace);
        # a first stage under load from the queue depth reads the clocks the
        # mirror predicts in both children.
        "e_ring_carry": base_ops() + [flood(leading=[v1], count=536), DOWN, UP, flood(leading=[v1], count=4087)],
        # two leading valids under load -> two byte-exact cookie replies
        "e_underload_two_replies": base_ops() + [flood(leading=[v1, v2]), OBSERVE, GET],
        # make_cookie's secret rotation (cookie.c:96-102, COOKIE_SECRET_MAX_AGE
        # 120 s): a `wg_advance` of 124 s (HZ=250: 31000 ticks) after the
        # checker's init puts the secret's birthdate past the age, so the
        # leading valid's MAC2 check (the first make_cookie under load) rotates
        # the secret (a coarse clock read and 32 random bytes, both recorded)
        # and the cookie reply is sealed under the new secret. Found by the
        # receive correspondence audit (docs/2026-10-13-audit-receive.md F7).
        "e_underload_cookie_rotated": base_ops() + [{"op": "wg_advance", "ticks": 31000},
                                                    flood(leading=[v1]), OBSERVE, GET],
        # The decay (receive.c:116-119; the simulation-target review's 3.4): the
        # flood's invalid tail leaves `last_under_load` at its last under-load
        # read. An initiation injected after the flood, inside the one-second
        # decay (the guest's 0.1 s post-flood wait), is under load by the decay:
        # a cookie reply, `last_under_load` kept.
        "e_underload_live": dict(
            ops=[CREATE, configure_peer(), UP, flood(), inject(v1), OBSERVE, GET],
            expect=["wg_receive_handshake_packet.was_under_load=1",
                    "wg_receive_handshake_packet.decay_expired=0"]),
        # ... and one injected after a `wg_advance` past the decay (HZ=250: 260
        # ticks is 1.04 s) is not: the decay has expired, `last_under_load` is
        # reset to 0 (receive.c:119), the initiation is consumed and answered
        # with a handshake response, and a second initiation after it never
        # enters the decay branch (the static is 0 again).
        "e_underload_decayed": dict(
            ops=[CREATE, configure_peer(), UP, flood(), {"op": "wg_advance", "ticks": 260},
                 inject(v1), inject(later_initiation(0x2222_2222, b"\x52" * 32)), OBSERVE, GET],
            expect=["wg_receive_handshake_packet.was_under_load=1",
                    "wg_receive_handshake_packet.decay_expired=1",
                    "wg_receive_handshake_packet.was_under_load=0",
                    "wg_noise_handshake_consume_initiation.flood=0"]),
    }


def inject(message):
    return {"op": "wg_inject", "family": 4, "port": PORT, "message": message.hex()}


def later_initiation(index, ephemeral):
    """A second consumable initiation from the peer: a later TAI64N timestamp,
    so consume_initiation's replay test passes (the guest's 0.4 s wait after an
    injection keeps it out of noise.c's flood test)."""
    return noise.initiation(noise.public_key(DEVICE), PEER, ephemeral, noise.tai64n(2, 0), index)


def controls():
    return {
        # a mid-flood valid initiation the mirror does not model (`control`,
        # submitted after the leading valid): the kernel makes a cookie reply for
        # it inside the flood section, so its modeled records (the nonce) land in
        # the region the mirror discards after the checked leading packet. The
        # discard meets a modeled record and fails closed (supersedes E19's
        # two-section assertion; docs/2026-10-05-e-dos.md §4.1 appendix).
        "e_underload_merged": base_ops()
        + [flood(leading=[valid_initiation(0x3333_3333, b"\x53" * 32)],
                 control=valid_initiation(0x4444_4444, b"\x54" * 32)), OBSERVE, GET],
    }


def ratelimit_traces():
    # arm C: a flood sets under_load; then two valid-MAC1+MAC2 Noise initiations
    # from one source IP reach the ratelimiter. The first inserts a bucket entry
    # (always allows) and is consumed -> a handshake response. The second, same
    # IP, hits the bucket (ratelimiter.c:121, the token arithmetic): with tokens
    # left it is allowed and consumed, but noise.c's own flood check (50/s,
    # last_initiation_consumption) drops a second consume in the same tick, so it
    # produces no response. So the ratelimiter's allow is checked by the record
    # stream (allow -> consume reads flood_now; deny -> dropped before consume),
    # and its token compare by the operands; only the first response is steered.
    two = flood(leading=[rl_initiation(d1.PEER_EPHEMERAL, 1, d1.PEER_INDEX),
                         rl_initiation(d1.PEER_EPHEMERAL_2, 2, d1.PEER_INDEX_2)])
    steer = RL_STEER
    expect = ["wg_receive_handshake_packet.initiation=1", "wg_ratelimiter_allow.entry_matches=1",
              "wg_ratelimiter_allow.inet=1"]
    return {"e_underload_ratelimit": dict(ops=[CREATE, configure_peer(), UP, two, OBSERVE, GET],
                                          steer=steer, expect=expect)}


# The ratelimiter traces' schedule, in encounter order: the cookie secret
# (wg_create), then the entry allocation at the first initiation's insert
# (ratelimiter.c:138, kind 305: a `draw` entry, which arms the trace's chunk
# for the site so the mirror consumes its record; B4, docs/2026-10-15-
# design-b4-load-ratelimiter.md 4.3), then the response's ephemeral and index.
RL_STEER = [["cookie_secret", RL_SECRET.hex()], ["kmemCacheAllocRlEntry", "draw"],
            ["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(RL_INDEX_1)]]


def write_suite(subdir, cases):
    out = ROOT / "corpus" / subdir
    out.mkdir(exist_ok=True)
    for name, case in cases.items():
        trace = {"version": 1, "id": name, "net_fixture": "bare"}
        trace.update(case if isinstance(case, dict) else {"ops": case})
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")


def write_steered(subdir, cases):
    out = ROOT / "corpus" / subdir
    out.mkdir(exist_ok=True)
    for name, c in cases.items():
        trace = {"version": 1, "id": name, "net_fixture": "bare", "ops": c["ops"],
                 "steer": c["steer"], "expect": c["expect"]}
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")


def boundary_traces():
    """The under_load threshold (receive.c:112-113, `>= MAX_QUEUED_INCOMING_HANDSHAKES
    / 8` = 512): the worker sees the batch's size on its first packet (the counter
    is decremented after the packet, receive.c:215), so one leading valid at a
    batch of 511 is not under load (consumed: a handshake response), at 512 and
    513 it is (a cookie reply). The compare's operands are checked
    (`.hsUnderLoad` declared with them, 2026-10-14; the receive audit's F9, the
    pre-release review's section 8)."""
    v1 = valid_initiation(0x1111_1111, b"\x51" * 32)
    return {
        "e_underload_511": dict(ops=[CREATE, configure_peer(), UP, flood(leading=[v1], count=510), OBSERVE, GET],
                                expect=["wg_receive_handshake_packet.under_load=0",
                                        "wg_receive_handshake_packet.initiation=1",
                                        "wg_noise_handshake_consume_initiation.flood=0"]),
        "e_underload_512": dict(ops=base_ops() + [flood(leading=[v1], count=511), OBSERVE, GET],
                                expect=["wg_receive_handshake_packet.under_load=1"]),
        "e_underload_513": dict(ops=base_ops() + [flood(leading=[v1], count=512), OBSERVE, GET],
                                expect=["wg_receive_handshake_packet.under_load=1"]),
    }


SENDER_SADDR6 = bytes(15) + b"\x01"   # ::1, the flood's source when family is 6


def rl_initiation6(ephemeral, sec, index):
    """`rl_initiation` over IPv6: make_cookie hashes the 16-byte source ::1."""
    cookie = noise.make_cookie(RL_SECRET, SENDER_SADDR6, SENDER_SPORT)
    init = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, ephemeral, noise.tai64n(sec, 0), index)
    return noise.with_mac2(init, cookie)


def ratelimit6_traces():
    """arm C over IPv6 (ratelimiter.c:101-106): the flood and the valid-MAC2
    initiations arrive from ::1, so the ratelimiter keys the source /64 in its
    IPv6 table (`.rlProtoIp6`). Two initiations: both allowed (the second hits
    the bucket), as the IPv4 trace. Six: the entry is inserted with four
    tokens left (TOKEN_MAX - PACKET_COST), the second to fifth are allowed and
    deducted (each then dropped by noise.c's own 50/s consumption check), and
    the sixth is denied: VALID_MAC_WITH_COOKIE_BUT_RATELIMITED, an invalid MAC
    under load, dropped (`.macRatelimited=1`, `.rlAllow=0`). The receive
    audit's F12; the pre-release review's limitations table."""
    steer = RL_STEER
    two = flood(leading=[rl_initiation6(d1.PEER_EPHEMERAL, 1, d1.PEER_INDEX),
                         rl_initiation6(d1.PEER_EPHEMERAL_2, 2, d1.PEER_INDEX_2)], family=6)
    six = flood(leading=[rl_initiation6(bytes([0x60 + i]) * 32, i + 1, 0x0600_0000 + i) for i in range(6)],
                family=6)
    return {
        "e_underload_ratelimit6": dict(ops=[CREATE, configure_peer(), UP, two, OBSERVE, GET], steer=steer,
                                       expect=["wg_receive_handshake_packet.initiation=1",
                                               "wg_ratelimiter_allow.inet6=1",
                                               "wg_ratelimiter_allow.entry_matches=1",
                                               "wg_cookie_validate_packet.ratelimited=0"]),
        "e_underload_ratelimit6_deny": dict(ops=[CREATE, configure_peer(), UP, six, OBSERVE, GET], steer=steer,
                                            expect=["wg_ratelimiter_allow.inet6=1",
                                                    "wg_ratelimiter_allow.allow=1",
                                                    "wg_ratelimiter_allow.allow=0",
                                                    "wg_cookie_validate_packet.ratelimited=1"]),
    }


# e_underload_busy (the producer's busy test at receive.c:554, a 2,100-send
# flood) was dropped at the landing of 2026-10-15 [USER: "(1) agreed"]: its
# comparison child sits at 4.40 s of the guest's 4.5 s bound under load, and
# on this configuration the trylock it reaches is a compile-time constant
# (include/linux/spinlock_up.h:56), declared constant in the mirror; the
# threshold compare it witnessed is the only thing lost.


def main():
    write_suite("wireguard", traces())
    write_suite("wireguard", boundary_traces())
    write_steered("wireguard", ratelimit_traces())
    write_steered("wireguard", ratelimit6_traces())
    write_suite("underload-controls", controls())
    print(f"wrote {len(traces()) + len(boundary_traces()) + len(busy_traces())} + {len(ratelimit_traces()) + len(ratelimit6_traces())} "
          f"wireguard and {len(controls())} control traces")


if __name__ == "__main__":
    main()
