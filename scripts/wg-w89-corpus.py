#!/usr/bin/env python3
"""Writes workstream W9's traces (docs/2026-10-06-w8-w9-netns-routing.md,
sections 4.3 and 7: `send4`'s arms, the dst cache, the fixture's tables and
the sender's wildcard bind) into corpus/wireguard.

Sessions reuse stage D1's steered handshakes (scripts/wg-d1-corpus.py) and
D3's retransmit advance (scripts/wg-d3-corpus.py). The output is
deterministic: rerunning this script reproduces the committed files.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

OBSERVE, GET, UP = d1.OBSERVE, d1.GET, {"op": "wg_up"}
RETRANSMIT = {"op": "wg_advance", "ticks": 1450}   # d3_retransmit: REKEY_TIMEOUT + the jitter's maximum
LISTENER = d1.LISTENER
ALIAS_SENDER = {"family": 4, "addr": "7f000002", "port": 51998}   # the wildcard sender at the loopback alias
OFF_LOOPBACK = {"family": 4, "addr": "c0000201", "port": 51999}  # 192.0.2.1: routes into wg0 while the default route exists
# the second initiation's draws are the retransmit's: unsteered
RETRANSMIT_STEER = [["init_ephemeral", "draw"], ["tai64n_now", "draw"], ["index_draw", "draw"]]


def deladdr(family):
    return {"op": "wg_deladdr", "family": family}


def delroute(family):
    return {"op": "wg_delroute", "family": family}


def xmit(dst="0a010203"):
    return {"op": "wg_xmit", "packet": {"family": 4, "dst": dst}}


def inject(message, to):
    op = d1.inject(message)
    op["to"] = to
    return op


def session_to(to):
    """wg0 initiates at wg_up; the response is injected from `to`; on the
    completed handshake wg0 sends a keepalive to the learned endpoint, whose
    source the sender's recvfrom reports (section 2.5)."""
    response = d1.respond(d1.wg0_initiation())
    return d1.setup() + [OBSERVE, inject(response.message, to), OBSERVE, GET]


def traces():
    out = {}
    # W9-M1: the endpoint is the wildcard sender at a loopback alias; Linux routes
    # 127.0.0.2 through the 127/8 local route and the sender receives the
    # initiation from 127.0.0.1 (section 2.5: today's rule dropped it)
    out["w9_endpoint_alias"] = (d1.setup(endpoint=ALIAS_SENDER) + [OBSERVE, GET], d1.steer_initiation(), [])
    # W9-M3: two sends through the cache: the initiation at wg_up (a miss after
    # the peer's dst_cache_init) and the retransmit (a hit iff the recorded
    # refresh jiffy is after the reset's)
    out["w9_two_sends"] = (d1.setup() + [OBSERVE, RETRANSMIT, OBSERVE, GET],
                           d1.steer_initiation() + RETRANSMIT_STEER,
                           ["fired:wg_expired_retransmit_handshake"])
    # W9-M9: the default route deleted before any lookup through it (the
    # initiation went over lo): no generation bump, so the retransmit may hit
    out["w9_delroute_untouched"] = (d1.setup() + [OBSERVE, delroute(4), RETRANSMIT, OBSERVE, GET],
                                    d1.steer_initiation() + RETRANSMIT_STEER,
                                    ["fired:wg_expired_retransmit_handshake"])
    # W9-M5: a route error (the default route gone, an endpoint off loopback):
    # send4 returns -ENETUNREACH, no datagram, tx_bytes unchanged. The peer
    # starts without an endpoint or keepalive (nothing is sent at wg_up, so no
    # REKEY_TIMEOUT rate limit); the running-device wg_set of both queues the
    # keepalive's initiation (netlink.c:470-479)
    quiet = d1.peer()
    del quiet["endpoint"]
    out["w9_unroutable"] = ([{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                                           "peers": [quiet]}},
                             UP, delroute(4),
                             {"op": "wg_set", "config": {"peers": [{"public_key": quiet["public_key"],
                                                                     "endpoint": OFF_LOOPBACK, "keepalive": 25}]}},
                             OBSERVE, GET], d1.steer_initiation(), [])
    # W9-M8: deleting wg0's only IPv4 address disables its routes as well: a
    # later wg_delroute 4 finds none (-ESRCH) and the inner sendto fails
    out["w9_deladdr_then_send"] = (d1.setup() + [OBSERVE, deladdr(4), delroute(4), xmit(), OBSERVE, GET],
                                   d1.steer_initiation(), [])
    # W9-M2: a response injected to the alias: wg0 learns src4 127.0.0.2, which
    # inet_confirm_addr rejects at the keepalive's send4 (the source cleared,
    # the keepalive leaves from 127.0.0.1)
    out["w9_inject_to_alias"] = (session_to("loopback-alias"), d1.steer_initiation(), d1.EXPECT_SESSION)
    # W9-M10: a response injected to wg0's own address: the sender's datagram
    # leaves from 10.255.254.1 (the local route's prefsrc), wg0 learns that
    # endpoint and resets the cache, and the wildcard sender receives the
    # keepalive from it
    out["w9_inject_to_wg0_addr"] = (session_to("wg0"), d1.steer_initiation(), d1.EXPECT_SESSION)
    # W9-M3 and W9-M9 need a cached dst that survives: the initiation's is
    # expired by the up's route adds (the fixture's order, section 14.3b), so
    # the first send after the session (the keepalive on the completed
    # handshake) misses and caches, and the next send hits: a data packet
    # (w9_session_two_sends), or a keepalive queued by a running-device
    # wg_set after a wg_delroute 4 that was never looked up (no generation
    # bump: w9_session_delroute_untouched)
    # The session's endpoint update resets the cache and its keepalive refreshes
    # in the same or the next jiffy (a tick in between is the 1-5% case of
    # section 2.4), so the first data send may miss once more; the second
    # always hits. For W9-M9 the inner packets are IPv6 (the peer's IPv6
    # allowed IP), so the IPv4 default route is never looked up before its
    # deletion while the outer sends still go through send4's cache.
    response = d1.respond(d1.wg0_initiation())
    out["w9_session_two_sends"] = (d1.setup() + [OBSERVE, d1.inject(response.message), OBSERVE,
                                                 xmit(), OBSERVE, xmit(), OBSERVE, GET],
                                   d1.steer_initiation(), d1.EXPECT_SESSION)
    allowed = [{"family": 4, "addr": "0a000000", "cidr": 8}, {"family": 6, "addr": "fd000000000000000000000000000000", "cidr": 8}]
    xmit6 = {"op": "wg_xmit", "packet": {"family": 6, "dst": "fd000000000000000000000000000001"}}
    out["w9_session_delroute_untouched"] = (
        d1.setup(allowed_ips=allowed) + [OBSERVE, d1.inject(response.message), OBSERVE, xmit6, OBSERVE,
                                         delroute(4), xmit6, OBSERVE, GET],
        d1.steer_initiation(), d1.EXPECT_SESSION)
    # the IPv6 side of the alias rule does not exist (no /8 on lo); the IPv6
    # delete-then-send: the address removal keeps the default route
    out["w9_deladdr6_then_send"] = (d1.setup() + [OBSERVE, deladdr(6), delroute(6), delroute(6), GET],
                                    d1.steer_initiation(), [])
    return {name: {"version": 1, "id": name, "ops": ops,
                   **({"steer": steer} if steer else {}), **({"expect": expect} if expect else {})}
            for name, (ops, steer, expect) in out.items()}


def main():
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
