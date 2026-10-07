#!/usr/bin/env python3
"""Writes workstream L's traces (wg0's lifecycle: create, down/up, the port
while running, delete; docs/2026-10-05-l-lifecycle.md, section 7) into
corpus/wireguard, and the random-port collision control into
corpus/lifecycle-controls.

Sessions reuse stage D1's steered handshakes (scripts/wg-d1-corpus.py) and
stage D2's data messages (harness/noise.py). A random port is steered
through `udp_port_draw` (udp_lib_get_port's get_random_u32, udp.c:257): the
draw `rand` with `32768 + ((rand * 28232) >> 32)` equal to the wanted port.
The output is deterministic: rerunning this script reproduces the committed
files. Every trace stays within evaluator/generate.py's WAIT_BUDGET_SECONDS
after its first wg_up (checked here).
"""
import importlib.util
import json
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402
from evaluator.generate import WAIT_BUDGET_SECONDS, wait_after_up  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)
# D3's helpers (the timer traces' sessions and advances) for the two traces
# that need the time advance
_spec3 = importlib.util.spec_from_file_location("wg_d3_corpus", ROOT / "scripts" / "wg-d3-corpus.py")
d3 = importlib.util.module_from_spec(_spec3)
_spec3.loader.exec_module(d3)

DEVICE, PEER, PORT, LISTENER = d1.DEVICE, d1.PEER, d1.PORT, d1.LISTENER
SENDER = {"family": 4, "addr": "7f000001", "port": 51998}   # the fixture's sender
OBSERVE, GET = d1.OBSERVE, d1.GET
UP, DOWN = {"op": "wg_up"}, {"op": "wg_down"}
CREATE, DELETE = {"op": "wg_create"}, {"op": "wg_delete"}
XMIT = {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a010203"}}
BARE = {"net_fixture": "bare"}

LOW, REMAINING = 32768, 60999 - 32768 + 1
INDEX_2 = 0x0c0d0e0f                       # wg0's index at its second initiation
PEER_INIT_INDEX = 0x0badcafe


def port_draw(port):
    """The u32 (little-endian hex) whose first candidate is `port`."""
    rand = -(-(port - LOW) * 2**32 // REMAINING)
    if LOW + (rand * REMAINING >> 32) != port or not 0 <= rand < 2**32:
        raise ValueError(f"no draw for port {port}")
    return struct.pack("<I", rand).hex()


def peer(endpoint=LISTENER, **extra):
    return d1.peer(endpoint=endpoint, **extra) if endpoint else \
        {k: v for k, v in d1.peer(**extra).items() if k != "endpoint"}


def configure(port=PORT, **peer_extra):
    config = {"private_key": d1.key(DEVICE), "peers": [peer(**peer_extra)]}
    if port is not None:
        config["listen_port"] = port
    return {"op": "wg_set", "config": config}


def set_device(**config):
    return {"op": "wg_set", "config": config}


def inject(message, port=PORT, family=4):
    return {"op": "wg_inject", "family": family, "port": port, "message": message.hex()}


def peer_initiation():
    """The peer initiates to wg0 (as stage D2's respond-then-data)."""
    return noise.initiation(noise.public_key(DEVICE), PEER, b"\x46" * 32, noise.tai64n(1, 0), PEER_INIT_INDEX)


RESPOND_STEER = [["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(d1.INDEX_RESPONDER_SIDE)]]
SESSION = d1.EXPECT_SESSION


def d2_initiator_steer():
    return d3.d2.initiator()[2]


def traces():
    init = d1.wg0_initiation()
    session_response = d1.respond(init)
    session = noise.initiator_session(session_response)
    second_steer = d1.steer_initiation(ephemeral=d1.EPHEMERAL_2, clock=d1.CLOCK_2, index=INDEX_2)
    out = {
        # A bare fixture: no wg0, so the dump fails with ENODEV; wg_create
        # makes it (ifindex 3, port 0, no keys; the ratelimiter's first
        # reference draws its key); then b1_basic's configuration, an up and
        # a transmission whose initiation reaches the listener.
        "l_create_get": (BARE, [GET, CREATE, GET, configure(), UP, XMIT, OBSERVE, GET], None, None),
        # A second RTM_NEWLINK with NLM_F_EXCL: EEXIST from the core, no
        # WireGuard code.
        "l_create_twice": (BARE, [CREATE, CREATE, GET], None, None),
        # wg_create, wg_delete, wg_create: the second device is ifindex 4
        # (the netns cursor is never reset), and its creation draws the
        # ratelimiter key again (the deletion dropped the last reference).
        "l_create_delete_create": (BARE, [CREATE, DELETE, CREATE, GET], None, None),
        # No port at wg_up: wg_socket_init(0) draws the port (udp.c:257);
        # the dump shows it, computed from the record.
        "l_random_port_natural": (BARE, [CREATE, configure(port=None), UP, GET], None, None),
        # The draw steered to port 40001; the peer's initiation to 40001
        # gets wg0's (steered) response from 40001 at the sender.
        "l_create_random_port_steered": (
            BARE, [CREATE, configure(port=None, endpoint=None), UP, inject(peer_initiation(), port=40001), OBSERVE, GET],
            [["udp_port_draw", port_draw(40001)]] + RESPOND_STEER, ["wg_receive_handshake_packet.initiation=1"]),
        # The fixture's ports: binding 51999 (the 127.0.0.1 listener) and
        # 51998 (the dual-stack sender) fails with EADDRINUSE and wg0 stays
        # down (no routes: ENETUNREACH); 51820 works.
        "l_up_fixture_port": (None, [configure(port=51999), UP, XMIT, set_device(listen_port=51998), UP,
                                     set_device(listen_port=PORT), UP, GET], None, None),
        # Two packets staged (the second's initiation rate-limited), then
        # wg_down: wg_stop purges them (tx_dropped 2), keeps the port, and
        # the routes go (ENETUNREACH).
        "l_down_purges_staged": (None, [configure(), UP, XMIT, XMIT, DOWN, OBSERVE, GET, XMIT], None, None),
        # Up and down are no-ops on a device already in that state.
        "l_up_down_noop": (None, [set_device(listen_port=PORT), UP, UP, DOWN, DOWN, UP, GET], None, None),
        # A persistent keepalive sends an initiation at each open: wg_stop
        # reset last_sent_handshake, so the second is not rate-limited.
        "l_down_up_keepalive": (None, [configure(keepalive=25), UP, OBSERVE, DOWN, UP, OBSERVE, GET], None, None),
        # A completed session (D1), then down and up: the keypairs are gone,
        # so the peer's data message under the old session misses the index
        # lookup and is dropped; the open's keepalive initiates afresh
        # (steered second initiation).
        "l_down_after_session": (
            None, [configure(keepalive=25), UP, OBSERVE, inject(session_response.message), DOWN, UP,
                   inject(session.to_wg0(0, b"")), OBSERVE, GET],
            d1.steer_initiation() + second_steer, SESSION + ["wg_packet_consume_data.no_keypair=1"]),
        # An initiation, then down and up without keepalive: the handshake
        # was cleared, so the response to that initiation misses the index
        # lookup.
        "l_down_up_stale_response": (
            None, [configure(), UP, XMIT, OBSERVE, DOWN, UP, inject(session_response.message), OBSERVE, GET],
            d1.steer_initiation(), ["wg_index_hashtable_lookup.found=0"]),
        # The port while running: wg_socket_init(51821) rebinds; the next
        # initiation reaches the sender from 51821.
        "l_set_port_running": (None, [configure(endpoint=SENDER), UP, set_device(listen_port=51821), GET, XMIT,
                                      OBSERVE], None, None),
        # The same port while running: set_port returns at once.
        "l_set_port_running_same": (None, [configure(), UP, set_device(listen_port=PORT), GET], None, None),
        # The sender's port while running: EADDRINUSE after the fwmark took
        # effect; the old sockets keep working (the initiation comes from
        # 51820).
        "l_set_port_running_inuse": (None, [configure(endpoint=SENDER), UP, set_device(fwmark=7, listen_port=51998),
                                            GET, XMIT, OBSERVE], None, None),
        # Port 0 while running, steered to 40002; the peer's initiation to
        # 40002 is answered from 40002.
        "l_set_port_running_random_steered": (
            None, [configure(endpoint=None), UP, set_device(listen_port=0), GET,
                   inject(peer_initiation(), port=40002), OBSERVE, GET],
            [["udp_port_draw", port_draw(40002)]] + RESPOND_STEER, ["wg_receive_handshake_packet.initiation=1"]),
        # The fwmark while running: no socket change.
        "l_fwmark_running": (None, [configure(), UP, set_device(fwmark=0x1234), GET, XMIT, OBSERVE], None, None),
        # Deleting a down device with a peer, then every operation on the
        # missing device: ENODEV, ENETUNREACH, stats null.
        "l_delete_down": (None, [configure(), DELETE, GET, UP, XMIT, OBSERVE, configure()], None, None),
        # Deleting an up device after a session: wg_stop first.
        "l_delete_up": (None, [configure(keepalive=25), UP, OBSERVE, inject(session_response.message), OBSERVE,
                               DELETE, GET, XMIT, OBSERVE], d1.steer_initiation(), SESSION),
        # Delete the fixture's wg0 and create another (ifindex 4), then a
        # session on it.
        "l_delete_create": (None, [DELETE, CREATE, GET, configure(keepalive=25), UP, OBSERVE,
                                   inject(session_response.message), OBSERVE, GET], d1.steer_initiation(), SESSION),
        # A bare fixture's RTM_DELLINK: ENODEV from the core.
        "l_delete_absent": (BARE, [DELETE, OBSERVE], None, None),
    }
    # With D3 (section 7) [AGENT, int-dl follow-up 2].
    retransmit_steer = d2_initiator_steer()
    zk_ops, _, zk_steer = d3.session()
    out.update({
        # An initiation (the staged packet queues it; its send arms the
        # retransmit timer), then wg_down: wg_stop purges the packet
        # (tx_dropped 1) and wg_timers_stop deletes the five timers, so an
        # advance past the retransmit's expiry runs no section, and the
        # observation finds nothing new.
        "l_down_stops_timers": (
            None, d3.d2.setup(keepalive=False) + [d3.xmit(), OBSERVE, DOWN, d3.advance(d3.RETRANSMIT), OBSERVE, GET],
            retransmit_steer, ["wg_packet_send_staged_packets.no_keypair=1", "wg_stop.peers_iterate=1"]),
        # D3's zero-key firing (as d3_zero_key: the persistent keepalive set
        # to 0 first, so it fires as a no-op in the same pass); the clear work
        # it queues runs in the advance's wait (the guest waits for it). Then
        # wg_delete of the up device: wg_stop over the cleared peer (its
        # wg_timers_stop finds no queued clear work: the work never stays
        # queued past an idle point in this harness), wg_destruct, and every
        # operation on the missing device.
        "l_delete_after_clear_work": (
            None, zk_ops + [d3.keepalive_off(), d3.advance(d3.ZERO_KEY), DELETE, GET, OBSERVE],
            zk_steer, SESSION + [d3.fired("zero_key_material"), d3.ZERO_KEY_ALIVE + "=1",
                                 "wg_stop.peers_iterate=1"]),
    })
    result = {}
    for name, (fixture, ops, steer, expect) in out.items():
        trace = {"version": 1, "id": name}
        if fixture:
            trace.update(fixture)
        trace["ops"] = ops
        if steer:
            trace["steer"] = steer
        if expect:
            trace["expect"] = expect
        if wait_after_up(ops) > WAIT_BUDGET_SECONDS:
            raise AssertionError(f"{name} exceeds the wait budget")
        result[name] = trace
    return result


def controls():
    """The random port's first candidate steered onto the fixture's
    listener port: Linux steps to another port, the mirror stops
    `unsupported` (the collision is outside its domain): a negative control
    that must fail that way."""
    return {"l_random_port_collision": {
        "version": 1, "id": "l_random_port_collision", "net_fixture": "bare",
        "ops": [CREATE, configure(port=None), UP, GET],
        "steer": [["udp_port_draw", port_draw(51999)]]}}


def main():
    for directory, written in (("wireguard", traces()), ("lifecycle-controls", controls())):
        out = ROOT / "corpus" / directory
        out.mkdir(exist_ok=True)
        for name, trace in written.items():
            (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
        print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
