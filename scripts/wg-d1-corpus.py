#!/usr/bin/env python3
"""Writes the stage D1 (wg0 initiates) traces into corpus/wireguard.

Each trace steers wg0's hidden inputs (docs/2026-10-03-steering-design.md,
section 6): the ephemeral key's random draw (before the C's clamp), the
wall-clock read in tai64n_now, and the index draw. From those, this script
computes the initiation wg0 will send (harness/noise.py) and the response
the peer, whose private key the trace knows, sends back from the fixture's
sender. The output is deterministic: rerunning this script reproduces the
committed files.

Schedules list every encounter of the sites they name, in encounter order:
create_initiation draws the ephemeral, then reads the clock, then draws the
index; create_response draws its ephemeral, then the index.
"""
import json
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

DEVICE = b"\x11" * 32          # wg0
OTHER_DEVICE = b"\x55" * 32    # wg0's key after a change
PEER = b"\x22" * 32            # the peer: its private key is the trace's
PORT = 51820
LISTENER = {"family": 4, "addr": "7f000001", "port": 51999}   # the fixture's listener
PSK = b"\xaa" * 32

# wg0's steered values. The ephemeral's first and last bytes change under
# the clamp, so a hook placed after the clamp would be seen.
EPHEMERAL = bytes(range(0x81, 0xa1))
EPHEMERAL_2 = bytes(range(0xc1, 0xe1))
CLOCK = (1_790_000_000, 987_654_321)       # rounds down to 973_078_528 ns
CLOCK_2 = (1_790_000_002, 16_777_215)      # rounds down to 0
INDEX = 0x0a0b0c0d
INDEX_RESPONDER_SIDE = 0x11223344          # wg0's index as a responder
RESP_EPHEMERAL = bytes(range(0x01, 0x21))  # wg0's response ephemeral (draw)

# The peer's values in its responses (not hidden inputs: they are in the message).
PEER_EPHEMERAL = b"\x44" * 32
PEER_EPHEMERAL_2 = b"\x45" * 32
PEER_INDEX = 0x01020304
PEER_INDEX_2 = 0x05060708

EXPECT_SESSION = ["wg_receive_handshake_packet.response=1", "wg_noise_handshake_begin_session.initiator=1",
                  "add_new_keypair.initiator=1", "wg_packet_send_staged_packets.no_keypair=0"]


def key(b):
    return b.hex()


def le32(n):
    return struct.pack("<I", n).hex()


def steer_initiation(ephemeral=EPHEMERAL, clock=CLOCK, index=INDEX):
    return [["init_ephemeral", ephemeral.hex()], ["tai64n_now", noise.timespec64(*clock).hex()],
            ["index_draw", le32(index)]]


def wg0_initiation(device=DEVICE, ephemeral=EPHEMERAL, clock=CLOCK, index=INDEX):
    return noise.steered_initiation(noise.public_key(PEER), device, ephemeral, *clock, index)


def respond(initiation, device=DEVICE, psk=None, ephemeral=PEER_EPHEMERAL, index=PEER_INDEX, **kw):
    return noise.response(initiation, PEER, ephemeral, psk, index, initiator_public=noise.public_key(device), **kw)


def peer(**extra):
    p = {"public_key": key(noise.public_key(PEER)), "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}],
         "endpoint": LISTENER}
    p.update(extra)
    return p


def setup(**extra):
    return [{"op": "wg_set", "config": {"private_key": key(DEVICE), "listen_port": PORT,
                                        "peers": [peer(keepalive=25, **extra)]}},
            {"op": "wg_up"}]


def inject(message, family=4):
    return {"op": "wg_inject", "family": family, "port": PORT, "message": message.hex()}


OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}


def initiate_trace(response, psk=None, after=()):
    """wg_up stages a keepalive and queues the initiation (device.c:54-58);
    wg_observe shows it at the listener; the response comes from the sender."""
    extra = {"preshared_key": key(psk)} if psk else {}
    return setup(**extra) + [OBSERVE, inject(response.message), OBSERVE, *after, GET]


def respond_then_initiate():
    """wg0 first answers an injected initiation (a pending next keypair), then
    initiates, and consumes the response: add_new_keypair's initiator arm
    demotes the next keypair (noise.c:211-222). A response sets
    last_sent_handshake, which rate-limits initiations for REKEY_TIMEOUT (5 s,
    beyond the trace's 4 s bound); changing wg0's private key expires the
    peer's keypairs and resets last_sent_handshake (noise.c:179-184), keeping
    the next keypair. Raising the keepalive from 0 then stages a keepalive,
    which finds no current keypair and queues the initiation (netlink.c:470-479).
    The endpoint is the sender's, learned from the injected initiation."""
    theirs = noise.initiation(noise.public_key(DEVICE), PEER, PEER_EPHEMERAL, noise.tai64n(1, 0), 0x0badcafe)
    ours = wg0_initiation(device=OTHER_DEVICE)
    response = respond(ours, device=OTHER_DEVICE)
    ops = [{"op": "wg_set", "config": {"private_key": key(DEVICE), "listen_port": PORT, "peers": [peer()]}},
           {"op": "wg_up"},
           inject(theirs), OBSERVE,
           {"op": "wg_set", "config": {"private_key": key(OTHER_DEVICE),
                                       "peers": [{"public_key": key(noise.public_key(PEER)), "keepalive": 25}]}},
           OBSERVE, inject(response.message), OBSERVE, GET]
    steer = [["resp_ephemeral", RESP_EPHEMERAL.hex()], ["index_draw", le32(INDEX_RESPONDER_SIDE)]] + steer_initiation()
    return ops, steer, ["wg_receive_handshake_packet.initiation=1"] + EXPECT_SESSION


def traces():
    init = wg0_initiation()
    basic = respond(init)
    second = respond(init, ephemeral=PEER_EPHEMERAL_2, index=PEER_INDEX_2)
    out = {
        # the initiation, the response, and the keepalive under the new session
        "d1_basic": (initiate_trace(basic), steer_initiation(), EXPECT_SESSION),
        "d1_preshared_key": (initiate_trace(respond(init, psk=PSK), psk=PSK), steer_initiation(), EXPECT_SESSION),
        # a flipped tag on encrypted_nothing: MAC1 is valid, message_decrypt fails
        "d1_tampered_nothing": (initiate_trace(respond(init, tamper="nothing")), steer_initiation(),
                                ["wg_receive_handshake_packet.response=1"]),
        # a receiver index in another bucket: the lookup walks an empty bucket
        "d1_wrong_receiver_index": (initiate_trace(respond(init, receiver_index=INDEX ^ 0x0101)), steer_initiation(),
                                    ["wg_receive_handshake_packet.response=1", "wg_index_hashtable_lookup.entry=0"]),
        # a receiver index in wg0's bucket: the walk finds an entry that does not match
        "d1_wrong_receiver_index_same_bucket": (
            initiate_trace(respond(init, receiver_index=INDEX ^ 0x80000000)), steer_initiation(),
            ["wg_receive_handshake_packet.response=1", "wg_index_hashtable_lookup.index_matches=0"]),
        # a second response after the session: the index now names the keypair,
        # so the handshake-typed lookup fails on the type mask
        "d1_second_response": (initiate_trace(basic, after=[inject(second.message), OBSERVE]), steer_initiation(),
                               EXPECT_SESSION + ["wg_index_hashtable_lookup.type_matches=0"]),
        "d1_respond_then_initiate": respond_then_initiate(),
    }
    return {name: {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": expect}
            for name, (ops, steer, expect) in out.items()}


def main():
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")


if __name__ == "__main__":
    main()
