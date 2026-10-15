#!/usr/bin/env python3
"""Writes the stage D3 (timers) traces into corpus/wireguard, and the timer
controls into corpus/timer-controls (docs/2026-10-05-d3-timers.md, sections
6-8). With --probe, runs them on Linux alone (no mirror) with the arm
records on, and summarizes what each trace's records show.

    scripts/in-bundle python3 scripts/wg-d3-corpus.py
    LEANUX_KERNEL_DIR=$PWD/.artifacts/kernel-net-choice-d3 \\
        scripts/in-bundle python3 scripts/wg-d3-corpus.py --probe OUT [--only ID,...]

Sessions are D1's (scripts/wg-d1-corpus.py): wg0 initiates with steered
values and the peer's response is computed offline. A `wg_advance` moves
`jiffies` (and, at the next tick, every clock) by its ticks; the timers due
then run in that operation's wait. Advance sizes come from
evaluator/generate.py (fire_advance, quiet_limit, expiry_advance): a target
timer's delay with its jitter maximum, the wheel's rounding for its level
and the wait, rounded up to 50 ticks; every other pending timer stays below
its quiet limit, so it fires neither in the operation nor naturally later.

Steering covers every encounter of the steered sites: wg0's first initiation
has values (the peer answers it); every later one (a retransmit, a new
handshake, a key that needs refreshing) has three `draw` entries, which the
mirror follows through the records (stream K's note, section 13.5).

Each trace's comment (TRACES below) states what Linux does; its `expect`
labels are decision outcomes and `fired:<callback>` for the timer sections
the mirror must run. The output is deterministic: rerunning this script
reproduces the committed files.
"""
import argparse
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from evaluator.generate import (D3_DRAWS, HZ, JITTER_MAX_TICKS, KEEPALIVE_TIMEOUT_TICKS, NEW_HANDSHAKE_TICKS,  # noqa: E402
                                REKEY_TIMEOUT_TICKS, WAIT_BUDGET_SECONDS, ZERO_KEY_TICKS, expiry_advance,
                                fire_advance, quiet_limit, wait_after_up)
from harness import noise  # noqa: E402
from harness.trace import validate_trace  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d2_corpus", ROOT / "scripts" / "wg-d2-corpus.py")
d2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d2)
d1 = d2.d1

OBSERVE, GET, inject = d1.OBSERVE, d1.GET, d1.inject
SESSION = d1.EXPECT_SESSION
DST4 = d2.DST4

RETRANSMIT = fire_advance(REKEY_TIMEOUT_TICKS + JITTER_MAX_TICKS)          # 1450
KEEPALIVE = fire_advance(KEEPALIVE_TIMEOUT_TICKS)                          # 2600
NEW_HANDSHAKE = fire_advance(NEW_HANDSHAKE_TICKS + JITTER_MAX_TICKS)       # 3950
PERSISTENT_5 = fire_advance(5 * HZ)                                        # 1350
ZERO_KEY = fire_advance(ZERO_KEY_TICKS)                                    # 139150
REJECT_AFTER = expiry_advance(180)                                         # 45250: REJECT_AFTER_TIME
REKEY_AFTER = expiry_advance(120)                                          # 30250: REKEY_AFTER_TIME
RX_FRESH = expiry_advance(180 - 10 - 5)                                    # 41500: receive.c:232-233
RATE_LIMIT = fire_advance(REKEY_TIMEOUT_TICKS)                             # 1350: past REKEY_TIMEOUT
# The persistent keepalive of 25 s that D1's sessions arm stays quiet below
# this total advance after its last arm.
PERSISTENT_25_QUIET = quiet_limit(25 * HZ)
# wg0's index in a steered second initiation.
SECOND_INDEX = 0x0e0f1011
# The callbacks' decisions (Leanux/Kernel/Decision.lean, stream M's region).
GIVE_UP = "wg_expired_retransmit_handshake.give_up"
NEED_ANOTHER = "wg_expired_send_keepalive.need_another"
INTERVAL = "wg_expired_send_persistent_keepalive.interval"
ZERO_KEY_ALIVE = "wg_expired_zero_key_material.alive"


# W12: the second and third keyless peers (private keys), at the listener.
PEER_B = b"\x33" * 32
PEER_C = b"\x44" * 32


def w12_peer(private, net):
    """A keyless peer at the fixture's listener with allowed IPs net/8 and a
    25 s persistent keepalive (wg_up initiates; the keepalive timer, 6250
    ticks in level 3, stays quiet below quiet_limit(6250) = 3975 ticks)."""
    return {"public_key": d1.key(noise.public_key(private)), "allowed_ips": [{"family": 4, "addr": net, "cidr": 8}],
            "endpoint": d1.LISTENER, "keepalive": 25}


def fired(name):
    return f"fired:wg_expired_{name}"


def advance(ticks):
    return {"op": "wg_advance", "ticks": ticks}


def xmit(n=1):
    return d2.xmit(4, DST4, d2.payload(16 + n, n))


def keepalive_off():
    """The persistent keepalive interval set to 0 on the existing peer: the
    timer it armed stays pending and fires later as a no-op
    (timers.c:140, `if (likely(peer->persistent_keepalive_interval))`)."""
    return {"op": "wg_set", "config": {"peers": [{"public_key": d1.key(noise.public_key(d1.PEER)), "keepalive": 0}]}}


def session(keepalive=25):
    """wg0 initiates at wg_up (the persistent keepalive stages a keepalive
    and queues the initiation, device.c:54-58), the response completes the
    session, and the staged keepalive goes out under it. Pending afterwards:
    the zero-key timer (540 s, from session_derived) and the persistent
    keepalive (`keepalive` s, re-armed at every authenticated packet)."""
    message, sess, steer = d2.initiator()
    ops = [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                        "peers": [d2.peer_config() | {"keepalive": keepalive}]}},
           {"op": "wg_up"}, OBSERVE, inject(message)]
    return ops, sess, steer


def staged_session():
    """Keepalive 0: a wg_xmit stages a packet and queues the initiation; the
    response flushes the packet (data sent: the new-handshake timer, 15 s
    plus jitter)."""
    message, sess, steer = d2.initiator()
    return d2.setup(keepalive=False) + [xmit(), OBSERVE, inject(message)], sess, steer


def data(sess, counter, text):
    return d2.to_wg0(sess, counter, d2.inner4(text))


def traces():
    message, sess, steer = d2.initiator()
    ka_ops, _, _ = session()
    out = {}

    # wg_up sends nothing (keepalive 0); the wg_xmit stages a packet and
    # queues the initiation, whose send arms the retransmit timer (1250 +
    # [0, 83) ticks). Nobody answers. The advance fires it:
    # wg_expired_retransmit_handshake (attempts 0 <= 18) increments the
    # attempts to 1, clears the endpoint source and queues a retry
    # (is_retry keeps the count; REKEY_TIMEOUT has passed, so the rate limit
    # lets it through): a second initiation at the listener, re-arming the
    # timer.
    out["d3_retransmit"] = (
        d2.setup(keepalive=False) + [xmit(), OBSERVE, advance(RETRANSMIT), OBSERVE, GET],
        steer + D3_DRAWS,
        [fired("retransmit_handshake"), "wg_packet_send_staged_packets.no_keypair=1",
         "wg_packet_send_queued_handshake_initiation.not_retry=0", GIVE_UP + "=0"])

    # As d3_retransmit, then 20 advances in all: firings 1-19 retry
    # (attempts 1..19, 20 initiations in all); firing 20 finds attempts 19 >
    # MAX_TIMER_HANDSHAKES (18) and gives up: the keepalive timer deleted, the
    # staged packet purged (tx_dropped 1), and the zero-key timer armed (it was
    # not pending: no session). No initiation after the give-up. The dump
    # shows the 20 initiations in the peer's tx_bytes. No wg_observe: on the
    # TCG guest the 20 advances take about 3.5 s of real time, and an
    # observation's 0.4 s wait exceeded the 4 s bound (probe h1).
    out["d3_retransmit_gives_up"] = (
        d2.setup(keepalive=False) + [xmit()] + [advance(RETRANSMIT)] * 20 + [GET],
        steer + D3_DRAWS * 19,
        [fired("retransmit_handshake"), "wg_packet_send_staged_packets.no_keypair=1", GIVE_UP + "=0",
         GIVE_UP + "=1", "wg_expired_retransmit_handshake.zero_key_not_pending=1"])

    # A session, then one data message from the peer: data_received arms the
    # send-keepalive timer (2500 ticks). The advance fires it:
    # wg_packet_send_keepalive stages a zero-length packet, the encrypt and
    # tx workers send a 32-byte keepalive (counter 1), and
    # need_another_keepalive is false, so no re-arm.
    out["d3_keepalive"] = (
        ka_ops + [data(sess, 0, "one"), advance(KEEPALIVE), OBSERVE, GET],
        steer,
        SESSION + [fired("send_keepalive"), "wg_timers_data_received.not_pending=1", NEED_ANOTHER + "=0"])

    # The control of audit M2: two data messages without a transmission
    # between them (the second finds the timer pending and sets
    # need_another_keepalive). The first advance fires the keepalive timer:
    # one keepalive, and the callback re-arms the timer at +10 s (an arm
    # record inside the timer section), but the tx worker's
    # any_authenticated_packet_sent deletes the re-arm, so the second advance
    # fires nothing: ONE keepalive, not two.
    out["d3_keepalive_rearm_deleted"] = (
        ka_ops + [data(sess, 0, "one"), data(sess, 1, "two"), advance(KEEPALIVE), advance(KEEPALIVE), OBSERVE, GET],
        steer,
        SESSION + [fired("send_keepalive"), "wg_timers_data_received.not_pending=1",
                   "wg_timers_data_received.not_pending=0", NEED_ANOTHER + "=1"])

    # B3 (docs/2026-10-15-design-b3-timer-wheel.md, section 9): the keepalive
    # callback's re-arm inside a catch-up pass. As d3_keepalive_rearm_deleted,
    # but one advance of 4200 ticks: the pass at the absorbing tick runs the
    # keepalive's bucket (due about 1700 ticks before the tick), the callback
    # re-arms at jiffies + 2500 with the base clock forwarded only to the
    # next due bucket of any owner (timer.c:1008-1014), so the re-arm's
    # delta is about 4200 and it lands on level 3 (slot 192+, width 512)
    # instead of level 2. The tx worker's any_authenticated_packet_sent then
    # deletes it, so only the kind-313 and kind-314 records show the level:
    # the mutant B3-M7 (the base clock taken as mod_timer's read) computes
    # level 2 and the kind-314 slot rejects it. The 25 s persistent keepalive
    # (6250 ticks from the response's receive) is not due: 4200 plus the
    # trace's real time (under 500 ticks) stays below it.
    assert 4200 + 500 < 25 * HZ
    out["d3_keepalive_rearm_catchup"] = (
        ka_ops + [data(sess, 0, "one"), data(sess, 1, "two"), advance(4200), OBSERVE, GET],
        steer,
        SESSION + [fired("send_keepalive"), "wg_timers_data_received.not_pending=1",
                   "wg_timers_data_received.not_pending=0", NEED_ANOTHER + "=1"])

    # B3 (section 9): two passes in one wait, with work between them. A 1 s
    # persistent keepalive (250 ticks, level 1, width 8) re-armed by the
    # batch's transmission fires naturally about 250 ticks into the batch's
    # wait; its keepalive's transmission re-arms it and it fires again about
    # 250 ticks later, each firing a pass of its own with the encrypt and tx
    # workers and the loopback NET_RX between (the T W N T W N stream of E1).
    # The batch waits 2400 ms (600 ticks), past the second firing (at most
    # 258 + 258 ticks after the transmission). The new-handshake timer the
    # transmission arms (3750 ticks) and the zero-key timer are not due; no
    # data is received, so no send-keepalive timer. The batch's wait is not
    # in wait_after_up's table; the trace's real time since wg_up is about
    # 3.3 s, under the guest's 4.5 s bound.
    ops1, _, _ = session(1)
    out["d3_two_passes"] = (
        ops1 + [{"op": "wg_batch", "items": [{"kind": "xmit", "packet": {"family": 4, "dst": DST4.hex(),
                                                                          "payload": d2.payload(17, 1).hex()}}],
                 "wait_ms": 2400}, GET],
        steer,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=1",
                   "wg_timers_any_authenticated_packet_traversal.keepalive=1"])

    # A session, then a data packet sent: data_sent arms the new-handshake
    # timer (3750 + [0, 83) ticks). The advance fires it:
    # wg_expired_new_handshake clears the endpoint source and queues an
    # initiation with is_retry false (attempts 0); the send worker sends a
    # fresh initiation (rate limit passed). The persistent keepalive (25 s,
    # re-armed by the transmission) stays quiet. A second transmission
    # after the firing (the session's keypair is still current) finds the
    # timer no longer pending (expire_timers detached it) and re-arms it,
    # with a jitter draw and an arm record (D3-M3).
    assert NEW_HANDSHAKE <= PERSISTENT_25_QUIET
    out["d3_new_handshake"] = (
        ka_ops + [xmit(), advance(NEW_HANDSHAKE), xmit(3), OBSERVE, GET],
        steer + D3_DRAWS,
        SESSION + [fired("new_handshake"), "wg_timers_data_sent.not_pending=1",
                   "wg_packet_send_queued_handshake_initiation.not_retry=1"])

    # Persistent keepalive 5 s: the session's packets re-arm the timer
    # (1250 ticks); the advance fires wg_expired_send_persistent_keepalive,
    # which sends a keepalive (the interval is nonzero); its transmission
    # re-arms the timer 5 s on, beyond the trace.
    ops5, _, _ = session(5)
    out["d3_persistent_keepalive"] = (
        ops5 + [OBSERVE, advance(PERSISTENT_5), OBSERVE, GET],
        steer,
        SESSION + [fired("send_persistent_keepalive"), "wg_timers_any_authenticated_packet_traversal.keepalive=1",
                   INTERVAL + "=1"])

    # The natural-firing control: persistent keepalive 2 s and no advance.
    # The response, injected right after wg_up (whose wait sent the
    # initiation), re-arms the timer at +500 ticks, about 2.1 s after wg_up;
    # it fires in real time inside one of the five observations' waits
    # (wg_observe's wait is an idle point, harness/guest.c), and that
    # observation sees the keepalive. Which wait is timing-dependent: the
    # labels are trace-wide, and the mirror follows the records. Its timer
    # section and the work after it show the same records, kinds and
    # decisions as d3_persistent_keepalive's virtual firing.
    ops2, _, _ = session(2)
    out["d3_persistent_natural"] = (
        [op for op in ops2 if op is not OBSERVE] + [OBSERVE] * 5 + [GET],
        steer,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=1"])

    # The zero-key timer (540 s from session_derived). The interval is set to
    # 0 first, so the persistent keepalive timer (25 s) fires earlier in the
    # same pass and sends nothing. wg_expired_zero_key_material queues the
    # clear work (wg_queued_expired_zero_key_material on handshake_send_wq):
    # the handshake and the keypairs are cleared, the keypair's index entry
    # removed. Then a data message under the old keys finds no keypair
    # (dropped), and a wg_xmit finds no keypair and initiates (the rate limit
    # passed long ago).
    out["d3_zero_key"] = (
        ka_ops + [keepalive_off(), advance(ZERO_KEY), data(sess, 0, "after zero"), xmit(2), OBSERVE, GET],
        steer + D3_DRAWS,
        SESSION + [fired("zero_key_material"), fired("send_persistent_keepalive"),
                   "wg_packet_consume_data.no_keypair=1", INTERVAL + "=0", ZERO_KEY_ALIVE + "=1",
                   "wg_expired_zero_key_material.already_queued=0"])

    # The session from a staged packet (keepalive 0): the flushed packet arms
    # the new-handshake timer (15 s). The 540 s advance runs both timers in
    # one pass in bucket order: the new handshake (which queues the send
    # worker), then the zero key (which queues the clear work); the work
    # runs FIFO on handshake_send_wq: the send worker sends an initiation
    # (steered, so the peer's response can be computed), then the clear
    # worker clears the handshake it created (its index entry removed) and
    # the keypairs. The peer's response to that initiation then finds no
    # handshake under its receiver index and is dropped (D3-M4).
    staged_ops, _, _ = staged_session()
    second = d1.wg0_initiation(ephemeral=d1.EPHEMERAL_2, clock=d1.CLOCK_2, index=SECOND_INDEX)
    late = d1.respond(second, ephemeral=d1.PEER_EPHEMERAL_2, index=d1.PEER_INDEX_2)
    out["d3_zero_key_after_new_handshake"] = (
        staged_ops + [advance(ZERO_KEY), inject(late.message), OBSERVE, GET],
        steer + d1.steer_initiation(d1.EPHEMERAL_2, d1.CLOCK_2, SECOND_INDEX),
        SESSION + [fired("new_handshake"), fired("zero_key_material"),
                   "wg_packet_send_staged_packets.no_keypair=1", ZERO_KEY_ALIVE + "=1",
                   "wg_index_hashtable_lookup.entry=0"])

    # Key expiry (section 6). Each starts from the session with the interval
    # then set to 0: the pending persistent keepalive fires in the advance
    # as a no-op; the zero-key timer (540 s) stays quiet.
    #
    # Send after REJECT_AFTER_TIME (181 s): send_staged_packets finds the
    # current keypair's sending birthdate expired (send.c:365) -> out_invalid:
    # sending.is_valid = false, the packet back on the staged queue, and an
    # initiation (no data message).
    out["d3_send_expired_key"] = (
        ka_ops + [keepalive_off(), advance(REJECT_AFTER), xmit(), OBSERVE, GET],
        steer + D3_DRAWS,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=0", "wg_packet_send_staged_packets.birthdate_expired=1"])
    # Send-side keep_key_fresh at REKEY_AFTER_TIME (121 s): the packet is
    # sent (counter 1), then keep_key_fresh (send.c:124-139; wg0 is the
    # initiator) queues an initiation: a data message, then an initiation.
    out["d3_send_keep_key_fresh"] = (
        ka_ops + [keepalive_off(), advance(REKEY_AFTER), xmit(), OBSERVE, GET],
        steer + D3_DRAWS,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=0", "keep_key_fresh.birthdate_expired=1",
                   "keep_key_fresh.send=1"])
    # Receive-side keep_key_fresh at 165 s (166 s): the first data message is
    # delivered and keep_key_fresh (receive.c:220-240) sets
    # sent_lastminute_handshake and queues an initiation; the second returns
    # before its clock read (one fewer kind-208 record).
    out["d3_rx_keep_key_fresh"] = (
        ka_ops + [keepalive_off(), advance(RX_FRESH), data(sess, 0, "fresh one"), data(sess, 1, "fresh two"),
                  OBSERVE, GET],
        steer + D3_DRAWS,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=0", "keep_key_fresh.rx_birthdate_expired=1",
                   "keep_key_fresh.rx_send=1", "keep_key_fresh.sent_lastminute=1"])
    # Receive after REJECT_AFTER_TIME (181 s): decrypt_packet (receive.c:253)
    # finds the receiving birthdate expired: receiving.is_valid = false, the
    # packet DEAD; nothing delivered, no initiation.
    out["d3_rx_expired_key"] = (
        ka_ops + [keepalive_off(), advance(REJECT_AFTER), data(sess, 0, "too late"), OBSERVE, GET],
        steer,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=0", "decrypt_packet.key_expired=1"])

    # The 5 s rate limit without the key trick (replaces
    # d1_respond_then_initiate's private-key change): the peer initiates and
    # wg0 responds (last_sent_handshake set; a pending next keypair). A
    # wg_xmit right away would be rate-limited; after an advance past
    # REKEY_TIMEOUT it stages, finds no current keypair and initiates. The
    # response completes wg0's session as initiator; add_new_keypair's
    # initiator arm demotes the pending next keypair.
    # The between zone [AGENT]: an advance of exactly the zero-key delay
    # plus the wait puts the timer's expiry inside the advance's window
    # (e < J_hi), but its level-4 bucket (up to 4096 ticks later) is most
    # likely still ahead, so Linux does not run it in this operation (probe
    # h-between); it may fire in the observation's wait, or after the trace.
    # The mirror does not predict firings from expiries (section 5.3: no
    # must-fire rule, audit M4); it follows the sections wherever they land
    # at an idle point. A mirror that fired every timer with e < J_hi would
    # fail here.
    out["d3_between_zone"] = (
        ka_ops + [keepalive_off(), advance(ZERO_KEY_TICKS + 25), OBSERVE, GET],
        steer,
        SESSION + [fired("send_persistent_keepalive"), INTERVAL + "=0"])

    # W12 (docs/2026-10-06-w3-w12.md, Part II): several peers' timers of
    # one kind due in one pass. Two keyless peers A and B with persistent
    # keepalives: wg_up queues both initiations; their send workers run in
    # the up's wait (the dispatch records say which first; the draws steer
    # whichever runs first), each arming its retransmit timer with the
    # jitter steered to 0 (byte 0x01), so the two expiries are equal, or
    # differ by one tick, and share a level-2 bucket (granularity 64) unless
    # a tick between the arms straddles a 64-tick boundary. The advance
    # fires both in one pass; the wheel runs a bucket LIFO (B then A); the
    # section records name each timer (dispatch order, kind 303's third
    # word), and each retry re-initiates (steered) and re-arms. Four
    # initiations at the listener, byte-exact. The schedule is consumed in
    # encounter order across sites (the kernel matches each steered site's
    # encounter against the schedule's head), so each initiation's jitter
    # entry follows its three draws.
    jitter0 = ["retransmit_jitter", "01"]
    w12_steers = [d1.steer_initiation(), d1.steer_initiation(ephemeral=d1.EPHEMERAL_2, clock=d1.CLOCK_2, index=SECOND_INDEX),
                  d1.steer_initiation(ephemeral=bytes(range(0x41, 0x61)), clock=(1_790_000_004, 0), index=0x12131415),
                  d1.steer_initiation(ephemeral=bytes(range(0x61, 0x81)), clock=(1_790_000_006, 0), index=0x16171819),
                  d1.steer_initiation(ephemeral=bytes(range(0x21, 0x41)), clock=(1_790_000_008, 0), index=0x1a1b1c1d),
                  d1.steer_initiation(ephemeral=bytes(range(0x01, 0x21)), clock=(1_790_000_010, 0), index=0x1e1f2021)]
    out["w12_retransmit_lifo"] = (
        [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                     "peers": [w12_peer(d1.PEER, "0a000000"), w12_peer(PEER_B, "0b000000")]}},
         {"op": "wg_up"}, OBSERVE, advance(RETRANSMIT), OBSERVE, GET],
        sum((st + [jitter0] for st in w12_steers[:4]), []),   # encounter order: the jitter ends each initiation
        [fired("retransmit_handshake"), "wg_packet_send_queued_handshake_initiation.not_retry=0", GIVE_UP + "=0"])
    # Three peers: a longer LIFO list in one bucket (stretch).
    out["w12_three_retransmit"] = (
        [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                     "peers": [w12_peer(d1.PEER, "0a000000"), w12_peer(PEER_B, "0b000000"),
                                               w12_peer(PEER_C, "0c000000")]}},
         {"op": "wg_up"}, OBSERVE, advance(RETRANSMIT), OBSERVE, GET],
        sum((st + [jitter0] for st in w12_steers[:6]), []),
        [fired("retransmit_handshake"), "wg_packet_send_queued_handshake_initiation.not_retry=0", GIVE_UP + "=0"])

    theirs = noise.initiation(noise.public_key(d1.DEVICE), d1.PEER, d1.PEER_EPHEMERAL, noise.tai64n(1, 0), 0x0badcafe)
    out["d3_respond_then_initiate"] = (
        [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                     "peers": [d2.peer_config(keepalive=False)]}},
         {"op": "wg_up"}, inject(theirs), advance(RATE_LIMIT), xmit(), OBSERVE, inject(message), OBSERVE, GET],
        [["resp_ephemeral", d1.RESP_EPHEMERAL.hex()], ["index_draw", d1.le32(d1.INDEX_RESPONDER_SIDE)]] + steer,
        ["wg_receive_handshake_packet.initiation=1", "wg_packet_send_staged_packets.no_keypair=1"] + SESSION)
    # A session, then wg0's private key is changed (set_device, netlink.c:575;
    # wg_set with a new private_key runs wg_noise_expire_current_peer_keypairs
    # over each existing peer). The peer holds a current keypair from the
    # session, so .current_keypair fires (noise.c:193) and the keypair's
    # sending half is invalidated; the handshake index entry is cleared. GET
    # shows wg0's new public key. No new draw: the per-peer static-static DH
    # and the cookie device-key recompute are crypto cut points.
    out["d3_privkey_change_expires"] = (
        ka_ops + [{"op": "wg_set", "config": {"private_key": d1.key(d1.OTHER_DEVICE)}}, OBSERVE, GET],
        steer,
        ["wg_noise_expire_current_peer_keypairs.current_keypair=1"])

    return out


def controls():
    """Traces that must fail (corpus/timer-controls; scripts/wg-d3-controls.py
    runs each with its guest variant)."""
    message, sess, steer = d2.initiator()
    ka_ops, _, _ = session()
    return {
        # The wait-0 control (section 8), run with the guest variant
        # advance-wait-0: the advance returns without waiting for its
        # absorbing tick, so the keepalive timer's section and the encrypt
        # and tx workers land in the next operation, a wg_get, which is not
        # an idle point: the mirror meets a section it does not expect there.
        # (If they stop after the wg_get, the trace has ended: the sections
        # were opened but not recorded, which fails as well.)
        "tc_advance_wait0": (ka_ops + [data(sess, 0, "one"), advance(KEEPALIVE), GET],
                             steer, [fired("send_keepalive")]),
    }


# Over the wait budget by construction, and kept [AGENT, int-dl follow-up 1]:
# the give-up needs 20 firings of the retransmit timer (attempts 0-19 against
# MAX_TIMER_HANDSHAKES 18), one per advance (each retry re-arms it 5 s past the
# advanced jiffies), and each advance needs its wait for the retry's send
# worker. Measured 3.1-3.9 s after wg_up against the 4.5 s bound
# (evaluator/generate.py ADVANCE_COST_SECONDS); the generator no longer draws
# this chain.
OVER_BUDGET = {"d3_retransmit_gives_up": 4.2}


def finish(out):
    result = {}
    for name, (ops, steer, expect) in out.items():
        cost = wait_after_up(ops)
        if name in OVER_BUDGET:
            if round(cost, 6) != OVER_BUDGET[name]:
                raise AssertionError(f"{name}: modeled wait {cost} s, recorded {OVER_BUDGET[name]} s")
        elif cost > WAIT_BUDGET_SECONDS:
            raise AssertionError(f"{name} exceeds the guest's wait budget")
        if len(expect) > 16:
            raise AssertionError(f"{name}: at most 16 expected outcomes")
        trace = {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": list(dict.fromkeys(expect))}
        result[name] = validate_trace(trace)
    return result


# --- Linux-only probes ------------------------------------------------------

def summarize(out, selected, sites):
    """Per trace and operation: the advance and arm records, the sections
    by symbol, the datagrams and stats each wg_observe saw; plus the
    Linux-side checks of evaluator/check.py, which need no mirror: every
    record from a declared consumer, the steering schedule consumed exactly
    and matching the records, every opened section recorded, and the
    jiffies progress."""
    from evaluator.check import (hidden_records, jiffies_problems, resolve_choices, section_problems,
                                 steering_problems)
    from evaluator.coverage import symbolize
    from harness.linux import DISPATCH_SYMBOLS, KERNEL, dispatch_addresses
    lines = lambda path: [json.loads(l) for l in (out / path).read_text().splitlines()]   # noqa: E731
    per = hidden_records(selected, lines("linux/hidden.jsonl"))
    ips = sorted({r[1] for ops in per.values() for op in ops for r in op})
    frames = symbolize([{"pcs": ips}], KERNEL / "vmlinux")["locations"] if ips else {}
    symbol = dict(zip(dispatch_addresses(KERNEL), DISPATCH_SYMBOLS))
    _, site_problems, _, meta = resolve_choices(per, sites, frames, symbol)
    steer_problems = steering_problems(selected, meta, lines("linux/steering.jsonl"))
    observed = {}
    for line in (out / "linux/boot.log").read_text().splitlines():
        if line.startswith("LEANUX_WGOBS "):
            record = json.loads(line[len("LEANUX_WGOBS "):])
            observed[(record["id"], record["index"])] = record
    observations = {r["id"]: r for r in lines("linux/observations.jsonl")}
    steering = {(r["id"], r["mode"]): r for r in lines("linux/steering.jsonl")}
    jiffies = jiffies_problems(selected, per)
    sections = section_problems(per, lines("linux/sections.jsonl"))
    report = {}
    for trace in selected:
        tid = trace["id"]
        ops, starts = [], []
        for i, (op, records) in enumerate(zip(trace["ops"], per[(tid, "pc")])):
            desc = []
            for kind, ip, _seq, _len, data, func in records:
                words = [int.from_bytes(bytes.fromhex(data[k:k + 16]), "little") for k in range(0, len(data), 16)]
                if kind == 300:
                    desc.append(f"start:{symbol.get(func, hex(func))}")
                    starts.append((i, symbol.get(func, hex(func))))
                elif kind == 301:
                    desc.append(f"stop:{symbol.get(func, hex(func))}")
                elif kind == 303:
                    desc.append(f"arm(d={words[1] - words[0]},{frames[ip][-1]['function']})")
                elif kind == 304:
                    desc.append(f"advance({words[1] - words[0]})")
                else:
                    desc.append(str(kind & 0x7fff))
            row = f"[{i}] {op['op']} ret={observations[tid]['observations'][i]['ret']}"
            if op["op"] == "wg_observe":
                record = observed[(tid, i)]
                row += (f" listener={[(d[1], d[2]) for d in record['datagrams']]}"
                        f" sender={[(r[3], r[4]) for r in record['replies']]} stats={record['stats']}")
            ops.append(row + ": " + " ".join(desc))
        fired = {f"fired:{s}" for _, s in starts if s.startswith("wg_expired_")}
        report[tid] = dict(
            ops=ops,
            fired_in_op=[[i, s] for i, s in starts if s.startswith("wg_expired_") or s.startswith("wg_queued_")],
            fired_labels_missing=[e for e in trace.get("expect", []) if e.startswith("fired:") and e not in fired],
            steering={m: {k: steering.get((tid, m), {}).get(k) for k in ("remaining", "mismatches")}
                      for m in ("pc", "cmp")},
            jiffies_problems=jiffies.get(tid, []), section_problems=sections.get(tid, []),
            site_problems=site_problems.get(tid, []) + steer_problems.get(tid, []))
    return report, per, meta


def firing_signature(labels, roles, start_symbol):
    """What a virtual and a natural firing of `start_symbol` must share, from
    its section onward in one operation (resolved records, as the mirror
    consumes them): the sections opened (a multiset: whether the tx worker
    runs nested in the encrypt worker's reschedule is timing), and the
    mirrored choice sites in order, without the reschedules and the ambient
    and cut records (scheduling and noise)."""
    sections, sites, on = [], [], False
    for label, _steered, _data in labels:
        if label == f"section_start:{start_symbol}":
            on = True
        if not on:
            continue
        if label.startswith("section_start:"):
            sections.append(label)
        elif not label.startswith(("section_stop:", "resched:")) and roles.get(label) == "mirror":
            sites.append(label)
    return sorted(sections), sites


def probe(args):
    from evaluator.check import load_hidden_sites
    from harness.linux import KERNEL, run_linux
    from harness.steer import call_sites, resolve as resolve_steering
    selected = list(finish(traces()).values())
    if args.generated:
        import random
        from evaluator.generate import steered_timers
        rng = random.Random(f"timers-probe-{args.generated_seed}")
        selected = [validate_trace(steered_timers(rng, f"gen-timers-{i:03}")) for i in range(args.generated)]
    if args.controls:
        selected += list(finish(controls()).values())
    if args.only:
        names = set(args.only.split(","))
        selected = [t for t in selected if t["id"] in names]
    sites = load_hidden_sites()
    by_label = {entry["label"]: entry for entry in sites.values()}
    out = args.probe.resolve()
    calls = call_sites(KERNEL / "vmlinux", out.parent / "cache")
    steer_wire = {t["id"]: resolve_steering(t, by_label, calls) for t in selected}
    if not args.summarize_only:
        out.mkdir(parents=True)
        (out / "traces.jsonl").write_text("".join(json.dumps(t) + "\n" for t in selected))
        run_linux(selected, out / "linux", timeout=900, steer_wire=steer_wire, arm_records=True,
                  guest_variant=args.guest_variant)
    report, per, meta = summarize(out, selected, sites)
    ids = {t["id"] for t in selected}
    if {"d3_persistent_keepalive", "d3_persistent_natural"} <= ids:
        roles = {entry["label"]: entry["role"] for entry in sites.values()}

        def signature(tid):
            sigs = [firing_signature(labels, roles, "wg_expired_send_persistent_keepalive")
                    for labels in meta[(tid, "pc")]]
            return [s for s in sigs if s[0]]
        virtual, natural = signature("d3_persistent_keepalive"), signature("d3_persistent_natural")
        report["natural_vs_virtual"] = dict(virtual=virtual, natural=natural, same=virtual == natural)
    (out / "summary.json").write_text(json.dumps(report, indent=1) + "\n")
    for name, entry in report.items():
        if name == "natural_vs_virtual":
            print("== natural vs virtual:", entry["same"])
            continue
        print(f"== {name} fired={entry['fired_in_op']} missing={entry['fired_labels_missing']}"
              f" steering={entry['steering']} jiffies={entry['jiffies_problems']} sections={entry['section_problems']}"
              f" sites={entry['site_problems']}")
        for line in entry["ops"]:
            print("  " + line[:600])
    print(Counter(json.loads(l)["current"] for l in (out / "linux/clocksource.jsonl").read_text().splitlines()))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--probe", type=Path, help="run on Linux alone into this new directory")
    parser.add_argument("--only")
    parser.add_argument("--controls", action="store_true", help="also probe the timer controls")
    parser.add_argument("--generated", type=int, default=0, help="probe this many steered_timers traces instead")
    parser.add_argument("--generated-seed", type=int, default=1)
    parser.add_argument("--guest-variant")
    parser.add_argument("--summarize-only", action="store_true")
    args = parser.parse_args()
    if args.probe:
        probe(args)
        return
    for directory, written in ((ROOT / "corpus" / "wireguard", finish(traces())),
                               (ROOT / "corpus" / "timer-controls", finish(controls()))):
        directory.mkdir(exist_ok=True)
        for name, trace in written.items():
            (directory / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
        print(f"wrote {len(written)} traces to {directory}")


if __name__ == "__main__":
    main()
