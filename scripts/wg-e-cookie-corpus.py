#!/usr/bin/env python3
"""Writes the stage E arm-4 traces (cookie-reply consumption and the MAC2 it
unlocks, docs/2026-10-05-e-dos.md section 6.A) into corpus/wireguard/e_*.json.

wg0 initiates with steered values, as in D1 (scripts/wg-d1-corpus.py); the
fixture's sender then answers with a cookie reply (type 3, 64 bytes) naming
wg0's index, the cookie encrypted with XChaCha20-Poly1305 under
BLAKE2s("cookie--" || the peer's public key) and AAD = the MAC1 of wg0's
initiation (harness/noise.py `cookie_message`). The cookie and nonce are the
trace's choice: the reply comes from the fixture, not from wg0's secret.

To make wg0 initiate again within the trace's time bound, a trace changes
wg0's private key: wg_noise_expire_current_peer_keypairs (netlink.c:574,
noise.c:179-184) clears the handshake and resets last_sent_handshake, and
leaves latest_cookie alone (it is written only in cookie.c). The peer's
set_peer then sends the staged keepalive (netlink.c:483-484), which queues an
initiation. Its MAC2 is compute_mac2(message, cookie) while the cookie is
valid and fresh (cookie.c:170-174), else zero.

The output is deterministic: rerunning this script reproduces the files.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness import noise  # noqa: E402

d1 = __import__("wg-d1-corpus")

PEER_PUBLIC = noise.public_key(d1.PEER)
COOKIE = bytes(range(0xc0, 0xd0))
COOKIE_2 = bytes(range(0xe0, 0xf0))
NONCE = bytes(range(0x60, 0x78))
NONCE_2 = bytes(range(0x90, 0xa8))
INDEX_2 = 0x1a2b3c4d   # wg0's index for its second initiation

CONSUMED = ["wg_cookie_message_consume.decrypted=1"]


def reply(cookie=COOKIE, nonce=NONCE, index=d1.INDEX, **kw):
    """The cookie reply to wg0's first (steered) initiation."""
    mac1 = noise.last_mac1(d1.wg0_initiation())
    return noise.cookie_message(index, cookie, nonce, mac1, PEER_PUBLIC, **kw)


def rekey():
    """wg0's private key changes; the peer, named without attributes, sends
    its staged keepalive, which queues the second initiation."""
    return {"op": "wg_set", "config": {"private_key": d1.key(d1.OTHER_DEVICE),
                                       "peers": [{"public_key": d1.key(PEER_PUBLIC)}]}}


def steer_both():
    return d1.steer_initiation() + d1.steer_initiation(d1.EPHEMERAL_2, d1.CLOCK_2, INDEX_2)


def second_initiation(cookie=None):
    """What wg0 sends after the key change: MAC2 under `cookie`, or zero."""
    init = d1.wg0_initiation(device=d1.OTHER_DEVICE, ephemeral=d1.EPHEMERAL_2, clock=d1.CLOCK_2, index=INDEX_2)
    return noise.with_mac2(init, cookie) if cookie else init


def traces():
    head = d1.setup() + [d1.OBSERVE]
    out = {
        # the reply is consumed; the re-initiation carries a real MAC2
        "e_cookie_then_reinitiate": (
            head + [d1.inject(reply()), d1.OBSERVE, rekey(), d1.OBSERVE, d1.GET], steer_both(),
            CONSUMED + ["wg_cookie_add_mac_to_packet.cookie_fresh=1"]),
        # a second valid reply after a consumed one: have_sent_mac1 is false,
        # so the C goes to out (cookie.c:212) without decrypting
        "e_cookie_double_reply": (
            head + [d1.inject(reply()), d1.OBSERVE, d1.inject(reply(COOKIE_2, NONCE_2)), d1.OBSERVE, d1.GET],
            d1.steer_initiation(), CONSUMED + ["wg_cookie_message_consume.no_mac1_sent=1"]),
        # the AAD is not wg0's last MAC1: the decrypt fails, nothing is
        # stored, and the re-initiation's MAC2 is zero
        "e_cookie_bad_mac1_aad": (
            head + [d1.inject(reply(aad=bytes(16))), d1.OBSERVE, rekey(), d1.OBSERVE, d1.GET], steer_both(),
            ["wg_cookie_message_consume.decrypted=0", "wg_cookie_add_mac_to_packet.cookie_valid=0"]),
        # a receiver index wg0 does not hold: the lookup misses
        "e_cookie_wrong_index": (
            head + [d1.inject(reply(index=d1.INDEX ^ 0x0101)), d1.OBSERVE, d1.GET], d1.steer_initiation(),
            ["wg_cookie_message_consume.lookup_miss=1"]),
    }
    return {name: {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": expect}
            for name, (ops, steer, expect) in out.items()}


def main():
    out = ROOT / "corpus" / "wireguard"
    written = traces()
    for name, trace in written.items():
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(written)} traces to {out}")
    # the bytes Linux must send after the key change (for reading reports)
    print("e_cookie_then_reinitiate second initiation:", second_initiation(COOKIE).hex())
    print("e_cookie_bad_mac1_aad second initiation:   ", second_initiation().hex())


if __name__ == "__main__":
    main()
