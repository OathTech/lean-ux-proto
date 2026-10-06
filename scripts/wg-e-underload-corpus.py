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


def valid_initiation(index, ephemeral):
    """A valid-MAC1 initiation to wg0 (MAC1 keyed by blake2s('mac1----' ||
    wg0_public)); its body is not consumed (the under-load path sends a cookie
    and returns before consume_initiation)."""
    return noise.initiation(noise.public_key(DEVICE), PEER, ephemeral, noise.tai64n(1, 0), index)


def inject(index, ephemeral):
    return {"op": "wg_inject", "family": 4, "port": PORT, "message": valid_initiation(index, ephemeral).hex()}


def flood(**extra):
    op = {"op": "wg_flood", "count": FLOOD_COUNT, "port": PORT}
    op.update(extra)
    return op


def base_ops():
    return [CREATE, configure(), UP]


def traces():
    # corpus/wireguard (default suite): robust, no injection, so no decay-timing
    # dependence. The flood crosses the under_load threshold and its receive-
    # worker section is discarded; no cookie reply (the invalid-MAC1 flood is
    # reply-free). Validates the flood op, the section-bracket discard and the
    # under_load reach (receive.c:115 covered) independently of the 1-second decay.
    return {
        "e_underload_flood": base_ops() + [flood(), OBSERVE, GET],
    }


def decay_traces():
    # corpus/underload-decay (opt-in suite): the decay-lever cookie-reply traces.
    # A flood sets last_under_load; valid-MAC1 initiations injected within the
    # one-second decay each yield exactly one byte-exact cookie reply. The flood
    # drain (~512 keyed-BLAKE2s MAC1 checks) can exceed the decay in the slower
    # comparison guest child under instrumented TCG, so these are opt-in and run
    # on a host where that drain fits the decay (docs/2026-10-05-e-dos.md §4.1).
    return {
        "e_underload_cookie": base_ops() + [flood(), inject(0x1111_1111, b"\x51" * 32), OBSERVE, GET],
        "e_underload_two_replies": base_ops()
        + [flood(), inject(0x2222_2222, b"\x52" * 32), inject(0x3333_3333, b"\x53" * 32), OBSERVE, GET],
    }


def controls():
    return {
        # the valid initiation is bundled into the flood's io_uring batch, so
        # the kernel processes it in the flood's (discarded) receive-worker
        # section (a merged injection at D=0). The mirror's section-bracket
        # discard meets the reply's modeled records inside the flood section and
        # fails closed (the two-distinct-sections assertion, §4.1).
        "e_underload_merged": base_ops()
        + [flood(messages=[valid_initiation(0x4444_4444, b"\x54" * 32).hex()]), OBSERVE, GET],
    }


def write_suite(subdir, cases):
    out = ROOT / "corpus" / subdir
    out.mkdir(exist_ok=True)
    for name, ops in cases.items():
        (out / f"{name}.json").write_text(json.dumps({"version": 1, "id": name, "net_fixture": "bare", "ops": ops},
                                                     indent=2) + "\n")


def main():
    write_suite("wireguard", traces())
    write_suite("underload-decay", decay_traces())
    write_suite("underload-controls", controls())
    print(f"wrote {len(traces())} wireguard, {len(decay_traces())} underload-decay, "
          f"{len(controls())} control traces")


if __name__ == "__main__":
    main()
