"""Generate an initialized, sessionless retry/give-up mirror input.

This is a synthetic schedule, not a Linux capture. The operations/configuration
come from the tracked d3 corpus; clocks, draws and timer-wheel records are
explicit generated inputs which the actual runner must accept. The schedule
follows the updated R6 recipe described by campaign 1, without importing its
proof observer or its general recipe generator.
"""

import argparse
import json
from pathlib import Path


def record(site, *words):
    return [site, b"".join(word.to_bytes(8, "little") for word in words).hex()]


def arm(now, delay, unit):
    """This recipe arms only detached timers, with no other timer pending."""
    expiry = now + delay
    level = next(n - 1 for n in range(1, 10) if delay < 63 << (3 * (n - 1)))
    rounded = (expiry >> (3 * level)) + 1
    slot = 64 * level + (rounded & 63)
    bucket = rounded << (3 * level)
    return [record(100, now, expiry, unit), record(428, now, unit),
            record(429, slot, bucket, unit)]


def recipe(root):
    trace = json.loads((root / "corpus/wireguard/d3_retransmit_gives_up.json").read_text())
    draws = dict(trace["steer"][:3])
    ephemeral = draws["init_ephemeral"]
    index = int.from_bytes(bytes.fromhex(draws["index_draw"]), "little")
    trace["ops"] = trace["ops"][:23]
    if [op["op"] for op in trace["ops"]] != ["wg_set", "wg_up", "wg_xmit"] + ["wg_advance"] * 20:
        raise ValueError("corpus retry operations changed")
    trace["id"] = "c2_initialized_giveup"
    trace["ops"][0]["config"]["peers"][0]["keepalive"] = 0
    trace.pop("steer")
    trace.pop("expect")
    trace["arm_records"] = True
    trace["dst_cache_records"] = False
    base = 2**32 - 75000

    def tick(i):
        return base + 2500 + 1451 * i

    def coarse(i):
        return (tick(i) - base) * 4000000

    def send(i):
        seconds, nanos = divmod(123000000 + coarse(i) - coarse(0), 10**9)
        return [record(40, 0, 1), record(6, coarse(i)), record(7, coarse(i)),
                [1, ephemeral], record(3, 1700000000 + seconds, nanos), record(4, index),
                record(8, coarse(i)), record(48, 0, 0), record(49, 0),
                record(424, tick(i)), record(14, 1)] + arm(tick(i), 1250, 2) + [record(41, 0)]

    trace["hidden"] = [
        [record(5, coarse(0) - 8000000), record(128, tick(0) - 2)],
        [record(128, tick(0) - 1)],
        [record(6, coarse(0)), record(300, 1, 0)] + send(0) + [record(128, tick(0) + 1)],
    ]
    for i in range(1, 21):
        if trace["ops"][i + 2]["ticks"] != tick(i) - (tick(i - 1) + 1):
            raise ValueError("corpus advance duration changed")
        records = [record(101, tick(i - 1) + 1, tick(i)), record(102, 0, 2)]
        if i < 20:
            records += [record(6, coarse(i)), record(300, 1, 0), record(103, 0)] + send(i)
        else:
            records += [record(420, tick(i))] + arm(tick(i), 135000, 3) + [record(103, 0)]
        records.append(record(128, tick(i) + 1))
        trace["hidden"].append(records)
    return trace


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps(recipe(args.root), separators=(",", ":")))
