#!/usr/bin/env python3
"""D3 stream K: Linux-only probe traces for the timer kernel change
(docs/2026-10-05-d3-timers.md, section 11, stream K, step 2).

Each trace advances virtual time with `wg_advance` so that one WireGuard timer
fires, on a kernel built from kernel/patches/choice-stream.patch with the arm
records switched on (harness/linux.py ARM_RECORDS is off by default). Steered
traces complete a session as D1 does (scripts/wg-d1-corpus.py). No mirror
runs: the output is the kernel's record streams, summarized per operation:
section starts and stops (by symbol), arm records (kind 303: jiffies,
expires, delay, consumer frame), advance records (kind 304: before, after),
and the datagrams each wg_observe saw.

    LEANUX_KERNEL_DIR=... scripts/in-bundle python3 scripts/d3-k-probes.py --out DIR [--only NAME,...]
"""
import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from harness.linux import DISPATCH_SYMBOLS, KERNEL, dispatch_addresses, run_linux  # noqa: E402
from harness.steer import call_sites, resolve as resolve_steering  # noqa: E402
from harness.trace import validate_trace  # noqa: E402

d1 = __import__("wg-d1-corpus")
rx = __import__("wg-d2-rx-probes")

XMIT = {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001", "payload": "6c65757864337072"}}


def advance(ticks):
    return {"op": "wg_advance", "ticks": ticks}


def traces():
    resp, key, index = rx.session()
    steer = d1.steer_initiation()
    session = d1.setup() + [d1.OBSERVE, d1.inject(resp.message)]
    no_keepalive = [{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT,
                                                "peers": [d1.peer()]}}, {"op": "wg_up"}]
    out = {
        # no session: the xmit stages a packet and queues an initiation, whose
        # send arms the retransmit timer (1250 + [0, 83) ticks); two advances
        # of 1450 fire it twice (attempts 1, 2)
        "k_retransmit": (no_keepalive + [XMIT, d1.OBSERVE, advance(1450), d1.OBSERVE, advance(1450), d1.OBSERVE], None),
        # a session, two data messages (the second sets need_another_keepalive),
        # advance 2600: the keepalive fires, re-arms (+10 s), and the tx
        # worker's any_authenticated_packet_sent deletes the re-arm
        "k_keepalive": (session + [d1.inject(rx.data_message(key, index, 0, rx.ipv4_udp(b"one"))),
                                   d1.inject(rx.data_message(key, index, 1, rx.ipv4_udp(b"two"))),
                                   advance(2600), d1.OBSERVE], steer),
        # a session, a data packet sent (data_sent arms new_handshake at
        # 3750 + [0, 83)), advance 3950: a fresh initiation
        "k_new_handshake": (session + [XMIT, advance(3950), d1.OBSERVE], steer),
        # a session with persistent keepalive 25 s (6250 ticks, level 3: up to
        # 512 late), advance 6800: a keepalive
        "k_persistent": (session + [d1.OBSERVE, advance(6800), d1.OBSERVE], steer),
        # a session, advance 139200 (540 s + 4096 + 25): the zero-key timer
        # and its clear work, after the persistent keepalive
        "k_zero_key": (session + [d1.OBSERVE, advance(139200), d1.OBSERVE, d1.GET], steer),
        # no WireGuard timer pending: the advance records alone
        "k_advance_only": ([{"op": "wg_set", "config": {"private_key": d1.key(d1.DEVICE), "listen_port": d1.PORT}},
                            {"op": "wg_up"}, advance(1), advance(250), d1.OBSERVE], None),
    }
    result = []
    for name, (ops, schedule) in out.items():
        trace = {"version": 1, "id": name, "ops": ops}
        if schedule:
            trace["steer"] = schedule
        result.append(validate_trace(trace))
    return result


def summarize(out, traces):
    from evaluator.check import hidden_records, load_hidden_sites  # noqa: F401
    from evaluator.coverage import symbolize
    rows = [json.loads(line) for line in (out / "linux/hidden.jsonl").read_text().splitlines()]
    per = hidden_records(traces, rows)
    ips = sorted({r[1] for ops in per.values() for op in ops for r in op})
    frames = symbolize([{"pcs": ips}], KERNEL / "vmlinux")["locations"]
    symbol = dict(zip(dispatch_addresses(KERNEL), DISPATCH_SYMBOLS))
    observations = {json.loads(l)["id"]: json.loads(l) for l in (out / "linux/observations.jsonl").read_text().splitlines()}
    observed = {}
    for line in (out / "linux/boot.log").read_text().splitlines():
        if line.startswith("LEANUX_WGOBS "):
            record = json.loads(line[len("LEANUX_WGOBS "):])
            observed[(record["id"], record["index"])] = record
    report = {}
    for trace in traces:
        lines = []
        for i, (op, records) in enumerate(zip(trace["ops"], per[(trace["id"], "pc")])):
            desc = []
            for kind, ip, seq, length, data, func in records:
                words = [int.from_bytes(bytes.fromhex(data[k:k + 16]), "little") for k in range(0, len(data), 16)]
                if kind in (300, 301):
                    desc.append(f"{'start' if kind == 300 else 'stop'}:{symbol.get(func, hex(func))}")
                elif kind == 303:
                    consumer = next((f["source"].split("/.deps/linux/")[-1].split(" ")[0] for f in frames[ip]
                                     if "include/" not in f["source"]), "?")
                    caller = frames[ip][-1]["function"]
                    desc.append(f"arm303(j={words[0]},e={words[1]},d={words[1] - words[0]},{consumer},{caller})")
                elif kind == 304:
                    desc.append(f"adv304(before={words[0]},after={words[1]},d={words[1] - words[0]})")
                else:
                    desc.append(str(kind & 0x7fff))
            obs = observations[trace["id"]]["observations"][i]
            extra = ""
            if op["op"] == "wg_observe":
                record = observed[(trace["id"], i)]
                extra = (f" datagrams={[(d[0], d[1], d[2]) for d in record['datagrams']]}"
                         f" replies={[(r[3], r[4]) for r in record['replies']]} stats={record['stats']}")
            lines.append(f"[{i}] {op['op']} ret={obs['ret']}{extra}: " + " ".join(desc))
        report[trace["id"]] = lines
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--only")
    parser.add_argument("--no-arm-records", action="store_true")
    parser.add_argument("--summarize-only", action="store_true", help="summarize an existing --out")
    args = parser.parse_args()
    from evaluator.check import load_hidden_sites
    selected = traces()
    if args.only:
        names = set(args.only.split(","))
        selected = [t for t in selected if t["id"] in names]
    sites = load_hidden_sites()
    by_label = {entry["label"]: entry for entry in sites.values()}
    calls = call_sites(KERNEL / "vmlinux", args.out.resolve().parent / "cache")
    steer_wire = {t["id"]: resolve_steering(t, by_label, calls) for t in selected if "steer" in t}
    out = args.out.resolve()
    if not args.summarize_only:
        out.mkdir(parents=True)
        (out / "traces.jsonl").write_text("".join(json.dumps(t) + "\n" for t in selected))
        run_linux(selected, out / "linux", timeout=600, steer_wire=steer_wire, arm_records=not args.no_arm_records)
    report = summarize(out, selected)
    (out / "summary.json").write_text(json.dumps(report, indent=1) + "\n")
    sections = [json.loads(l) for l in (out / "linux/sections.jsonl").read_text().splitlines()]
    for name, lines in report.items():
        print(f"== {name} {[(s['mode'], s['opened'], s['dropped']) for s in sections if s['id'] == name]}")
        for line in lines:
            print("  " + line)
    print(Counter(json.loads(l)["current"] for l in (out / "linux/clocksource.jsonl").read_text().splitlines()))


if __name__ == "__main__":
    main()
