#!/usr/bin/env python3
"""L0, the Linux-only lifecycle probe (docs/2026-10-05-l-lifecycle.md,
section 11). Runs probe traces of wg_create, wg_down/wg_up, a running port
change, the random port, wg_delete, a recreation and the fail() teardown on
the oracle kernel, without the mirror (it stops `unsupported` on these
operations until stream M), and reports per operation:

- the choice records: kind, length, the consumer frame (the first frame
  outside the random and clock helpers, as the check attributes them), and
  whether the mirror's site table declares that (kind, frame);
- the KCOV counts per stream and child against the guest's bounds;
- the wall time of the lifecycle operations (LEANUX_TIMING);
- the results and the dumps' ifindex and listen_port.

    LEANUX_KERNEL_DIR=... scripts/in-bundle python3 scripts/wg-l0-probe.py OUT_DIR [--analyze-only]

OUT_DIR (inside the task's .artifacts) receives one run directory per batch
and summary.json. The run directories are large; delete them once read.
"""
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness.linux import ARTIFACTS, KERNEL, LinuxRunError, run_linux  # noqa: E402
from harness.steer import CHOICE_HELPERS, call_sites  # noqa: E402
from harness.trace import KCOV_CAPACITY, validate_trace  # noqa: E402
from evaluator.coverage import symbolize  # noqa: E402

KEY1 = "11" * 32
PEER = "22" * 32
PEER_CFG = {"public_key": PEER, "endpoint": {"family": 6, "addr": "0" * 31 + "1", "port": 51999},
            "keepalive": 25, "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}


def op(name, **kw):
    return dict(op=name, **kw)


def wg_set(**config):
    return op("wg_set", config=config)


XMIT = op("wg_xmit", packet={"family": 4, "dst": "0a000001"})

TRACES = [
    # bare: ENODEV before creation; create (ifindex 3); EEXIST; delete;
    # ENODEV, stats null; ENODEV on a second delete; recreate (ifindex 4)
    {"version": 1, "id": "l0_bare_create", "net_fixture": "bare", "ops": [
        op("wg_get"), op("wg_create"), op("wg_get"), op("wg_create"), op("wg_observe"),
        op("wg_delete"), op("wg_get"), op("wg_up"), op("wg_down"), op("wg_observe"), op("wg_delete"),
        op("wg_create"), op("wg_get"), op("wg_delete")]},
    # the fixture's wg0: up on a fixed port, down, xmit without routes, up
    # again (the re-add rules), the no-op up and down, delete of a down device
    {"version": 1, "id": "l0_down_up", "ops": [
        wg_set(listen_port=51820), op("wg_up"), op("wg_get"), op("wg_down"), op("wg_get"), XMIT,
        op("wg_up"), op("wg_up"), XMIT, op("wg_get"), op("wg_down"), op("wg_down"), op("wg_delete"),
        op("wg_observe")]},
    # an up without a port: the random draw; down/up keeps it; delete of an up device
    {"version": 1, "id": "l0_random_port", "ops": [
        op("wg_up"), op("wg_get"), op("wg_down"), op("wg_up"), op("wg_get"), op("wg_delete"), op("wg_get")]},
    # a running port change: free port, a fixture port (EADDRINUSE), port 0
    # (a random draw while bound), the same port; delete while up
    {"version": 1, "id": "l0_set_port_running", "ops": [
        wg_set(listen_port=51820), op("wg_up"), wg_set(listen_port=51821), op("wg_get"),
        wg_set(listen_port=51998, fwmark=7), op("wg_get"), wg_set(listen_port=0), op("wg_get"),
        wg_set(listen_port=51821), op("wg_delete")]},
    # wg_up on the two fixture ports, then a free one
    {"version": 1, "id": "l0_up_fixture_ports", "ops": [
        wg_set(listen_port=51999), op("wg_up"), XMIT, wg_set(listen_port=51998), op("wg_up"),
        wg_set(listen_port=51820), op("wg_up"), op("wg_get")]},
    # a peer with a keepalive: the initiation at up, a down (reset of
    # last_sent_handshake), the up's keepalive initiation, delete while up
    {"version": 1, "id": "l0_peer_down_up_delete", "ops": [
        wg_set(private_key=KEY1, listen_port=51820, peers=[PEER_CFG]), op("wg_up"), op("wg_observe"),
        op("wg_down"), op("wg_observe"), op("wg_up"), op("wg_observe"), op("wg_delete"), op("wg_observe")]},
    # bare: create, configure, up, delete, create again (the ratelimiter key
    # drawn again: the refcount returned to 0), get
    {"version": 1, "id": "l0_delete_create", "net_fixture": "bare", "ops": [
        op("wg_create"), wg_set(private_key=KEY1, listen_port=51820, peers=[PEER_CFG]), op("wg_up"),
        op("wg_observe"), op("wg_delete"), op("wg_create"), op("wg_get"), op("wg_up"), op("wg_get"),
        op("wg_delete")]},
]
# A batch of its own: a trace that fails with wg0 live and up (rlimit 8: no
# free descriptor for the route socket after wg_up), then a bare creation whose
# window must show the ratelimiter key draw (the refcount is 0 again only
# if fail() deleted wg0 synchronously).
FAIL_TRACES = [
    {"version": 1, "id": "l0_fail_live", "rlimit_nofile": 8, "ops": [wg_set(listen_port=51820), op("wg_up"),
                                                                     op("wg_delete")]},
    {"version": 1, "id": "l0_after_fail", "net_fixture": "bare", "ops": [op("wg_create"), op("wg_get"),
                                                                         op("wg_delete")]},
]


def hidden_sites():
    out = subprocess.run([str(ROOT / ".lake/build/bin/leanux-model"), "--hidden-sites"], capture_output=True,
                         check=True).stdout
    return {(e["kind"], f"{e['file']}:{e['line']}"): e for e in json.loads(out)}


def kind_class(kind):
    kind &= 0x7fff
    return "random" if kind in {1, 101, 102, 104, 108, 110} else "clock" if 200 <= kind <= 216 \
        else "section" if kind in (300, 301) else "resched" if kind == 302 else f"kind{kind}"


def read_lines(run, prefix):
    rows = []
    for line in (run / "boot.log").read_text(errors="replace").splitlines():
        line = line.rstrip("\r")
        if line.startswith(prefix + " "):
            rows.append(json.loads(line[len(prefix) + 1:]))
    return rows


def analyze(run, traces, sites):
    ops = {t["id"]: t["ops"] for t in traces}
    hidden = [json.loads(line) for line in (run / "hidden.jsonl").read_text().splitlines()]
    ips = sorted({r[1] for row in hidden for r in row["records"]})
    frames = symbolize([{"pcs": ips}], KERNEL / "vmlinux")["locations"] if ips else {}
    per = {}
    for row in hidden:
        key = (row["id"], row["index"])
        entry = per.setdefault(key, {"op": ops[row["id"]][row["index"]]["op"], "records": {}, "counts": {}})
        for kind, ip, _seq, length, _data in row["records"]:
            chain = [f["source"].split("/.deps/linux/")[-1].split(" ")[0] for f in frames.get(ip, [])]
            consumer = next((s for s in chain if s.split(":")[0] not in CHOICE_HELPERS), None)
            cls = kind_class(kind)
            site = sites.get((cls, consumer)) if cls not in ("section",) else None
            label = site["label"] if site else ("section" if cls == "section" else "UNDECLARED")
            name = f"{row['stream']}:{row['mode']}:{kind & 0x7fff}:{consumer}:{length}:{label}"
            entry["records"][name] = entry["records"].get(name, 0) + 1
    for prefix, stream, mode in (("LEANUX_COVERAGE", "task", "pc"), ("LEANUX_RCOVERAGE", "remote", "pc"),
                                 ("LEANUX_CMP", "task", "cmp"), ("LEANUX_RCMP", "remote", "cmp")):
        for row in read_lines(run, prefix):
            entry = per.setdefault((row["id"], row["index"]), {"op": ops[row["id"]][row["index"]]["op"],
                                                               "records": {}, "counts": {}})
            entry["counts"][f"{stream}:{mode}"] = row["count"]
    for row in read_lines(run, "LEANUX_TIMING"):
        per[(row["id"], row["index"])].setdefault("wall_ms", {})[row["mode"]] = round(row["ns"] / 1e6, 2)
    return per


def main():
    out = Path(sys.argv[1]).resolve()
    analyze_only = "--analyze-only" in sys.argv[2:]
    sites = hidden_sites()
    bounds = {"pc": KCOV_CAPACITY - 1, "cmp": (KCOV_CAPACITY - 1) // 4,
              "pc_at_64k": 64 * 1024 - 1, "cmp_at_64k": (64 * 1024 - 1) // 4}
    summary = {"kernel": str(KERNEL), "bounds": bounds, "batches": {}}
    for name, traces in (("main", TRACES), ("fail", FAIL_TRACES)):
        traces = [validate_trace(t) for t in traces]
        run = out / name
        status, results = "complete", None
        if not analyze_only:
            try:
                results = run_linux(traces, run, timeout=600)
            except LinuxRunError as exc:
                status = f"{exc.kind}: {exc}"
        else:
            status = json.loads((run / "run-status.json").read_text())["kind"]
        if results is None and (run / "observations.jsonl").exists():
            results = [json.loads(line) for line in (run / "observations.jsonl").read_text().splitlines()]
        per = analyze(run, traces, sites) if (run / "hidden.jsonl").exists() else {}
        errors = (run / "guest-errors.jsonl").read_text().splitlines() if (run / "guest-errors.jsonl").exists() else []
        batch = {"status": status, "guest_errors": [json.loads(e) for e in errors], "traces": {}}
        for t in traces:
            obs = next((r["observations"] for r in results or [] if r["id"] == t["id"]), None)
            rows = []
            for i, o in enumerate(t["ops"]):
                entry = per.get((t["id"], i), {})
                row = {"index": i, "op": o["op"], "counts": entry.get("counts"), "records": entry.get("records"),
                       "wall_ms": entry.get("wall_ms")}
                if obs:
                    row["ret"] = obs[i]["ret"]
                    if "device" in obs[i]:
                        row["device"] = {k: obs[i]["device"].get(k) for k in ("ifindex", "listen_port", "fwmark")}
                    if "stats" in obs[i]:
                        row["stats"] = obs[i]["stats"]
                rows.append(row)
            batch["traces"][t["id"]] = rows
        summary["batches"][name] = batch
    # the port draw's call sites in the image (steerability, section 3.3)
    sites_in_image = call_sites(KERNEL / "vmlinux", ARTIFACTS / "cache")
    summary["udp_port_draw_sites"] = {f"{k}:{c}": v for (k, c), v in sites_in_image.items()
                                      if k != "tail_jumps" and c.startswith("net/ipv4/udp.c:")}
    summary["udp_tail_jump_functions"] = [f for f in sites_in_image.get(("tail_jumps", ""), []) if "udp" in f]
    undeclared = Counter()
    for batch in summary["batches"].values():
        for rows in batch["traces"].values():
            for row in rows:
                for name, n in (row["records"] or {}).items():
                    if name.endswith(":UNDECLARED"):
                        undeclared[f"{row['op']} {name}"] += n
    summary["undeclared"] = dict(undeclared)
    (out / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({"statuses": {k: v["status"] for k, v in summary["batches"].items()},
                      "undeclared": summary["undeclared"]}, indent=1))


if __name__ == "__main__":
    main()
