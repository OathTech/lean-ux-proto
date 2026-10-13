"""Reconstruct small proof-campaign witnesses from tracked fixtures.

Print one runner JSON input; no guest, kernel run, or retained run artifact.
"""
import argparse
import ast
import copy
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def recorded_fixture(name):
    tree = ast.parse((ROOT / "evaluator/test_model_replay.py").read_text())
    for node in tree.body:
        if (isinstance(node, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)):
            call = node.value
            if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute)
                    and isinstance(call.func.value, ast.Name)
                    and call.func.value.id == "json" and call.func.attr == "loads"
                    and len(call.args) == 1):
                raise ValueError(f"fixture {name} is no longer a literal json.loads call")
            return json.loads(ast.literal_eval(call.args[0]))
    raise ValueError(f"missing recorded fixture {name}")


def inclusive_floor():
    trace = recorded_fixture("CONTENDED_ROAM_CMP")
    window = json.loads((ROOT / "corpus/wireguard/rx_window.json").read_text())
    data_records = trace["hidden"][4]
    trace["id"] = "r1_inclusive_floor"
    trace["ops"] = trace["ops"][:4] + window["ops"][4:6]
    trace["hidden"] = trace["hidden"][:4] + [copy.deepcopy(data_records) for _ in range(2)]
    clocks = iter(["dde80fec1e000000", "1d2b1fec1e000000"])
    for record in trace["hidden"][5]:
        if record[0] == 6:
            record[1] = next(clocks)
    if next(clocks, None) is not None:
        raise ValueError("recorded data path no longer has exactly two clock reads")
    for records in trace["hidden"]:
        for record in records:
            if record[0] in {40, 42, 44, 46, 48, 50} and len(record[1]) == 16:
                record[1] += "0000000000000000"
    trace.pop("steer")
    trace["dst_cache_records"] = False
    trace["arm_records"] = False
    return trace


def stale_dump_cursor():
    """Exact synthetic choice records; this is not a Linux capture."""
    def peers(first, count):
        return {"op": "wg_set", "config": {"peers": [
            {"public_key": bytes([n]).hex() + "00" * 31}
            for n in range(first, first + count)
        ]}}

    def zero(site, size=8):
        return [site, "00" * size]

    return {
        "version": 1,
        "id": "r2_stale_dump_cursor",
        "dst_cache_records": False,
        "ops": [peers(1, 14), peers(15, 14), {"op": "wg_get_start"},
                {"op": "wg_delete"}, {"op": "wg_create"},
                peers(101, 14), peers(115, 13), {"op": "wg_get_recv"}],
        "hidden": [
            [zero(5) for _ in range(14)],
            [zero(5) for _ in range(14)],
            [zero(170)], [zero(124)],
            [zero(120), zero(121, 32), zero(122, 16), zero(123, 16),
             zero(126), zero(126)],
            [zero(5) for _ in range(14)],
            [zero(5) for _ in range(13)], [],
        ],
    }


def stale_dump_cursor_orphan():
    """Retain a trie owner after the stale cursor releases its replacement peer."""
    trace = stale_dump_cursor()
    trace["id"] = "r2_stale_dump_cursor_orphan"
    trace["ops"][6]["config"]["peers"][-1]["allowed_ips"] = [
        {"family": 4, "addr": "0a000000", "cidr": 8}]
    return trace


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    cases = {"r1-inclusive-floor": inclusive_floor,
             "r2-stale-dump-cursor": stale_dump_cursor,
             "r2-stale-dump-cursor-orphan": stale_dump_cursor_orphan}
    parser.add_argument("case", choices=cases)
    args = parser.parse_args()
    print(json.dumps(cases[args.case](), separators=(",", ":")))
