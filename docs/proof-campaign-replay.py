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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", choices=["r1-inclusive-floor"])
    args = parser.parse_args()
    print(json.dumps(inclusive_floor(), separators=(",", ":")))
