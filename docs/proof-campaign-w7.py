"""Generate explicit records for the tracked eight-operation W7 ring-wrap recipe.

The operations are unchanged. The records combine the existing historical
session seed with a generated non-yielding burst schedule; this is not a Linux
capture. Timer-arm and destination-cache records use the original disabled
modes, and every hidden read those modes require is supplied explicitly.
"""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("recipes", ROOT / "docs/proof-campaign-replay.py")
recipes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(recipes)

trace = json.loads((ROOT / "corpus/w7-tier/w7_ring_wrap.json").read_text())
seed = recipes.historical_session_seed()
if (len(trace["ops"]) != 8 or trace["ops"][3]["message"] != seed["ops"][3]["message"]
        or len(trace["ops"][4]["items"]) != 1 or len(trace["ops"][5]["items"]) != 1024):
    raise ValueError("tracked W7 operations no longer match the source recipe")
trace.pop("steer", None)
trace.pop("expect", None)
trace["arm_records"] = False
trace["dst_cache_records"] = False


def record(site, value=0):
    width = 16 if site in {40, 42, 44, 46, 48, 50} else 8
    return [site, value.to_bytes(width, "little").hex()]


def batch(count):
    records = [record(6, 133000000000) for _ in range(count)]
    records.extend([record(44), record(45), record(46)])
    for _ in range(min(count, 1022)):
        records.extend([record(20, 112), record(48), record(49)])
        if count == 1:
            records.append(record(16, 160))
        records.append(record(6, 133000000000))
    records.append(record(47))
    return records


trace["hidden"] = seed["hidden"][:4] + [batch(1), batch(1024), [], []]
for operation in trace["hidden"]:
    for rec in operation:
        if rec[0] in {40, 42, 44, 46, 48, 50} and len(rec[1]) == 16:
            rec[1] += "0000000000000000"
recipes.add_wait_bounds(trace, range(len(trace["ops"]) - 1))
print(json.dumps(trace, separators=(",", ":")))
