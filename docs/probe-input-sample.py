#!/usr/bin/env python3
"""Fixed, unfiltered sample for the 2026-10-21 scope probe, not a new suite.

--emit prints the frozen sample without executing the model or Linux.
--run uses the existing checker with only candidate selection and chunking
replaced in this process. No checker, harness or mirror source is changed.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root))
from evaluator.generate import generate_wireguard
from harness.trace import validate_trace

parser = argparse.ArgumentParser(description=__doc__)
mode = parser.add_mutually_exclusive_group(required=True)
mode.add_argument("--emit", action="store_true")
mode.add_argument("--run", action="store_true")
args = parser.parse_args()

sample = generate_wireguard(20261021, 16, max_ops=12, steered=.15, data=.15,
                           timers=.10, alloc=.05, lifecycle=.10, routing=.05, netns=.03)
payload = "".join(json.dumps(t, sort_keys=True, separators=(",", ":")) + "\n" for t in sample)
print(f"sample: {len(sample)} traces, sha256 {hashlib.sha256(payload.encode()).hexdigest()}",
      file=sys.stderr, flush=True)
if args.emit:
    sys.stdout.write(payload)
    raise SystemExit(0)

# Retain parser failures as failures of this selected sample. Do not replace
# them with later candidates or label them differential agreement.
validated, rejected = [], []
for trace in sample:
    try:
        validated.append(validate_trace(trace))
    except ValueError as error:
        rejected.append(trace["id"])
        print(f"SCOPE INPUT REFUSAL {trace['id']}: {error}", file=sys.stderr, flush=True)

from evaluator import check

def no_domain_filter(_traces):
    raise RuntimeError("the independent sample must not call the domain filter")

def fixed_candidates(*_args, **_kwargs):
    return validated

def singletons(traces):
    for index, trace in enumerate(traces):
        yield index, [trace], f"probe-{index:02}"

check.domain_filter = no_domain_filter
check.load_traces = fixed_candidates
check.chunk_traces = singletons
stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
out = Path(os.environ.get("LEANUX_ARTIFACTS", root / ".artifacts")) / f"scope-probe-{stamp}"
status = check.main(["--suite", "wireguard", "--out", str(out)])
raise SystemExit(status or bool(rejected))
