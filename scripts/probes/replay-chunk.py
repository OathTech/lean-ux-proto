#!/usr/bin/env python3
"""Replay a recorded chunk's Linux outputs through this tree's mirror and
checker: `run_chunk` with `run_linux` replaced by a copy of the recorded
`linux/` directory, re-collected by the harness's own parser. Deterministic
evidence for a check path that depends on what the kernel happened to do
in one run (the W7 placement selection with a thousand open polls, which a
quiet box never exercises and a loaded one exercises by chance). Run from
the repository root with `LEANUX_KERNEL_DIR` at the build the chunk ran on:

    scripts/in-bundle python3 -B scripts/probes/replay-chunk.py \
        <recorded chunk>/linux <suite> <trace id> .artifacts/check/<new dir>

The output directory is a fresh directory under `.artifacts`; the result
line is the trace's outcome, its problems, and the selected placements."""
import json
import shutil
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
import evaluator.check as check  # noqa: E402
import harness.linux as linux  # noqa: E402


def main(argv):
    recorded, suite, trace_id, out = Path(argv[0]).resolve(), argv[1], argv[2], Path(argv[3]).resolve()
    if not (recorded / 'boot.log').exists():
        sys.exit(f'{recorded}: not a recorded linux directory (no boot.log)')
    if out.exists():
        sys.exit(f'{out}: exists')

    def replay_linux(traces, outdir, **kw):
        shutil.copytree(recorded, outdir)
        return linux._collect(outdir, traces, 0, None)   # the recorded boot.log, parsed as the run parsed it
    check.run_linux = replay_linux
    config = check.load_kcov_config()
    traces = check.load_traces([suite], {}, 20260920, trace_id, Counter(), check.ALLOC_SHARE, {})
    if [t['id'] for t in traces] != [trace_id]:
        sys.exit(f'{suite} selects {[t["id"] for t in traces]} for {trace_id}')
    decisions = check.load_decisions(config)
    instrumented, functions, _ = check.instrumented_lines(check.KERNEL / 'vmlinux', config['functions'], config['files'])
    kcov = (config, decisions, check.witness_table(decisions, instrumented, functions, config['branch_free_functions']),
            instrumented, functions)
    results, _, outcomes = check.run_chunk(traces, out, kcov)
    r = results[trace_id]
    print('outcome:', r['outcome'], 'side:', r.get('side'), 'detail:', str(r.get('detail'))[:300])
    for p in r.get('problems', [])[:8]:
        print('  problem:', json.dumps(p)[:300])
    print('selected before the put:', {k: v[:200] for k, v in outcomes.items() if k.startswith('napi placement')})
    print('selection runs:', sorted(d.name for d in out.glob('model-cmp-napi-*')))
    return 0 if r['outcome'] == 'agreement' else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
