#!/usr/bin/env python3
"""Evaluator-level allocation controls (docs/2026-10-05-a-alloc.md, section
7): each case runs the whole check (Linux, record resolution, the steering
check and the mirror; `evaluator.check.run_chunk`) on one A1 trace, and must
produce a FAILING result of the stated kind. scripts/alloc-controls.py
checks the same controls on the kernel side only (Linux, no mirror).

    scripts/in-bundle python3 scripts/alloc-evaluator-controls.py \\
        --kernel .artifacts/kernel-net-choice-a \\
        --control-kernel .artifacts/kernel-net-choice-actl \\
        --out .artifacts/alloc-evaluator-controls

- K1 (control kernel, `record_ok`): the forced failure is recorded with
  outcome 1. Linux takes the failure arm; the record claims success.
- K4 (control kernel, `nofail`): the steered encounter counts as
  `__GFP_NOFAIL`: never failed, the entry left over.
- K5 (control kernel, `addr_naming`): naming by address only never names a
  helper site: the entry left over.
- C-kv (oracle): a fail record at the 8 KiB `kvmalloc` of the fd array (an
  `rlimit_nofile = 1024` trace whose `dup3` expands the table to 1024
  slots). Linux falls back to `vmalloc` and succeeds; the mirror must answer
  `unsupported "kvmalloc vmalloc fallback"`, never -ENOMEM. The host refuses
  to schedule this failure (harness/steer.py `alloc_refusal`); this control
  bypasses that refusal for its one trace, so the failure is forced (the
  record's steered bit is set) rather than natural; the mirror reads only
  the outcome byte, which is the same for both.
Each case runs in its own process, with LEANUX_KERNEL_DIR selecting the
kernel.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FAIL = '00' * 8
CTL = {'record_ok': 2, 'nofail': 4, 'addr_naming': 8}
CKV = {"version": 1, "id": "ac_kvmalloc_fallback", "rlimit_nofile": 1024,
       "ops": [{"op": "eventfd2", "init": 0, "flags": 0},
               {"op": "dup3", "fd": {"ref": 0}, "newfd": {"literal": 1000}, "flags": 0},
               {"op": "write", "fd": {"literal": 1000}, "count": 8, "value": "1"}],
       "steer": [["kvmallocFdArray", FAIL]]}


def corpus(name):
    return json.loads((ROOT / 'corpus/alloc' / f'{name}.json').read_text())


# case: (kernel option, load flags, trace, bypass the host's refusal, what must fail)
CASES = {
    'K1': ('control_kernel', CTL['record_ok'], corpus('a_sendbuf_init_nomem'), False,
           'a forced failure recorded as ok: the records disagree with Linux'),
    'K4': ('control_kernel', CTL['nofail'], corpus('a_sendbuf_init_nomem'), False,
           'a __GFP_NOFAIL encounter is never failed: the schedule is left over'),
    'K5': ('control_kernel', CTL['addr_naming'], corpus('a_sendbuf_init_nomem'), False,
           'naming by address only: the helper site is never steered, the schedule left over'),
    'C-kv': ('kernel', 0, CKV, True, 'the mirror answers unsupported "kvmalloc vmalloc fallback"'),
}


def run_case(name, out):
    sys.path.insert(0, str(ROOT))
    import harness.steer as steer
    from evaluator import check
    from evaluator.coverage import instrumented_lines
    from harness.trace import validate_trace
    _, flags, trace, bypass, _ = CASES[name]
    if bypass:
        refuse = steer.alloc_refusal
        steer.alloc_refusal = lambda t, label, value: None if t['id'] == CKV['id'] else refuse(t, label, value)
    config = check.load_kcov_config()
    decisions = check.load_decisions(config)
    instrumented, functions = instrumented_lines(check.KERNEL / 'vmlinux', config['functions'], config['files'])
    kcov = (config, decisions, check.witness_table(decisions, instrumented, functions,
                                                   config['branch_free_functions']), instrumented, functions)
    results, _, _ = check.run_chunk([validate_trace(trace)], out, kcov, alloc_flags=flags)
    result = results[trace['id']]
    (out / 'result.json').write_text(json.dumps(result, indent=1) + '\n')
    print(json.dumps(result)[:3000])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--kernel', required=True)
    ap.add_argument('--control-kernel', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--case', help=argparse.SUPPRESS)
    ap.add_argument('--only', help='comma-separated cases')
    args = ap.parse_args()
    out = Path(args.out).resolve()
    if args.case:
        run_case(args.case, out / args.case)
        return 0
    summary = {}
    for name in (args.only.split(',') if args.only else CASES):
        kernel_opt, _, trace, _, what = CASES[name]
        kernel = Path(getattr(args, kernel_opt)).resolve()
        env = dict(os.environ, LEANUX_KERNEL_DIR=str(kernel))
        proc = subprocess.run([sys.executable, __file__, '--kernel', args.kernel, '--control-kernel',
                               args.control_kernel, '--out', str(out), '--case', name], env=env, cwd=ROOT)
        path = out / name / 'result.json'
        result = json.loads(path.read_text()) if path.exists() else dict(outcome='no_result', exit=proc.returncode)
        kinds = sorted({p['problem'] for p in result.get('problems', [])})
        detail = result.get('detail', '')
        if name == 'C-kv':
            ok = result['outcome'] == 'unsupported_path' and 'kvmalloc vmalloc fallback' in detail
        else:
            ok = result['outcome'] not in ('agreement', 'no_result') and result.get('side') != 'linux'
        summary[name] = dict(expected=what, kernel=str(kernel), outcome=result['outcome'], problems=kinds,
                             detail=detail[-400:], rejected_as_expected=ok)
    (out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps(summary, indent=1))
    ok = all(s['rejected_as_expected'] for s in summary.values())
    print('PASS' if ok else 'FAIL', f"({sum(s['rejected_as_expected'] for s in summary.values())}/{len(summary)})")
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
