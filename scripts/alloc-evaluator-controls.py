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
- C-kv (oracle): the 8 KiB `kvmalloc` of the fd array (an
  `rlimit_nofile = 1024` trace whose `dup3` expands the table to 1024
  slots). Its slab attempt carries __GFP_NORETRY and can fail, after which
  `vmalloc` succeeds; the mirror must then answer `unsupported "kvmalloc
  vmalloc fallback"`, never -ENOMEM. Neither a natural failure nor a forced
  one can be produced on this base: no memory-pressure fixture exists, the
  control kernel has no such flag, and the guest steers network traces only
  (the schedule rides the remote KCOV instance). So the control has two
  parts: (a) Linux, armed with the kvmalloc helper range and not steered,
  runs the trace and the whole check must agree, which shows that the
  record resolves to `kvmallocFdArray` and is consumed (the natural success);
  (b) the mirror alone, given (a)'s records with that record's outcome byte
  set to 0 (what a natural failure records), must stop with the
  `unsupported` answer.
- C-kv-forced (oracle, A2): since A2 the guest steers FS traces on their own
  KCOV instance, so the 8 KiB slab attempt can be failed on Linux. The host
  refuses such an entry (harness/steer.py, the kvmalloc limit); this control
  lifts the refusal in its own process only. Linux must go on to `vmalloc`
  and succeed (the dup3 returns its fd), recording a steered fail at
  `kvmallocFdArray`, and the mirror must stop with `unsupported "kvmalloc
  vmalloc fallback"` rather than take the -ENOMEM arm.
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
sys.path.insert(0, str(ROOT))
from harness.linux import approved_kernel_identity  # noqa: E402
CONTROL_IDENTITY_FILE = ROOT / 'kernel/identity-x86_64-net-choice-actl.txt'
FAIL = '00' * 8
CTL = {'record_ok': 2, 'nofail': 4, 'addr_naming': 8}
CKV = {"version": 1, "id": "ac_kvmalloc_fallback", "rlimit_nofile": 1024,
       "ops": [{"op": "eventfd2", "init": 0, "flags": 0},
               {"op": "dup3", "fd": {"ref": 0}, "newfd": {"literal": 1000}, "flags": 0},
               {"op": "write", "fd": {"literal": 1000}, "count": 8, "value": "1"}]}


def corpus(name):
    return json.loads((ROOT / 'corpus/alloc' / f'{name}.json').read_text())


# case: (kernel option, load flags, trace, sites armed unsteered, what must hold)
CASES = {
    'K1': ('control_kernel', CTL['record_ok'], corpus('a_sendbuf_init_nomem'), (),
           'a forced failure recorded as ok: the records disagree with Linux'),
    'K4': ('control_kernel', CTL['nofail'], corpus('a_sendbuf_init_nomem'), (),
           'a __GFP_NOFAIL encounter is never failed: the schedule is left over'),
    'K5': ('control_kernel', CTL['addr_naming'], corpus('a_sendbuf_init_nomem'), (),
           'naming by address only: the helper site is never steered, the schedule left over'),
    'C-kv': ('kernel', 0, CKV, ('kvmallocFdArray',),
             '(a) armed, the natural success agrees; (b) a fail record: unsupported "kvmalloc vmalloc fallback"'),
    'C-kv-forced': ('kernel', 0, dict(CKV, id='ac_kvmalloc_forced', steer=[['kvmallocFdArray', FAIL]],
                                     domain_extension='failslab'), (),
                    'a forced 8 KiB slab failure: Linux falls back to vmalloc (dup3 succeeds); the mirror answers '
                    'unsupported "kvmalloc vmalloc fallback"'),
}


def run_case(name, out):
    sys.path.insert(0, str(ROOT))
    import harness.steer as steer
    from evaluator import check
    from evaluator.coverage import instrumented_lines
    from harness.trace import validate_trace
    _, flags, trace, arm, _ = CASES[name]
    if name == 'C-kv-forced':   # lift the host's 8 KiB refusal, in this process only
        steer.ALLOC_SITES['kvmallocFdArray'].pop('kvmalloc_limit')
    config = check.load_kcov_config()
    decisions = check.load_decisions(config)
    instrumented, functions, _chains = instrumented_lines(check.KERNEL / 'vmlinux', config['functions'], config['files'])
    kcov = (config, decisions, check.witness_table(decisions, instrumented, functions,
                                                   config['branch_free_functions']), instrumented, functions)
    results, _, _ = check.run_chunk([validate_trace(trace)], out, kcov, alloc_flags=flags, arm=arm)
    result = results[trace['id']]
    if name == 'C-kv':
        result = dict(armed_run=result)
        # (b): the armed run's records, the fd array's outcome byte set to 0
        inputs = [json.loads(line) for line in (out / 'model/inputs.jsonl').read_text().splitlines()]
        site = next(e['id'] for e in check.load_hidden_sites().values() if e['label'] == 'kvmallocFdArray')
        found = [(i, k) for i, op in enumerate(inputs[0]['hidden']) for k, r in enumerate(op) if r[0] == site]
        result['fd_array_records'] = [inputs[0]['hidden'][i][k] for i, k in found]
        result['alloc_armed'] = inputs[0].get('alloc_armed')
        if len(found) == 1:
            i, k = found[0]
            rec = inputs[0]['hidden'][i][k]
            inputs[0]['hidden'][i][k] = [rec[0], '00' + rec[1][2:]]
            proc = subprocess.run([str(check.MODEL)], input=(json.dumps(inputs[0]) + '\n').encode(),
                                  capture_output=True, timeout=120)
            result['fail_record'] = dict(exit=proc.returncode, stderr=proc.stderr.decode()[-500:])
    if name == 'C-kv-forced':
        linux = [json.loads(line) for line in (out / 'linux/observations.jsonl').read_text().splitlines()]
        steering = [json.loads(line) for line in (out / 'linux/steering.jsonl').read_text().splitlines()]
        records = [r for row in (json.loads(line) for line in (out / 'linux/hidden.jsonl').read_text().splitlines())
                   if row['mode'] == 'pc' for r in row['records'] if r[0] & 0x7fff == steer.ALLOC_KIND]
        result = dict(check=result, linux_rets=[o['ret'] for o in linux[0]['observations']], steering=steering,
                      steered_alloc_records=sum(1 for r in records if r[0] & 0x8000))
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
    if args.only and (out / 'summary.json').exists():   # merge with the earlier cases' results
        summary = json.loads((out / 'summary.json').read_text())
    for name in (args.only.split(',') if args.only else CASES):
        kernel_opt, _, trace, _, what = CASES[name]
        kernel = Path(getattr(args, kernel_opt)).resolve()
        env = dict(os.environ, LEANUX_KERNEL_DIR=str(kernel))
        # The identity check (harness/linux.py verify_kernel): the oracle is
        # checked against kernel/identity-x86_64-net-choice.txt; the control
        # kernel, never an oracle, is named explicitly for its cases.
        env.pop('LEANUX_KERNEL_IDENTITY', None)
        if kernel_opt == 'control_kernel':
            env['LEANUX_KERNEL_IDENTITY'] = approved_kernel_identity(CONTROL_IDENTITY_FILE)
        proc = subprocess.run([sys.executable, __file__, '--kernel', args.kernel, '--control-kernel',
                               args.control_kernel, '--out', str(out), '--case', name], env=env, cwd=ROOT)
        path = out / name / 'result.json'
        result = json.loads(path.read_text()) if path.exists() else dict(outcome='no_result', exit=proc.returncode)
        kinds = sorted({p['problem'] for p in result.get('problems', [])})
        detail = result.get('detail', '')
        if name == 'C-kv':
            fr = result.get('fail_record', {})
            ok = result.get('armed_run', {}).get('outcome') == 'agreement' and fr.get('exit') == 3 \
                and 'kvmalloc vmalloc fallback' in fr.get('stderr', '') \
                and result.get('alloc_armed') == ['kvmallocFdArray', 'kvmallocFdBitmaps']
            result['outcome'] = 'see armed_run and fail_record'
            detail = json.dumps(dict(armed=result.get('armed_run', {}).get('outcome'), fail_record=fr))
        elif name == 'C-kv-forced':
            chk = result.get('check', {})
            steering = result.get('steering', [])
            ok = result.get('linux_rets', [None, None])[1] == 1000 and result.get('steered_alloc_records') == 1 \
                and len(steering) == 2 and all(r['remaining'] == 0 and r['mismatches'] == 0 for r in steering) \
                and chk.get('outcome') != 'agreement' and 'kvmalloc vmalloc fallback' in json.dumps(chk)
            result['outcome'] = chk.get('outcome', 'no_result')
            detail = json.dumps(chk)
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
