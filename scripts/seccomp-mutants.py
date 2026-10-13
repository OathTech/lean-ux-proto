"""The seccomp sentinel and the kind-309 one-off (docs/2026-10-12-seccomp-design.md
sections 7 and 8; AGENTS.md "Gates and speedbumps"). Each is applied to a clean
committed tree, verified as applied, checked on the smallest subset of the
`seccomp` suite that rejects it, then reverted. Run from the repository root at
a claim point:

    scripts/in-bundle python3 scripts/seccomp-mutants.py [NAME ...]

The sentinel, `cache-forgets-prev`, replaces bitmap_copy by bitmap_fill in the
mirror's seccomp_cache_prepare, so a newer filter that is constant-allow for a
number hides an older filter's kill; s_chain_older_kills_child catches it as a
data mismatch (ALLOW against SIGSYS) and a control-flow mismatch (the cache-hit
arm against the loop). The kind-309 instrument's one-off,
`S-M2-jt-zero-jle` (the `jt == 0` arm of the classic-to-eBPF conversion
emitting JLE for JGE, net/core/filter.c:761-779), ran once on the sc2 scratch
kernel on 2026-10-13 and was rejected through the hidden-mismatch channel on
s_lang_jumps_k (JGE|K 10 with jt 0); it is deleted, as the rule for a new
instrument says. The sentinel runs on the one trace that rejects it (the
baseline on the same trace, so a known failure there does not count); a
pattern of None is pending and reported, not run.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILTER = 'Leanux/Seccomp/Filter.lean'
TRANSLATE = 'Leanux/Seccomp/Translate.lean'

# (name, what it changes and the instrument expected to reject it, file, old, new, the trace or None for the suite)
MUTANTS = [
  ('S-M1-cache-forgets-prev', 'seccompCachePrepare starts from all-ones instead of the previous bitmap: '
   'data (ALLOW against SIGSYS) and control flow (cache hit against the loop) on s_chain_older_kills_child',
   FILTER,
   "    if ← kbranch .cachePrepareHasPrev prev.isSome then pure prev.get!   -- bitmap_copy\n",
   "    if ← kbranch .cachePrepareHasPrev prev.isSome then pure (BitVec.allOnes NR_syscalls)   -- bitmap_copy\n",
   's_chain_older_kills_child'),
]
PENDING = {m[0] for m in MUTANTS if m[3] is None}


def mutate(name, text, old, new):
    olds, news = (old, new) if isinstance(old, list) else ([old], [new])
    for o, n in zip(olds, news, strict=True):
        assert text.count(o) == 1, f'{name}: pattern not unique/present: {o!r}'
        text = text.replace(o, n)
    return text


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def check(out, trace=None):
    """Run the seccomp suite (or one trace of it) into `out`; the report, or
    None with the stderr tail."""
    run(['rm', '-rf', out])
    cmd = ['timeout', '3000', sys.executable, '-m', 'evaluator.check', '--suite', 'seccomp', '--out', out]
    if trace:
        cmd += ['--trace', trace]
    proc = run(cmd, capture_output=True, text=True)
    path = os.path.join(ROOT, out, 'report.json')
    return (json.load(open(path)) if os.path.exists(path) else None), proc


def signatures(report):
    found = set()
    for f in report['failures']:
        trace = f.get('id', '?')
        found.add((trace, 'outcome', f['outcome']))
        for p in f.get('problems', []):
            found.add((trace, p.get('index'), p.get('label'), p['problem']))
    if report['aborted']:
        found.add(('*', 'aborted', report['aborted'][:200]))
    return found


def main():
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
    head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    names = [m[0] for m in MUTANTS]
    selected = sys.argv[1:] or names
    unknown = sorted(set(selected) - set(names))
    if unknown:
        raise SystemExit(f'unknown mutants: {unknown}')
    results = {}
    baselines = {}
    for name, what, path, old, new, trace in MUTANTS:
        if name not in selected:
            continue
        if name in PENDING:
            results[name] = dict(description=what, base=head, file=path, status='pending')
            print(name, 'pending (no pattern yet)', flush=True)
            continue
        if trace not in baselines:   # the unmutated tree on the same subset; its known failures do not count
            baseline, proc = check(f'.artifacts/check/seccomp-baseline-{trace or "suite"}', trace)
            if baseline is None:
                raise SystemExit(f'baseline run produced no report: {proc.stderr[-2000:]}')
            baselines[trace] = signatures(baseline)
            print('baseline', trace or 'suite', baseline['status'], baseline['counts'], flush=True)
        base = baselines[trace]
        full = os.path.join(ROOT, path)
        mutated = mutate(name, open(full).read(), old, new)
        open(full, 'w').write(mutated)
        try:
            assert path in run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout, f'{name}: not applied'
            out = f'.artifacts/check/mutant-{name}'
            report, proc = check(out, trace)
            if report is None:
                results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status='error',
                                     stderr=proc.stderr[-2000:])
                print(name, 'error (no report)', proc.stderr[-400:], flush=True)
                continue
            new_found = sorted(map(str, signatures(report) - base))
            kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                           {f['outcome'] for f in report['failures']})
            results[name] = dict(description=what, base=head, file=path, exit=proc.returncode,
                                 status='rejected' if new_found else 'survived', check_status=report['status'],
                                 counts=report['counts'], failure_kinds=kinds, aborted=report['aborted'],
                                 beyond_baseline=new_found[:20], report=out + '/report.json')
            print(name, results[name]['status'], report['counts'], new_found[:6], flush=True)
        finally:
            run(['git', 'checkout', '--', path])
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
    os.makedirs(os.path.join(ROOT, '.artifacts/check'), exist_ok=True)
    json.dump(results, open(os.path.join(ROOT, '.artifacts/check/seccomp-mutants-summary.json'), 'w'), indent=2)


if __name__ == '__main__':
    main()
