"""The pipes sentinel mutants (AGENTS.md, "Gates and speedbumps"): one hidden
record ignored, one decision outcome a KCOV witness catches. Each is applied
to a clean committed tree, verified as applied, checked on the `pipes` suite
(corpus/pipes), then reverted. Run from the repository root at a claim point:

    scripts/in-bundle python3 scripts/pipes-mutants.py [NAME ...]

Every sentinel must be rejected: its run must find something the unmutated
baseline run (made first, on the same suite) does not. With a passing
baseline that is simply a failing run; the baseline rule keeps the mutants
informative should an open, known failure be in the tree (at integration the
baseline passes). The stage-1 catalogue this set was chosen from (18 entries,
docs/2026-10-05-p-pipes.md section 8) is in git history before the 2026-10-12
rewrite; a new pipes instrument gets a one-off entry here, run once, then
deleted unless it replaces a sentinel.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PIPE = 'Leanux/FS/Pipe.lean'
SIGNAL = 'Leanux/Kernel/Signal.lean'
INODE = 'Leanux/FS/Inode.lean'

# (name, what it changes and the instrument expected to reject it, file, old, new)
# The two pipes sentinels (AGENTS.md, "Gates and speedbumps"): a hidden record
# ignored, and a decision outcome KCOV witnesses (control flow). The stage-1
# catalogue (18 entries) is in git history before the 2026-10-12 rewrite.
MUTANTS = [
  ('P-M12-noatime-ignored', 'touch_atime despite O_NOATIME: hidden (no record left) on p_noatime', INODE,
   "  if ← branchCmp .fileAccessedNotNoatime (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0 then\n",
   "  if (← branchCmp .fileAccessedNotNoatime (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0) || true then\n"),
  ('P-M7-tmp-page-ignored', 'always alloc_page: A2 (:512-518 witnesses)', PIPE,
   "      let mut page := p.tmpPage\n",
   "      let mut page : Option PageId := none\n"),
]
PENDING = {m[0] for m in MUTANTS if m[3] is None}


def mutate(name, text, old, new):
    """Apply one mutant's replacements (a pattern, or a list of patterns),
    each of which must occur exactly once."""
    olds, news = (old, new) if isinstance(old, list) else ([old], [new])
    for o, n in zip(olds, news, strict=True):
        assert text.count(o) == 1, f'{name}: pattern not unique/present: {o!r}'
        text = text.replace(o, n)
    return text


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def check(out):
    """Run the pipes suite into `out`; the report, or None with the stderr tail."""
    run(['rm', '-rf', out])
    proc = run(['timeout', '3000', sys.executable, '-m', 'evaluator.check', '--suite', 'pipes', '--out', out],
               capture_output=True, text=True)
    path = os.path.join(ROOT, out, 'report.json')
    return (json.load(open(path)) if os.path.exists(path) else None), proc


def signatures(report):
    """What a run found, per trace: its outcome and each problem (operation,
    decision label, kind). A mutant is rejected when its run has a signature
    the unmutated baseline does not (with a passing baseline: when it fails)."""
    found = set()
    for f in report['failures']:
        # a chunk-level failure (the Linux run, the mirror run) carries no id
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
    # The baseline: the unmutated tree on the same suite. Its known failures
    # (if any) do not count as rejections.
    baseline, proc = check('.artifacts/check/mutant-baseline')
    if baseline is None:
        raise SystemExit(f'baseline run produced no report: {proc.stderr[-2000:]}')
    base = signatures(baseline)
    results = {'baseline': dict(base=head, status=baseline['status'], counts=baseline['counts'],
                                known=sorted(map(str, base))[:50])}
    print('baseline', baseline['status'], baseline['counts'], len(base), 'signatures', flush=True)
    for name, what, path, old, new in MUTANTS:
        if name not in selected:
            continue
        if name in PENDING:
            results[name] = dict(description=what, base=head, file=path, status='pending')
            print(name, 'pending (no pattern yet)', flush=True)
            continue
        full = os.path.join(ROOT, path)
        mutated = mutate(name, open(full).read(), old, new)   # before opening for writing
        open(full, 'w').write(mutated)
        try:
            diff = run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout
            assert path in diff, f'{name}: mutation not applied'
            out = f'.artifacts/check/mutant-{name}'
            report, proc = check(out)
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
    json.dump(results, open(os.path.join(ROOT, '.artifacts/check/pipes-mutants-summary.json'), 'w'), indent=2)


if __name__ == '__main__':
    main()
