#!/usr/bin/env python3
"""Mechanical mutants of the mirror against the differential check: the
mutation campaign (docs/2026-10-13-mutation-campaign.md). Every mutant is one
edit at one line of one mirror file, enumerated deterministically from the
committed tree, applied to a detached scratch worktree, built and checked on
the corpus subset that reaches that file, and recorded with its verdict
channel. A survivor (the check agrees with a wrong mirror) is a finding on
the check's reach; an uncompilable mutant counts separately. The sentinel
scripts (`scripts/wg-mutants.py`, `pipes-mutants.py`, `seccomp-mutants.py`)
stay the claim-point speedbump; this tool measures the check's sensitivity
across the whole mirror once.

    scripts/in-bundle python3 scripts/mutate.py --list [--cap N] [--class C ...] [--file F ...]
    scripts/in-bundle python3 scripts/mutate.py --show ID
    scripts/in-bundle python3 scripts/mutate.py --apply ID --into WORKTREE
    scripts/in-bundle python3 scripts/mutate.py --run [--cap N] [--class C ...] [--file F ...]
                                                [--ids ID ...] [--workers K] [--results FILE]
                                                [--confirm-survivors]

Classes (one edit each; `old` and `new` are whole lines):
  decision-negated      a recorded decision's outcome negated (`branch`/`branchCmp`), the arms swapped
  condition-negated     a plain `if` condition (no decision) negated
  comparison-operator   `≥`↔`>`, `≤`↔`<`, `==`↔`!=` at a comparison
  constant-off-by-one   a numeric constant (a `def` constant or a literal in a condition) plus one
  early-return-removed  `then return ...` becomes `then pure ()`: the early arm falls through
  operand-swapped       a `branchCmp`'s two recorded operands exchanged, outcome kept
  record-skipped        a hidden-input consumption replaced by a constant (`hidden`, `hiddenAlloc`)
  stop-passthrough      `then unsupported "..."` / `then invariant "..."` becomes `then pure ()`
  order-swapped         two adjacent early-return decisions exchanged (the sentinel B1-M5's shape)

Determinism: the enumeration depends only on the tree; ids are a hash of
(file, line, class, old line). `--cap N` keeps at most N per (file, class),
evenly spaced by line. The subset a mutant runs on is the file's area suite
and corpus prefixes (SUBSETS); with `--confirm-survivors`, a survivor is
rerun on the whole area suite before it counts. Verdicts follow
`scripts/wg-mutants.py`: rejected (only mirror-side outcomes), survived (a
clean pass), no_verdict (infrastructure), uncompilable (the model build
failed).
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MIRROR = ['Leanux/WG', 'Leanux/FS', 'Leanux/Seccomp', 'Leanux/Kernel', 'Leanux/Env', 'Leanux/Env.lean',
          'Leanux/Runner.lean', 'Leanux/Syscalls.lean']
CLASSES = ['decision-negated', 'condition-negated', 'comparison-operator', 'constant-off-by-one',
           'early-return-removed', 'operand-swapped', 'record-skipped', 'stop-passthrough', 'order-swapped']

# The corpus subset that reaches a file: (suite, [id prefixes]) per mirror
# path prefix, from the sentinel scripts' subsets and the design docs; '' is
# the whole suite. The whole area suite (AREA) confirms a survivor.
SUBSETS = {
    'Leanux/WG/Handshake.lean': [('wireguard', ['c_', 'b1_'])],
    'Leanux/WG/NoiseCrypto.lean': [('wireguard', ['c_', 'b1_'])],
    'Leanux/WG/Curve25519.lean': [('wireguard', ['c_', 'b1_'])],
    'Leanux/WG/Blake2s.lean': [('wireguard', ['c_', 'b1_'])],
    'Leanux/WG/Send.lean': [('wireguard', ['b1_', 'w4_', 'd3_'])],
    'Leanux/WG/Receive.lean': [('wireguard', ['rx_', 'd2_', 'e_'])],
    'Leanux/WG/RxData.lean': [('wireguard', ['rx_', 'd2_'])],
    'Leanux/WG/Data.lean': [('wireguard', ['d2_', 'w5_'])],
    'Leanux/WG/Peer.lean': [('wireguard', ['s2_', 'wg_', 'l_'])],
    'Leanux/WG/PeerRemove.lean': [('wireguard', ['l_', 'wg_'])],
    'Leanux/WG/Device.lean': [('wireguard', ['wg_', 'w9_', 'l_'])],
    'Leanux/WG/Socket.lean': [('wireguard', ['w9_', 'w8_'])],
    'Leanux/WG/Netlink.lean': [('wireguard', ['n1_', 'wg_'])],
    'Leanux/WG/NetlinkDump.lean': [('wireguard', ['n2_'])],
    'Leanux/WG/AllowedIps.lean': [('wireguard', ['n1_', 'b1_'])],
    'Leanux/WG/Timers.lean': [('wireguard', ['d3_'])],
    'Leanux/WG/Keypair.lean': [('wireguard', ['b1_', 'd3_'])],
    'Leanux/WG/State.lean': [('wireguard', ['b1_', 'rx_', 'wg_'])],
    'Leanux/WG/Types.lean': [('wireguard', ['b1_', 'rx_', 'w7_'])],
    'Leanux/WG/PtrRing.lean': [('wireguard', ['w7_', 'w4_'])],
    'Leanux/WG/PrevQueue.lean': [('wireguard', ['w7_', 'rx_'])],
    'Leanux/Env.lean': [('wireguard', ['d3_', 's2_', 'e_'])],
    'Leanux/Env/Batch.lean': [('wireguard', ['w7_', 'rx_', 'd2_'])],
    'Leanux/FS/Eventpoll.lean': [('epoll', [''])],
    'Leanux/FS/Wait.lean': [('epoll', ['']), ('pipes', [''])],
    'Leanux/FS/Poll.lean': [('epoll', [''])],
    'Leanux/FS/Fput.lean': [('epoll', ['']), ('pipes', [''])],
    'Leanux/FS/': [('pipes', [''])],
    'Leanux/Seccomp/': [('seccomp', [''])],
    'Leanux/Kernel/Signal.lean': [('pipes', ['']), ('seccomp', [''])],
    'Leanux/Kernel/': [('handwritten', ['']), ('wireguard', ['b1_', 'd3_'])],
    'Leanux/Runner.lean': [('handwritten', ['']), ('wireguard', ['b1_'])],
    'Leanux/Syscalls.lean': [('handwritten', ['']), ('wireguard', ['b1_'])],
}
# The allocation records (kind 305) are armed only in the alloc suite's
# traces, so a skipped `hiddenAlloc` is invisible elsewhere: record-skipped
# mutants of the WireGuard and FS files run on `alloc` first.
CLASS_SUBSETS = {'record-skipped': [('alloc', [''])]}
AREA = {'wireguard': 'wireguard', 'pipes': 'pipes', 'epoll': 'epoll', 'seccomp': 'seccomp', 'handwritten': 'handwritten',
        'alloc': 'alloc'}

MISMATCH_OUTCOMES = frozenset({'semantic_mismatch', 'control_flow_mismatch', 'hidden_mismatch',
                               'mirror_invariant', 'unsupported_path'})

# evaluator.check on the traces of the suites whose ids start with one of the prefixes
SUBSET = """import sys
sys.path.insert(0, '.')
import evaluator.check as c
prefixes = [p for p in sys.argv[1].split(',')]
load = c.load_traces
c.load_traces = lambda *a, **k: [t for t in load(*a, **k) if any(t['id'].startswith(p) for p in prefixes)]
sys.exit(c.main(sys.argv[2:]))
"""


# ---------------------------------------------------------------- enumeration

def mirror_files():
    files = []
    for entry in MIRROR:
        p = ROOT / entry
        if p.is_dir():
            files += sorted(p.rglob('*.lean'))
        elif p.exists():
            files.append(p)
    return [f.relative_to(ROOT).as_posix() for f in files]


def balanced(s, start):
    """The index just past the balanced parenthesised group starting at
    s[start] == '(' (None if unbalanced)."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i + 1
    return None


def top_tokens(s):
    """Split on spaces outside parentheses."""
    tokens, depth, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        if ch == ' ' and depth == 0:
            if cur:
                tokens.append(cur)
            cur = ''
        else:
            cur += ch
    if cur:
        tokens.append(cur)
    return tokens


def negate(expr):
    e = expr.strip()
    if e == 'true':
        return 'false'
    if e == 'false':
        return 'true'
    if e.startswith('!') and e[1:].startswith('(') and balanced(e, 1) == len(e):
        return e[2:-1]
    return f'(!({e}))'


def in_string(line, idx):
    return line[:idx].count('"') % 2 == 1


OP_PAIRS = {'≥': '>', '>': '≥', '≤': '<', '<': '≤', '==': '!=', '!=': '=='}
OP_RE = re.compile(r' (≥|>|≤|<|==|!=) ')
DEF_CONST_RE = re.compile(r'^(def [A-Z][A-Z_0-9]* : (?:Nat|UInt64|Int64|Int|UInt32|UInt8) := )(\d+)$')
LITERAL_RE = re.compile(r'(?<![\w.])(\d+)(?![\w.])')


def mutate_line(line):
    """Every mutant of one line: (class, new_line, note)."""
    out = []
    stripped = line.strip()
    if not stripped or stripped.startswith('--') or stripped.startswith('/-') or stripped.startswith('-/') \
            or stripped.startswith('/--'):
        return out
    code = line.split('--')[0].rstrip() if ' --' in line else line.rstrip()

    # decision-negated: `← branch .d EXPR` (to ` then` or end) and `branchCmp .d (COND) a b`
    m = re.search(r'← branch (\.[A-Za-z0-9_]+) ', code)
    if m:
        rest = code[m.end():]
        cut = rest.find(' then')
        expr = rest if cut < 0 else rest[:cut]
        if expr.strip() and 'do' not in expr.split():
            out.append(('decision-negated', code[:m.end()] + negate(expr) + ('' if cut < 0 else rest[cut:]), m.group(1)))
    m = re.search(r'branchCmp(?:Excluded)? (\.[A-Za-z0-9_]+) ', code)
    if m:
        rest = code[m.end():]
        if rest.startswith('('):
            end = balanced(rest, 0)
            if end:
                cond, tail = rest[:end], rest[end:]
                out.append(('decision-negated', code[:m.end()] + negate(cond) + tail, m.group(1)))
                # operand-swapped: the two operands after the condition, before ` then`/end
                if 'Excluded' not in code[m.start():m.end()]:
                    tcut = tail.find(' then')
                    ops = tail if tcut < 0 else tail[:tcut]
                    toks = top_tokens(ops)
                    if len(toks) == 2 and toks[0] != toks[1]:
                        swapped = ' ' + toks[1] + ' ' + toks[0]
                        out.append(('operand-swapped', code[:m.end()] + cond + swapped + ('' if tcut < 0 else tail[tcut:]), m.group(1)))

    # condition-negated: a plain `if COND then` without a decision
    m = re.match(r'^(\s*(?:else )?if )(?!←|let |h :)(.+?)( then\b.*)$', code)
    if m and 'branch' not in code and '←' not in m.group(2):
        out.append(('condition-negated', m.group(1) + negate(m.group(2)) + m.group(3), ''))

    # comparison-operator: at most the first two operators of a condition line
    if ('if ' in code or 'branchCmp' in code) and '"' not in code:
        for i, om in enumerate(OP_RE.finditer(code)):
            if i >= 2:
                break
            op = om.group(1)
            new = code[:om.start()] + ' ' + OP_PAIRS[op] + ' ' + code[om.end():]
            out.append(('comparison-operator', new, f'{op}→{OP_PAIRS[op]}'))

    # constant-off-by-one: a def constant, or a literal in a condition line
    dm = DEF_CONST_RE.match(code)
    if dm:
        out.append(('constant-off-by-one', dm.group(1) + str(int(dm.group(2)) + 1), dm.group(1).split()[1]))
    elif ('if ' in code or 'branchCmp' in code) and '"' not in code and 'import' not in code:
        seen = 0
        for lm in LITERAL_RE.finditer(code):
            if in_string(code, lm.start()):
                continue
            # skip decision-name-like contexts and the `[0:n]` loop bounds
            if code[max(0, lm.start() - 1)] in '.[:':
                continue
            seen += 1
            if seen > 2:
                break
            new = code[:lm.start()] + str(int(lm.group(1)) + 1) + code[lm.end():]
            out.append(('constant-off-by-one', new, lm.group(1)))

    # early-return-removed: `then return ...` with no else on the line
    m = re.search(r'\bthen return\b(.*)$', code)
    if m and ' else ' not in code and not code.rstrip().endswith('do'):
        out.append(('early-return-removed', code[:m.start()] + 'then pure ()', ''))

    # record-skipped
    m = re.search(r'← hiddenAlloc (\.[A-Za-z0-9_]+)', code)
    if m:
        out.append(('record-skipped', code[:m.start()] + '← (pure true : M Bool)' + code[m.end():], m.group(1)))
    m = re.search(r'← hidden (\.[A-Za-z0-9_]+)', code)
    if m:
        site = 'HiddenSite' + m.group(1)
        out.append(('record-skipped',
                    code[:m.start()] + f'← (pure (List.replicate ({site}).info.len 0) : M (List UInt8))' + code[m.end():],
                    m.group(1)))

    # stop-passthrough: `then unsupported "..."` / `then invariant "..."` at line end, no else
    m = re.search(r'\bthen (unsupported|invariant) (s!)?"[^"]*"\s*$', code)
    if m and ' else ' not in code:
        out.append(('stop-passthrough', code[:m.start()] + 'then pure ()', m.group(1)))
    return out


def enumerate_mutants(files=None, classes=None, cap=None):
    """All mutants of the committed tree (the working tree must be clean for
    the ids to mean anything), optionally capped per (file, class)."""
    mutants = []
    for path in mirror_files():
        if files and not any(path.startswith(f) or path == f for f in files):
            continue
        lines = (ROOT / path).read_text().split('\n')
        in_doc = False
        per_class = {}
        for n, line in enumerate(lines, 1):
            s = line.strip()
            if in_doc:
                if '-/' in s:
                    in_doc = False
                continue
            if s.startswith('/-') and '-/' not in s:
                in_doc = True
                continue
            for cls, new, note in mutate_line(line):
                if classes and cls not in classes:
                    continue
                if new == line.rstrip():
                    continue
                digest = hashlib.sha1(f'{path}:{n}:{cls}:{line}'.encode()).hexdigest()[:10]
                # several mutants of one class at one line (two literals, two
                # operators) share the digest: the first keeps it, the rest
                # carry an ordinal, so earlier results keep their ids
                seen = sum(1 for m in per_class.get(cls, []) if m['id'].startswith(f'm-{digest}'))
                ident = f'm-{digest}' if seen == 0 else f'm-{digest}-{seen}'
                per_class.setdefault(cls, []).append(dict(id=ident, file=path, line=n, cls=cls,
                                                          old=line, new=new, note=note))
        if not classes or 'order-swapped' in classes:
            pat = re.compile(r'^(\s*)if ← branch(?:Cmp)? \.[A-Za-z0-9_]+ .* then return\b')
            for n in range(1, len(lines)):
                a, b = lines[n - 1], lines[n]
                ma, mb = pat.match(a), pat.match(b)
                if ma and mb and ma.group(1) == mb.group(1) and a != b:
                    digest = hashlib.sha1(f'{path}:{n}:order-swapped:{a}'.encode()).hexdigest()[:10]
                    per_class.setdefault('order-swapped', []).append(dict(
                        id=f'm-{digest}', file=path, line=n, cls='order-swapped', old=a + '\n' + b, new=b + '\n' + a,
                        note='two adjacent decisions exchanged'))
        for cls, ms in per_class.items():
            if cap and len(ms) > cap:
                step = len(ms) / cap
                ms = [ms[int(i * step)] for i in range(cap)]
            mutants += ms
    mutants.sort(key=lambda m: (m['file'], m['line'], m['cls']))
    return mutants


def subsets_for(path, cls=None):
    extra = CLASS_SUBSETS.get(cls, []) if path.startswith(('Leanux/WG/', 'Leanux/FS/')) else []
    for prefix, subs in SUBSETS.items():
        if path == prefix or path.startswith(prefix):
            return extra + subs
    return extra + [('handwritten', [''])]


# ---------------------------------------------------------------- running

def apply_mutant(m, tree):
    full = Path(tree) / m['file']
    lines = full.read_text().split('\n')
    span = m['old'].count('\n') + 1
    if '\n'.join(lines[m['line'] - 1:m['line'] - 1 + span]) != m['old']:
        raise RuntimeError(f"{m['id']}: line {m['line']} of {m['file']} is not the enumerated line")
    lines[m['line'] - 1:m['line'] - 1 + span] = m['new'].split('\n')
    full.write_text('\n'.join(lines))


def classify(report):
    if report is None:
        return 'no_verdict', [], ['no report']
    outcomes = {f['outcome'] for f in report['failures']}
    mismatches, other = sorted(outcomes & MISMATCH_OUTCOMES), sorted(outcomes - MISMATCH_OUTCOMES)
    if report.get('aborted'):
        # The check aborts when corpus traces fall out of the mirror's domain
        # before Linux runs: the mutated mirror stopped (unsupported or an
        # invariant) on every one of them in the domain filter. That is the
        # mirror's own verdict, named in the abort message; any other abort
        # is the infrastructure's.
        reason = str(report['aborted'])
        if 'wrong side of the domain filter' in reason or 'mirror invariant violated' in reason \
                or 'domain filter failed' in reason:
            return 'rejected', ['domain_filter'], []
        if 'model build failed' in reason:
            return 'uncompilable', [], ['build failed']
        if 'duplicate label or unanchored file' in reason:
            return 'invalid', [], ['the decision table broken']
        return 'no_verdict', mismatches, other + ['aborted']
    if outcomes and outcomes <= {'invalid_output'}:
        # the mutated mirror's output no longer parses: the runner's output
        # format was mutated, not the C's control flow
        return 'invalid', [], ['invalid_output']
    if mismatches and not other:
        return 'rejected', mismatches, other
    if mismatches:
        return 'no_verdict', mismatches, other
    if report['status'] == 'pass' and not report['failures']:
        return 'survived', [], []
    return 'no_verdict', [], other or ['fail without failures']


def run_check(tree, suite, prefixes, out, timeout):
    """One check in `tree` on the suite subset; (report or None, stderr tail, uncompilable)."""
    # The scratch tree's own bundle wrapper, with this tree's workspace
    # variables dropped so the wrapper derives the scratch tree's (the check
    # requires --out inside its own artifacts root).
    cmd = [str(Path(tree) / 'scripts' / 'in-bundle'), 'python3']
    if prefixes and prefixes != ['']:
        cmd += ['-c', SUBSET, ','.join(prefixes)]
    else:
        cmd += ['-m', 'evaluator.check']
    cmd += ['--suite', suite, '--out', out]
    env = {k: v for k, v in os.environ.items() if k not in ('LEANUX_ROOT', 'LEANUX_ARTIFACTS', 'LEANUX_CACHE_ROOT')}
    shutil.rmtree(Path(tree) / out, ignore_errors=True)
    proc = subprocess.run(['timeout', str(timeout), *cmd], cwd=tree, env=env, capture_output=True, text=True)
    report_path = Path(tree) / out / 'report.json'
    report = json.load(open(report_path)) if report_path.exists() else None
    build_log = Path(tree) / out / 'build.log'
    uncompilable = report is None and build_log.exists() and b'error:' in build_log.read_bytes()
    return report, proc.stderr[-1500:], uncompilable


def first_problem(report):
    for f in report.get('failures', []):
        for p in f.get('problems', []):
            return f"{f.get('trace')}: {p.get('problem')}: {p.get('detail', '')}"[:300]
        return f"{f.get('trace')}: {f.get('outcome')}: {f.get('detail', '')}"[:300]
    return ''


def scratch_tree(k, base):
    """A detached scratch worktree at HEAD with the build copied in."""
    path = ROOT.parent / f'mutation-scratch-{k}'
    if not path.exists():
        subprocess.run(['git', 'worktree', 'add', '--detach', str(path), 'HEAD'], cwd=ROOT, check=True,
                       capture_output=True)
        shutil.copytree(base / '.lake', path / '.lake', symlinks=True)
    return path


def clean_tree(tree):
    subprocess.run(['git', 'checkout', '--', '.'], cwd=tree, check=True, capture_output=True)
    dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=tree,
                           capture_output=True, text=True).stdout
    if dirty:
        raise RuntimeError(f'scratch tree {tree} is dirty: {dirty}')


ONLY_SUITE = None   # --only-suite: every mutant runs on this whole suite instead of its subsets


def run_one(m, tree, timeout, confirm):
    t0 = time.time()
    clean_tree(tree)
    apply_mutant(m, tree)
    result = dict(m, status=None, runs=[])
    try:
        for suite, prefixes in ([(ONLY_SUITE, [''])] if ONLY_SUITE else subsets_for(m['file'], m['cls'])):
            out = f".artifacts/check/mut-{m['id']}-{suite}"
            report, err, uncompilable = run_check(tree, suite, prefixes, out, timeout)
            status, mism, other = classify(report)
            if uncompilable:
                status = 'uncompilable'
            run = dict(suite=suite, prefixes=prefixes, status=status, mismatches=mism, other=other,
                       counts=report['counts'] if report else None,
                       problem=first_problem(report) if report else err[-300:])
            result['runs'].append(run)
            if status != 'survived':
                shutil.rmtree(Path(tree) / out, ignore_errors=True) if status == 'rejected' else None
                break
            if confirm and prefixes != ['']:
                out2 = f".artifacts/check/mut-{m['id']}-{suite}-full"
                report2, err2, unc2 = run_check(tree, AREA[suite], [''], out2, timeout * 2)
                status2, mism2, other2 = classify(report2)
                result['runs'].append(dict(suite=AREA[suite], prefixes=[''], status=status2, mismatches=mism2,
                                           other=other2, counts=report2['counts'] if report2 else None,
                                           problem=first_problem(report2) if report2 else err2[-300:]))
                if status2 != 'survived':
                    break
    finally:
        clean_tree(tree)
    statuses = [r['status'] for r in result['runs']]
    if 'uncompilable' in statuses:
        result['status'] = 'uncompilable'
    elif 'rejected' in statuses:
        result['status'] = 'rejected'
    elif statuses and all(s == 'survived' for s in statuses):
        result['status'] = 'survived'
    else:
        result['status'] = 'no_verdict'
    last = result['runs'][-1] if result['runs'] else {}
    result['channel'] = ','.join(last.get('mismatches', [])) or ','.join(last.get('other', []))
    result['problem'] = last.get('problem', '')
    result['seconds'] = round(time.time() - t0)
    return result


def run_campaign(mutants, workers, results_path, timeout, confirm, offset=0):
    done = set()
    if results_path.exists():
        for line in results_path.read_text().splitlines():
            if line.strip():
                done.add(json.loads(line)['id'])
    todo = [m for m in mutants if m['id'] not in done]
    print(f'{len(todo)} to run ({len(done)} already in {results_path}), {workers} workers', flush=True)
    lock = threading.Lock()
    queue = list(todo)

    def worker(k):
        tree = scratch_tree(k + offset, ROOT)
        while True:
            with lock:
                if not queue:
                    return
                m = queue.pop(0)
            try:
                r = run_one(m, tree, timeout, confirm)
            except Exception as exc:   # a scratch-tree problem is reported, never silently skipped
                r = dict(m, status='no_verdict', channel='tool', problem=str(exc)[:300], runs=[], seconds=0)
            with lock:
                with open(results_path, 'a') as fh:
                    fh.write(json.dumps(r) + '\n')
                print(f"{r['id']} {r['file']}:{r['line']} {r['cls']} {r['status']} {r['channel']} {r['seconds']}s", flush=True)

    threads = [threading.Thread(target=worker, args=(k,)) for k in range(workers)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()


def reclassify(results_path, workers):
    """Recompute every non-rejected row's status from its kept report (the
    classification may have been refined after the run); the abort reason
    becomes the row's problem."""
    rows = [json.loads(l) for l in results_path.read_text().splitlines() if l.strip()]
    changed = 0
    for r in rows:
        if r['status'] == 'rejected' or not r['runs']:
            continue
        last = r['runs'][-1]
        for k in range(workers):
            suite = last['suite']
            tag = '-full' if last['prefixes'] == [''] and len(r['runs']) > 1 and r['runs'][-2]['suite'] != suite else ''
            p = ROOT.parent / f'mutation-scratch-{k}' / '.artifacts' / 'check' / f"mut-{r['id']}-{suite}{tag}" / 'report.json'
            if not p.exists():
                p = ROOT.parent / f'mutation-scratch-{k}' / '.artifacts' / 'check' / f"mut-{r['id']}-{suite}" / 'report.json'
            if p.exists():
                report = json.load(open(p))
                status, mism, other = classify(report)
                if report.get('aborted'):
                    r['problem'] = str(report['aborted'])[:300]
                if status != r['status']:
                    r['status'], r['channel'] = status, ','.join(mism) or ','.join(other)
                    changed += 1
                break
    results_path.write_text(''.join(json.dumps(r) + '\n' for r in rows))
    return changed


def summarise(results_path):
    rows = [json.loads(l) for l in results_path.read_text().splitlines() if l.strip()]
    by = {}
    for r in rows:
        key = (r['file'], r['cls'])
        d = by.setdefault(key, dict(generated=0, uncompilable=0, invalid=0, rejected=0, survived=0, no_verdict=0, channels={}))
        d['generated'] += 1
        d[r['status']] += 1
        if r['status'] == 'rejected':
            d['channels'][r['channel']] = d['channels'].get(r['channel'], 0) + 1
    return rows, by


def render_report(results_path):
    """The campaign's tables in Markdown: by file and class, the channels'
    shares, every survivor with its diff, every uncompilable with its line."""
    rows, by = summarise(results_path)
    lines = []
    total = dict(generated=0, uncompilable=0, invalid=0, rejected=0, survived=0, no_verdict=0)
    lines.append('| File | Class | Generated | Uncompilable | Invalid | Rejected | Survived | No verdict |')
    lines.append('| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |')
    for (f, c), d in sorted(by.items()):
        lines.append(f"| `{f.split('/', 1)[1]}` | {c} | {d['generated']} | {d['uncompilable']} | {d['invalid']} | "
                     f"{d['rejected']} | {d['survived']} | {d['no_verdict']} |")
        for k in total:
            total[k] += d[k]
    lines.append(f"| **all** | | **{total['generated']}** | **{total['uncompilable']}** | **{total['invalid']}** | "
                 f"**{total['rejected']}** | **{total['survived']}** | **{total['no_verdict']}** |")
    lines.append('')
    by_class = {}
    for r in rows:
        d = by_class.setdefault(r['cls'], dict(generated=0, uncompilable=0, invalid=0, rejected=0, survived=0, no_verdict=0))
        d['generated'] += 1
        d[r['status']] += 1
    lines.append('| Class | Generated | Uncompilable | Invalid | Rejected | Survived | No verdict |')
    lines.append('| --- | ---: | ---: | ---: | ---: | ---: | ---: |')
    for c, d in sorted(by_class.items()):
        lines.append(f"| {c} | {d['generated']} | {d['uncompilable']} | {d['invalid']} | {d['rejected']} | {d['survived']} | {d['no_verdict']} |")
    lines.append('')
    channels = {}
    for r in rows:
        if r['status'] == 'rejected':
            channels[r['channel']] = channels.get(r['channel'], 0) + 1
    rejected = sum(channels.values()) or 1
    lines.append('| Channel | Rejections | Share |')
    lines.append('| --- | ---: | ---: |')
    for ch, n in sorted(channels.items(), key=lambda kv: -kv[1]):
        lines.append(f'| {ch} | {n} | {100 * n // rejected}% |')
    lines.append('')
    secs = [r['seconds'] for r in rows if r.get('seconds')]
    if secs:
        lines.append(f'Time per mutant: median {sorted(secs)[len(secs) // 2]} s, mean {sum(secs) // len(secs)} s, '
                     f'total {sum(secs) // 3600} h {(sum(secs) % 3600) // 60} min of worker time over {len(secs)} runs.')
        lines.append('')
    survivors = [r for r in rows if r['status'] == 'survived']
    lines.append(f'### Survivors ({len(survivors)})')
    lines.append('')
    for r in survivors:
        runs = '; '.join(f"{x['suite']}{'' if x['prefixes'] == [''] else ' ' + ','.join(x['prefixes'])}: {x['status']}"
                         for x in r['runs'])
        lines.append(f"- `{r['id']}` `{r['file']}:{r['line']}` {r['cls']} ({runs})")
        lines.append('  ```')
        lines.append(f"  - {r['old'].strip()}")
        lines.append(f"  + {r['new'].strip()}")
        lines.append('  ```')
    lines.append('')
    unc = [r for r in rows if r['status'] in ('uncompilable', 'invalid')]
    lines.append(f'### Uncompilable or invalid ({len(unc)})')
    lines.append('')
    for r in unc:
        lines.append(f"- `{r['id']}` `{r['file']}:{r['line']}` {r['cls']}: `{r['new'].strip()[:110]}`")
    lines.append('')
    nv = [r for r in rows if r['status'] == 'no_verdict']
    lines.append(f'### No verdict ({len(nv)})')
    lines.append('')
    for r in nv:
        lines.append(f"- `{r['id']}` `{r['file']}:{r['line']}` {r['cls']}: {r['channel']} {r['problem'][:160]}")
    return '\n'.join(lines) + '\n'


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--show')
    ap.add_argument('--apply')
    ap.add_argument('--into')
    ap.add_argument('--run', action='store_true')
    ap.add_argument('--ids', nargs='*')
    ap.add_argument('--class', dest='classes', nargs='*', choices=CLASSES)
    ap.add_argument('--file', dest='files', nargs='*')
    ap.add_argument('--cap', type=int)
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--scratch-offset', type=int, default=0,
                    help='first scratch worktree index (fresh trees when earlier ones are still in use)')
    ap.add_argument('--timeout', type=int, default=2400, help='seconds per check run')
    ap.add_argument('--results', default='.artifacts/mutation/results.jsonl')
    ap.add_argument('--confirm-survivors', action='store_true')
    ap.add_argument('--summary', action='store_true')
    ap.add_argument('--report', help='write the Markdown tables of --results to this file')
    ap.add_argument('--reclassify', action='store_true', help='recompute non-rejected statuses from the kept reports')
    ap.add_argument('--only-suite', help='run the selected mutants on this whole suite only (a confirmation pass)')
    args = ap.parse_args(argv)
    if args.reclassify:
        print(f'{reclassify(ROOT / args.results, args.workers)} rows reclassified')
        return 0
    if args.report:
        Path(args.report).write_text(render_report(ROOT / args.results))
        print(f'wrote {args.report}')
        return 0

    mutants = enumerate_mutants(args.files, args.classes, args.cap)
    if args.ids:
        wanted = set(args.ids)
        mutants = [m for m in enumerate_mutants() if m['id'] in wanted]
        missing = wanted - {m['id'] for m in mutants}
        if missing:
            raise SystemExit(f'unknown ids: {sorted(missing)}')
    if args.list:
        counts = {}
        for m in mutants:
            counts[(m['file'], m['cls'])] = counts.get((m['file'], m['cls']), 0) + 1
            print(f"{m['id']} {m['file']}:{m['line']} {m['cls']} {m['note']}")
        print(f'{len(mutants)} mutants', file=sys.stderr)
        return 0
    if args.show:
        for m in enumerate_mutants():
            if m['id'] == args.show:
                print(f"{m['file']}:{m['line']} {m['cls']}\n- {m['old']}\n+ {m['new']}")
                return 0
        raise SystemExit('unknown id')
    if args.apply:
        if not args.into:
            raise SystemExit('--apply needs --into WORKTREE')
        for m in enumerate_mutants():
            if m['id'] == args.apply:
                apply_mutant(m, args.into)
                print(f"applied {m['id']} to {args.into}/{m['file']}:{m['line']}")
                return 0
        raise SystemExit('unknown id')
    if args.summary:
        rows, by = summarise(ROOT / args.results)
        for (f, c), d in sorted(by.items()):
            print(f"{f} {c} generated {d['generated']} uncompilable {d['uncompilable']} rejected {d['rejected']} "
                  f"survived {d['survived']} no_verdict {d['no_verdict']} channels {d['channels']}")
        print(f"{len(rows)} results")
        return 0
    if args.run:
        global ONLY_SUITE
        ONLY_SUITE = args.only_suite
        dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT,
                               capture_output=True, text=True).stdout
        if dirty:
            raise SystemExit('the campaign tree must be clean (the ids are of the committed tree)')
        results_path = ROOT / args.results
        results_path.parent.mkdir(parents=True, exist_ok=True)
        run_campaign(mutants, args.workers, results_path, args.timeout, args.confirm_survivors, args.scratch_offset)
        return 0
    ap.print_help()
    return 2


if __name__ == '__main__':
    sys.exit(main())
