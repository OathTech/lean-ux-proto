"""Build the mirror, run traces on the pinned Linux guest and the mirror, compare.

    scripts/in-bundle python3 -m evaluator.check [--suite handwritten,critic,generated]
        [--generated-count N] [--seed S] [--trace ID] [--out DIR] [--no-build]

The command fails unless every trace agrees on observations (A1) and every
operation's model branch labels are consistent with Linux KCOV coverage (A2).
Timeouts, crashes, invalid output, unknown labels and environment failures
never count as agreement. `--trace ID` replays a single case.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from harness.linux import KERNEL, LinuxRunError, run_linux
from harness.trace import InvalidTrace, loads_trace, validate_trace
from .coverage import instrumented_lines, symbolize
from .generate import generate
from .protocol import InvalidOutput, compare, loads, parse_batch, validate_coverage

ROOT = Path(__file__).resolve().parents[1]
ANCHORS = ROOT / 'correspondence/kcov.json'
SUITES = ('handwritten', 'critic', 'generated')
CHUNK = 100


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def model_identity():
    paths = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Leanux.lean']
    paths += sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'Leanux').rglob('*.lean'))
    return {path: sha256((ROOT / path).read_bytes()) for path in paths}


def git_state():
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True, check=True)
    dirty = subprocess.run(['git', 'status', '--porcelain'], cwd=ROOT, capture_output=True, text=True, check=True)
    return dict(head=head.stdout.strip(), dirty=bool(dirty.stdout.strip()))


def load_traces(suites, count, seed, only):
    traces = []
    for suite in suites:
        if suite == 'generated':
            traces += generate(seed, count)
        else:
            files = sorted((ROOT / 'corpus' / suite).glob('*.json'))
            if not files:
                raise ValueError(f'empty corpus suite {suite}')
            traces += [loads_trace(path.read_text()) for path in files]
    ids = [trace['id'] for trace in traces]
    if len(set(ids)) != len(ids):
        raise ValueError('duplicate trace identifiers')
    if only is not None:
        traces = [trace for trace in traces if trace['id'] == only]
        if not traces:
            raise ValueError(f'no trace {only!r} in the selected suites')
    return [validate_trace(trace) for trace in traces]


MODEL = ROOT / '.lake/build/bin/leanux-model'


def build_model(out, rebuild):
    """Build, or with rebuild=False require the existing build to be up to date."""
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    command = ['lake', 'build', 'leanux-model'] + ([] if rebuild else ['--no-build'])
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=1800)
    (out / 'build.log').write_bytes(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError('model build failed or is out of date; see build.log')
    return dict(mode='built' if rebuild else 'reused-up-to-date', binary_sha256=sha256(MODEL.read_bytes()))


def run_model(traces, out):
    payload = ''.join(json.dumps(t, separators=(',', ':'), sort_keys=True) + '\n' for t in traces)
    (out / 'inputs.jsonl').write_text(payload)
    result = subprocess.run([MODEL], input=payload.encode(), capture_output=True, timeout=300)
    (out / 'model.stdout').write_bytes(result.stdout)
    (out / 'model.stderr').write_bytes(result.stderr)
    if result.returncode:
        kind = {3: 'unsupported_path', 4: 'mirror_invariant'}.get(result.returncode, 'invalid_output')
        raise ModelStopped(kind, result.stderr.decode(errors='replace').strip()[-2000:])
    return parse_batch(traces, result.stdout)


class ModelStopped(InvalidOutput):
    """The mirror stopped without observations: a path outside its domain
    (exit 3), a mirror invariant failure (exit 4), or another error."""
    def __init__(self, kind, detail):
        super().__init__(detail)
        self.kind = kind


def load_kcov_config():
    config = json.loads(ANCHORS.read_text())
    if set(config) != {'version', 'description', 'files', 'functions', 'known_gaps'} or config['version'] != 2:
        raise ValueError('kcov config fields or version')
    if not config['files'] or not config['functions'] or any(type(x) is not str for x in config['files'] + config['functions']):
        raise ValueError('kcov config needs anchored files and instrumented functions')
    for gap in config['known_gaps']:
        if set(gap) != {'op', 'name', 'line', 'note'} or gap['line'].rsplit(':', 1)[0] not in config['files']:
            raise ValueError(f'known gap {gap}: fields or file')
    return config


SPAN_WINDOW = (40, 60)
SOURCE = Path(os.environ.get('LEANUX_SHARED_ROOT', ROOT)).resolve() / '.deps/linux'
_source_cache = {}


def non_statement(line):
    """Lines that own no code of their own: braces, labels, blanks and comments."""
    path, number = line.rsplit(':', 1)
    if path not in _source_cache:
        _source_cache[path] = (SOURCE / path).read_text().splitlines()
    lines = _source_cache[path]
    if not 1 <= int(number) <= len(lines):
        raise InvalidOutput(f'span line {line} is beyond the end of the file')
    text = lines[int(number) - 1].strip()
    return (not text or text in ('{', '}', '};') or re.match(r'(/\*|//|\*(\s|/|$))', text) is not None
            or re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*:', text) is not None)


def load_decisions(config):
    """The mirror's decision table (`leanux-model --decisions`), validated."""
    result = subprocess.run([MODEL, '--decisions'], capture_output=True, timeout=60)
    if result.returncode:
        raise InvalidOutput('leanux-model --decisions failed')
    return parse_decisions(loads(result.stdout.decode()), config)


def parse_decisions(decisions, config):
    if type(decisions) is not list or not decisions:
        raise InvalidOutput('empty decision table')
    table = {}
    for entry in decisions:
        if set(entry) != {'label', 'file', 'line', 'when_true', 'when_false', 'unobservable_true', 'unobservable_false',
                          'comparison'}:
            raise InvalidOutput(f'decision fields: {entry}')
        label = entry['label']
        if type(label) is not str or label in table or entry['file'] not in config['files']:
            raise InvalidOutput(f'decision {label}: duplicate label or unanchored file')
        if type(entry['line']) is not int or non_statement(f"{entry['file']}:{entry['line']}"):
            raise InvalidOutput(f'decision {label}: condition line must be a source statement')
        reasons = {True: entry['unobservable_true'], False: entry['unobservable_false']}
        comparison = entry['comparison']
        if comparison is not None and (set(comparison) != {'rel', 'const_rhs'} or comparison['rel'] not in RELATIONS
                                       or type(comparison['const_rhs']) is not bool):
            raise InvalidOutput(f'decision {label}: comparison spec')
        if any(r is not None and (type(r) is not str or not r) for r in reasons.values()):
            raise InvalidOutput(f'decision {label}: unobservable reasons must be strings')
        spans = {}
        for outcome, key in ((True, 'when_true'), (False, 'when_false')):
            lines = set()
            for span in entry[key]:
                if set(span) != {'file', 'lo', 'hi'} or span['file'] not in config['files']:
                    raise InvalidOutput(f'decision {label}: span fields or file')
                if type(span['lo']) is not int or type(span['hi']) is not int or not 1 <= span['lo'] <= span['hi']:
                    raise InvalidOutput(f'decision {label}: span bounds')
                # Spans stay near their condition: within the enclosing C function.
                if not entry['line'] - SPAN_WINDOW[0] <= span['lo'] and span['hi'] <= entry['line'] + SPAN_WINDOW[1]:
                    raise InvalidOutput(f'decision {label}: span {span} too far from line {entry["line"]}')
                lines.update(f"{span['file']}:{n}" for n in range(span['lo'], span['hi'] + 1))
            spans[outcome] = {line for line in lines if not non_statement(line)}
        if spans[True] & spans[False]:
            raise InvalidOutput(f'decision {label}: outcome spans overlap')
        table[label] = dict(site=f"{entry['file']}:{entry['line']}", spans=spans, reasons=reasons,
                            function=label.split('.', 1)[0], comparison=comparison)
    return table


def witness_table(decisions, instrumented, functions):
    """Witnesses are the instrumented lines of each outcome span. A side with
    no witness must declare why it is unobservable, and a declared reason must
    not hide a side that does have witnesses. Each decision's C function (the
    label prefix) must own instrumentation, so reaching it is checkable."""
    table, problems = {}, []
    for label, entry in decisions.items():
        table[label] = {o: entry['spans'][o] & instrumented for o in (True, False)}
        for outcome in (True, False):
            if not table[label][outcome] and entry['reasons'][outcome] is None:
                problems.append(f'{label}={int(outcome)}: no KCOV witness and no unobservable reason')
            if table[label][outcome] and entry['reasons'][outcome] is not None:
                problems.append(f'{label}={int(outcome)}: declared unobservable but witnessed by '
                                f'{sorted(table[label][outcome])}')
        if entry['function'] not in functions:
            problems.append(f'{label}: C function {entry["function"]} owns no instrumentation point')
    if problems:
        raise InvalidOutput('decision table does not match the instrumented kernel:\n  ' + '\n  '.join(problems))
    return table


def op_lines(row, locations, files):
    return set(line_positions(row, locations, files))


def line_positions(row, locations, files):
    """Each anchored line's first position in the operation's coverage. The
    guest records each PC once, at its first execution, in execution order."""
    positions = {}
    for position, pc in enumerate(row['pcs']):
        for frame in locations[pc]:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files:
                positions.setdefault(source, position)
    return positions


def parse_step(label):
    name, sep, outcome = label.rpartition('=')
    if not sep or outcome not in ('0', '1'):
        return None
    return name, outcome == '1'


def control_flow(trace, model_obs, coverage, locations, config, decisions, witnesses, instrumented, functions):
    """A2: the mirror's decision outcomes agree with Linux KCOV coverage.

    For each operation: each decision is reported at most once; a reported
    outcome must cover one of its
    witnesses; the opposite outcome's witnesses must be uncovered; and a
    decision the mirror did not report must have no covered witness at all.
    """
    steps = {}
    for branch in model_obs['branches']:
        steps.setdefault(branch['index'], []).append(branch['label'])
    span_lines = set().union(*(e['spans'][o] for e in decisions.values() for o in (True, False)))
    problems, gaps = [], Counter()
    order_stats = Counter()
    for index, op in enumerate(trace['ops']):
        positions = line_positions(coverage[index], locations, config['files'])
        lines = set(positions)
        if not lines:
            problems.append(dict(index=index, problem='no coverage in anchored files'))
        unmapped = sorted((lines & span_lines) - instrumented)
        if unmapped:
            problems.append(dict(index=index, problem='covered span lines missing from the instrumentation map',
                                 lines=unmapped))
        reported, sequence = set(), []
        for label in steps.get(index, []):
            step = parse_step(label)
            if step is None or step[0] not in decisions:
                problems.append(dict(index=index, label=label, problem='unknown decision'))
            elif any(name == step[0] for name, _ in reported):
                problems.append(dict(index=index, label=label, problem='decision reported more than once'))
            else:
                reported.add(step)
                sequence.append(step)
        if not reported:
            problems.append(dict(index=index, problem='no model decision'))
        for name, outcome in sorted(reported):
            own, other = witnesses[name][outcome], witnesses[name][not outcome]
            if own and not (lines & own):
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='outcome not witnessed',
                                     witnesses=sorted(own)))
            if lines & other:
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='opposite outcome covered',
                                     covered=sorted(lines & other)))
        # Order: within each C function, witnessed decisions appear in the
        # mirror's order at their first witness in Linux's execution. (Across
        # functions an arm's first witness can follow a nested call's
        # decisions, so positions are only comparable within a function.)
        previous = {}
        for name, outcome in sequence:
            covered = witnesses[name][outcome] & lines
            if not covered:
                order_stats['unwitnessed'] += 1
                continue
            here = min(positions[line] for line in covered)
            function = decisions[name]['function']
            if function in previous:
                order_stats['compared'] += 1
                order_stats['ties'] += here == previous[function][1]
            if function in previous and here < previous[function][1]:
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='decision order differs from Linux',
                                     after=previous[function][0], linux_position=here,
                                     previous_position=previous[function][1]))
            previous[function] = (f'{name}={int(outcome)}', here)
        names = {name for name, _ in reported}
        for name, sides in witnesses.items():
            if name not in names and lines & (sides[True] | sides[False]):
                problems.append(dict(index=index, label=name, problem='Linux evaluated an unreported decision',
                                     covered=sorted(lines & (sides[True] | sides[False]))))
        for gap in config['known_gaps']:
            if gap['op'] == op['op'] and gap['line'] in lines:
                gaps[gap['name']] += 1
    gaps.update({f'order: {k}': v for k, v in order_stats.items()})
    return problems, gaps


KCOV_CMP_CONST = 1
RELATIONS = ('lt', 'le', 'gt', 'ge', 'eq', 'ne', 'flag')
# The constants a compiler may use for `x REL c`: `x < c` becomes `x <= c-1`,
# `x <= c` becomes `x < c+1`, and so on; equality and mask tests are exact.
CONSTANT_SHIFTS = {'lt': (0, -1), 'le': (0, 1), 'gt': (0, 1), 'ge': (0, -1), 'eq': (0,), 'ne': (0,), 'flag': (0,)}


def encode(value, bits):
    """`value` as a `bits`-wide C value, or None if it does not fit."""
    if 0 <= value < 1 << bits:
        return value
    if -(1 << (bits - 1)) <= value < 0:
        return value & ((1 << bits) - 1)
    return None


def operands_match(lhs, rhs, record, comparison):
    """Whether a `KCOV_TRACE_CMP` record (type, arg1, arg2) is the C comparison
    `lhs REL rhs` the mirror declares. Operands must fit the recorded width
    (type bits 1-2: log2 bytes). A constant record (KCOV puts the constant in
    arg1) needs a declared constant right-hand side: the variable must equal
    `lhs` exactly and the constant may be shifted only as the relation allows.
    A non-constant record may list the operands in either order, because the
    compiler canonicalizes operand order (`nr < max_fds` is recorded as
    `(max_fds, nr)`)."""
    kind, x, y = record
    bits = 8 << (kind >> 1)
    a, b = encode(lhs, bits), encode(rhs, bits)
    if a is None or b is None:
        return False
    if kind & KCOV_CMP_CONST:
        if not comparison['const_rhs']:
            return False
        return y == a and any(x == (rhs + shift) & ((1 << bits) - 1) for shift in CONSTANT_SHIFTS[comparison['rel']])
    return sorted((x, y)) == sorted((a, b))


def operand_agreement(trace, model_obs, comparisons, locations, decisions):
    """A3: declared value comparisons report operands, and each matches a
    comparison Linux made at the decision's condition line (the innermost
    source frame of the comparison) in the same operation."""
    problems, checked = [], 0
    for branch in model_obs['branches']:
        name = branch['label'].rpartition('=')[0]
        if name not in decisions:
            continue  # control_flow reports unknown labels
        comparison = decisions[name]['comparison']
        if comparison is None:
            if 'operands' in branch:
                problems.append(dict(index=branch['index'], label=branch['label'],
                                     problem='operands on a decision not declared a comparison'))
            continue
        if 'operands' not in branch:
            problems.append(dict(index=branch['index'], label=branch['label'],
                                 problem='declared comparison reported without operands'))
            continue
        site = decisions[name]['site']
        records = [(r[0], int(r[1], 16), int(r[2], 16)) for r in comparisons[branch['index']]['records']
                   if locations[r[3]][0]['source'].split('/.deps/linux/')[-1].split(' ')[0] == site]
        lhs, rhs = branch['operands']
        if not records:
            problems.append(dict(index=branch['index'], label=branch['label'], problem='no comparison recorded at condition',
                                 site=site, operands=[lhs, rhs]))
        elif not any(operands_match(lhs, rhs, r, comparison) for r in records):
            problems.append(dict(index=branch['index'], label=branch['label'], problem='operands differ from Linux',
                                 site=site, operands=[lhs, rhs], linux=[[k, hex(x), hex(y)] for k, x, y in records[:6]]))
        else:
            checked += 1
    return problems, checked


def run_chunk(traces, out, kcov):
    out.mkdir(parents=True)
    results, gaps = {}, Counter()
    outcomes = Counter()
    try:
        linux = run_linux(traces, out / 'linux')
        coverage = [loads(line) for line in (out / 'linux/coverage.jsonl').read_text().splitlines()]
        validate_coverage(traces, coverage)
        mapped = symbolize(coverage, KERNEL / 'vmlinux')
        (out / 'linux/coverage-map.json').write_text(json.dumps(mapped, indent=1) + '\n')
        comparisons = [loads(line) for line in (out / 'linux/comparisons.jsonl').read_text().splitlines()]
        compared = symbolize([{'pcs': sorted({r[3] for row in comparisons for r in row['records']})}],
                             KERNEL / 'vmlinux')
        (out / 'linux/comparison-map.json').write_text(json.dumps(compared, indent=1) + '\n')
    except LinuxRunError as exc:
        return {t['id']: dict(outcome=exc.kind, side='linux', detail=str(exc)) for t in traces}, gaps, outcomes
    except (InvalidOutput, ValueError, OSError, subprocess.SubprocessError) as exc:
        return {t['id']: dict(outcome='invalid_coverage', side='linux', detail=str(exc)) for t in traces}, gaps, outcomes
    (out / 'model').mkdir()
    try:
        model = run_model(traces, out / 'model')
    except (InvalidOutput, OSError, subprocess.SubprocessError) as exc:
        kind = getattr(exc, 'kind', 'invalid_output')
        return {t['id']: dict(outcome=kind, side='model', detail=str(exc)) for t in traces}, gaps, outcomes
    rows, cmp_rows = iter(coverage), iter(comparisons)
    for trace, expected, actual in zip(traces, linux, model):
        trace_coverage = [next(rows) for _ in trace['ops']]
        trace_comparisons = [next(cmp_rows) for _ in trace['ops']]
        result = compare(trace, expected, actual)
        if result['outcome'] == 'agreement':
            problems, trace_gaps = control_flow(trace, actual, trace_coverage, mapped['locations'], *kcov)
            operand_problems, checked = operand_agreement(trace, actual, trace_comparisons,
                                                          compared['locations'], kcov[1])
            problems += operand_problems
            outcomes['operand pairs matched'] += checked
            gaps.update(trace_gaps)
            outcomes.update(b['label'] for b in actual['branches'])
            if problems:
                result = dict(id=trace['id'], outcome='control_flow_mismatch', problems=problems)
        results[trace['id']] = result
    return results, gaps, outcomes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--suite', default=','.join(SUITES))
    parser.add_argument('--generated-count', type=int, default=1000)
    parser.add_argument('--seed', type=int, default=20260920)
    parser.add_argument('--trace')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--no-build', action='store_true', help='reuse the existing .lake build')
    args = parser.parse_args(argv)
    suites = args.suite.split(',')
    if not suites or any(s not in SUITES for s in suites):
        parser.error(f'--suite must be a comma-separated subset of {SUITES}')
    artifacts = Path(os.environ.get('LEANUX_ARTIFACTS', ROOT / '.artifacts')).resolve()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out = (args.out or artifacts / 'check' / stamp).resolve()
    if not out.is_relative_to(artifacts) or out == artifacts:
        parser.error(f'--out must be a new directory inside {artifacts}')
    try:
        traces = load_traces(suites, args.generated_count, args.seed, args.trace)
        config = load_kcov_config()
    except (InvalidTrace, ValueError, OSError) as exc:
        parser.exit(2, f'invalid input: {exc}\n')
    out.mkdir(parents=True, exist_ok=False)
    started = datetime.now(timezone.utc).isoformat()
    results, gaps, build, aborted = {}, Counter(), None, None
    outcomes, decisions, kcov = Counter(), {}, None
    try:
        build = build_model(out, rebuild=not args.no_build)
        decisions.update(load_decisions(config))
        instrumented, functions = instrumented_lines(KERNEL / 'vmlinux', config['functions'], config['files'])
        kcov = (config, decisions, witness_table(decisions, instrumented, functions), instrumented, functions)
        observable = sum(bool(w[True] or w[False]) for w in kcov[2].values())
        print(f'{len(decisions)} decisions, {observable} with KCOV witnesses', file=sys.stderr)
        for start in range(0, len(traces), CHUNK):
            chunk = traces[start:start + CHUNK]
            print(f'traces {start}-{start + len(chunk) - 1} ...', file=sys.stderr, flush=True)
            chunk_results, chunk_gaps, chunk_outcomes = run_chunk(chunk, out / f'chunk-{start // CHUNK:03}', kcov)
            results.update(chunk_results)
            gaps.update(chunk_gaps)
            outcomes.update(chunk_outcomes)
    except BaseException as exc:  # recorded as an aborted, failing run, then re-raised
        aborted = f'{type(exc).__name__}: {exc}'
        raise
    finally:
        matched = outcomes.pop('operand pairs matched', 0)
        status = write_report(out, traces, results, gaps, build, aborted, started, suites, args,
                              decision_summary(decisions, outcomes, kcov[2] if kcov else {}), matched)
    return 0 if status == 'pass' else 1


def decision_summary(decisions, outcomes, witnesses):
    """How often each decision outcome occurred in agreeing traces, and
    which outcomes KCOV can witness: the map of what the corpus exercises."""
    rows = {}
    for label, entry in decisions.items():
        rows[label] = dict(site=entry['site'], true=outcomes[f'{label}=1'], false=outcomes[f'{label}=0'],
                           witnessed_true=bool(witnesses.get(label, {}).get(True)),
                           witnessed_false=bool(witnesses.get(label, {}).get(False)))
    return dict(decisions=len(rows), never_evaluated=sorted(l for l, r in rows.items() if not r['true'] + r['false']),
                one_outcome_only=sorted(l for l, r in rows.items() if bool(r['true']) != bool(r['false'])),
                table=rows)


def write_report(out, traces, results, gaps, build, aborted, started, suites, args, decision_coverage=None,
                 operand_pairs_matched=0):
    ordered = [results.get(trace['id'], dict(id=trace['id'], outcome='not_run')) for trace in traces]
    counts = Counter(r['outcome'] for r in ordered)
    vmlinux = KERNEL / 'vmlinux'
    kernel = dict(vmlinux_sha256=sha256(vmlinux.read_bytes())) if vmlinux.is_file() else dict(missing=str(vmlinux))
    passed = (aborted is None and bool(traces) and 'missing' not in kernel
              and counts == Counter(agreement=len(traces)))
    report = dict(
        version=1, status='pass' if passed else 'fail', aborted=aborted, build=build,
        started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(),
        git=git_state(), model_sources=model_identity(),
        kernel=kernel,
        kcov_config_sha256=sha256(ANCHORS.read_bytes()),
        selection=dict(suites=suites, generated_count=args.generated_count, seed=args.seed, trace=args.trace),
        traces=len(traces), operations=sum(len(t['ops']) for t in traces),
        counts=dict(counts), known_gap_hits=dict(gaps), operand_pairs_matched=operand_pairs_matched,
        decision_coverage=decision_coverage,
        failures=[r for r in ordered if r['outcome'] != 'agreement'])
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'traces', 'operations', 'counts', 'operand_pairs_matched')}, indent=2))
    print(f'report: {out / "report.json"}', file=sys.stderr)
    return report['status']


if __name__ == '__main__':
    raise SystemExit(main())
