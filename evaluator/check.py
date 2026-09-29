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
import subprocess
import sys

from harness.linux import KERNEL, LinuxRunError, run_linux
from harness.trace import InvalidTrace, loads_trace, validate_trace
from .coverage import symbolize
from .generate import generate
from .protocol import InvalidOutput, compare, loads, parse_batch, validate_coverage

ROOT = Path(__file__).resolve().parents[1]
ANCHORS = ROOT / 'correspondence/kcov-anchors-v1.json'
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


def build_model(out):
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    result = subprocess.run(['lake', 'build', 'leanux-model'], cwd=ROOT, env=env,
                            capture_output=True, timeout=1800)
    (out / 'build.log').write_bytes(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError('model build failed; see build.log')


def run_model(traces, out):
    binary = ROOT / '.lake/build/bin/leanux-model'
    payload = ''.join(json.dumps(t, separators=(',', ':'), sort_keys=True) + '\n' for t in traces)
    (out / 'inputs.jsonl').write_text(payload)
    result = subprocess.run([binary], input=payload.encode(), capture_output=True, timeout=300)
    (out / 'model.stdout').write_bytes(result.stdout)
    (out / 'model.stderr').write_bytes(result.stderr)
    if result.returncode:
        raise InvalidOutput(f'model exited {result.returncode}')
    return parse_batch(traces, result.stdout)


def load_anchors():
    anchors = json.loads(ANCHORS.read_text())
    for op, labels in anchors['labels'].items():
        for label, entry in labels.items():
            if set(entry) not in ({'covered', 'uncovered'}, {'unobservable'}):
                raise ValueError(f'anchor {op}/{label}: expected covered+uncovered or unobservable')
    return anchors


def op_lines(row, locations, files):
    lines = set()
    for pc in row['pcs']:
        for frame in locations[pc]:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files:
                lines.add(source)
    return lines


def control_flow(trace, model_obs, coverage, locations, anchors):
    """A2: each reported label's witness lines agree with Linux coverage."""
    labels = {}
    for branch in model_obs['branches']:
        labels.setdefault(branch['index'], set()).add(branch['label'])
    problems, gaps = [], Counter()
    for index, op in enumerate(trace['ops']):
        lines = op_lines(coverage[index], locations, anchors['files'])
        table = anchors['labels'].get(op['op'], {})
        reported = labels.get(index, set())
        if not reported:
            problems.append(dict(index=index, problem='no model label'))
        for label in sorted(reported):
            entry = table.get(label)
            if entry is None:
                problems.append(dict(index=index, label=label, problem='label has no anchor entry'))
            elif 'covered' in entry:
                missing = [line for line in entry['covered'] if line not in lines]
                present = [line for line in entry['uncovered'] if line in lines]
                if missing or present:
                    problems.append(dict(index=index, label=label, missing=missing, unexpected=present))
        for gap in anchors['known_gaps']:
            if gap['op'] == op['op'] and gap['line'] in lines:
                gaps[gap['name']] += 1
    return problems, gaps


def run_chunk(traces, out, anchors):
    out.mkdir(parents=True)
    results, gaps = {}, Counter()
    try:
        linux = run_linux(traces, out / 'linux')
        coverage = [loads(line) for line in (out / 'linux/coverage.jsonl').read_text().splitlines()]
        validate_coverage(traces, coverage)
        mapped = symbolize(coverage, KERNEL / 'vmlinux')
        (out / 'linux/coverage-map.json').write_text(json.dumps(mapped, indent=1) + '\n')
    except LinuxRunError as exc:
        return {t['id']: dict(outcome=exc.kind, side='linux', detail=str(exc)) for t in traces}, gaps
    except (InvalidOutput, ValueError, OSError, subprocess.SubprocessError) as exc:
        return {t['id']: dict(outcome='invalid_coverage', side='linux', detail=str(exc)) for t in traces}, gaps
    (out / 'model').mkdir()
    try:
        model = run_model(traces, out / 'model')
    except (InvalidOutput, OSError, subprocess.SubprocessError) as exc:
        return {t['id']: dict(outcome='invalid_output', side='model', detail=str(exc)) for t in traces}, gaps
    rows = iter(coverage)
    for trace, expected, actual in zip(traces, linux, model):
        trace_coverage = [next(rows) for _ in trace['ops']]
        result = compare(trace, expected, actual)
        if result['outcome'] == 'agreement':
            problems, trace_gaps = control_flow(trace, actual, trace_coverage, mapped['locations'], anchors)
            gaps.update(trace_gaps)
            if problems:
                result = dict(id=trace['id'], outcome='control_flow_mismatch', problems=problems)
        results[trace['id']] = result
    return results, gaps


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
    out.mkdir(parents=True, exist_ok=False)
    try:
        traces = load_traces(suites, args.generated_count, args.seed, args.trace)
        anchors = load_anchors()
    except (InvalidTrace, ValueError, OSError) as exc:
        parser.exit(2, f'invalid input: {exc}\n')
    if not args.no_build:
        build_model(out)
    started = datetime.now(timezone.utc).isoformat()
    results, gaps = {}, Counter()
    for start in range(0, len(traces), CHUNK):
        chunk = traces[start:start + CHUNK]
        print(f'traces {start}-{start + len(chunk) - 1} ...', file=sys.stderr, flush=True)
        chunk_results, chunk_gaps = run_chunk(chunk, out / f'chunk-{start // CHUNK:03}', anchors)
        results.update(chunk_results)
        gaps.update(chunk_gaps)
    ordered = [results[trace['id']] for trace in traces]
    counts = Counter(r['outcome'] for r in ordered)
    report = dict(
        version=1, status='pass' if counts == Counter(agreement=len(traces)) else 'fail',
        started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(),
        git=git_state(), model_sources=model_identity(),
        kernel=dict(vmlinux_sha256=sha256((KERNEL / 'vmlinux').read_bytes())),
        anchors_sha256=sha256(ANCHORS.read_bytes()),
        selection=dict(suites=suites, generated_count=args.generated_count, seed=args.seed, trace=args.trace),
        traces=len(traces), operations=sum(len(t['ops']) for t in traces),
        counts=dict(counts), known_gap_hits=dict(gaps),
        failures=[r for r in ordered if r['outcome'] != 'agreement'])
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'traces', 'operations', 'counts', 'known_gap_hits')}, indent=2))
    print(f'report: {out / "report.json"}', file=sys.stderr)
    return 0 if report['status'] == 'pass' else 1


if __name__ == '__main__':
    raise SystemExit(main())
