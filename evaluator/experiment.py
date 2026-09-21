"""Coordinator-produced batch evidence with explicit outcomes for every input."""
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path

from harness.trace import InvalidTrace, UnsupportedTrace, validate_trace
from harness.linux import LinuxRunError, run_linux
from .generate import identity
from .protocol import compare, loads, validate_coverage, InvalidOutput
from .runner import run_model
from .submission import canonical, digest
from .coverage import symbolize
from .boundary import ROOT


def atomic_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def coverage_rows(path):
    return [loads(line) for line in Path(path).read_text().splitlines()]


def run_batch(model, traces, out, *, required_identities, branch_labels):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    if not traces or len(traces) != len(required_identities):
        raise ValueError('empty or omitted required test batch')
    if [identity(t) for t in traces] != required_identities:
        raise ValueError('required test identities/order changed')
    if len({t.get('id') for t in traces}) != len(traces):
        raise ValueError('duplicate trace identifiers')
    manifest = dict(version=1, author='coordinator evaluator', status='running',
                    candidate_sha256=model.identity, required_identities=required_identities,
                    input_sha256=digest(canonical(traces)), started_at_utc=datetime.now(timezone.utc).isoformat())
    atomic_json(out / 'attempt.json', manifest)
    atomic_json(out / 'inputs.json', traces)
    results = [None] * len(traces)
    valid, positions = [], []
    for index, trace in enumerate(traces):
        try:
            valid.append(validate_trace(trace))
            positions.append(index)
        except UnsupportedTrace as exc:
            results[index] = dict(id=trace.get('id'), outcome='unsupported_input', detail=str(exc))
        except InvalidTrace as exc:
            results[index] = dict(id=trace.get('id'), outcome='invalid_input', detail=str(exc))
    if valid:
        try:
            linux = run_linux(valid, out / 'linux')
            coverage = coverage_rows(out / 'linux/coverage.jsonl')
            validate_coverage(valid, coverage)
            try:
                mapped = symbolize(coverage, ROOT / '.artifacts/kernel-active-sandbox/vmlinux')
            except (ValueError, OSError) as exc:
                raise InvalidOutput(str(exc)) from exc
            atomic_json(out / 'linux/coverage-map.json', mapped)
            execution, observations = run_model(model, valid, out / 'model')
            if observations is None:
                for position, trace in zip(positions, valid):
                    results[position] = dict(id=trace['id'], **execution)
            else:
                for position, trace, actual, expected in zip(positions, valid, observations, linux):
                    if (any(b['label'] not in branch_labels for b in actual['branches']) or
                            {b['index'] for b in actual['branches']} != set(range(len(trace['ops'])))):
                        results[position] = dict(id=trace['id'], outcome='missing_coverage', side='model')
                    else:
                        results[position] = compare(trace, expected, actual)
        except LinuxRunError as exc:
            for position, trace in zip(positions, valid):
                results[position] = dict(id=trace['id'], outcome=exc.kind, side='linux', detail=str(exc))
        except InvalidOutput as exc:
            for position, trace in zip(positions, valid):
                results[position] = dict(id=trace['id'], outcome='missing_coverage', side='linux', detail=str(exc))
    counts = dict(Counter(r['outcome'] for r in results))
    report = dict(version=1, status='pass' if counts == {'agreement': len(traces)} else 'fail',
                  input_count=len(traces), distinct_traces=len(set(required_identities)), counts=counts, results=results,
                  candidate_sha256=model.identity, required_identities=required_identities)
    atomic_json(out / 'report.json', report)
    manifest.update(status='complete', report_sha256=digest((out / 'report.json').read_bytes()),
                    finished_at_utc=datetime.now(timezone.utc).isoformat())
    atomic_json(out / 'attempt.json', manifest)
    return report


def validate_completed_batch(out, traces, candidate_identity):
    """A prior attempt is reusable only with a complete, bound evidence record."""
    out = Path(out)
    record = json.loads((out / 'attempt.json').read_text())
    report_path = out / 'report.json'
    expected = [identity(t) for t in traces]
    if record.get('status') != 'complete' or record.get('candidate_sha256') != candidate_identity:
        raise ValueError('incomplete attempt or stale candidate')
    if record.get('required_identities') != expected or record.get('input_sha256') != digest(canonical(traces)):
        raise ValueError('stale or omitted required input')
    if record.get('report_sha256') != digest(report_path.read_bytes()):
        raise ValueError('missing or changed evaluator report')
    report = json.loads(report_path.read_text())
    if report.get('input_count') != len(traces) or len(report.get('results', [])) != len(traces):
        raise ValueError('empty or omitted evaluator results')
    if [r.get('id') for r in report['results']] != [t['id'] for t in traces]:
        raise ValueError('missing or reordered evaluator results')
    return report
