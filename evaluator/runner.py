"""Fresh model snapshots, independent builds, and bounded JSONL execution."""
from dataclasses import dataclass
import json
from pathlib import Path
import shutil

from .boundary import ROOT, prepare
from .process import run
from .protocol import parse_batch
from .submission import digest, canonical, file_manifest, validate_submission

LEAN_ADDRESS_SPACE = 8 * 1024**3


@dataclass
class Model:
    source: Path
    scratch: Path
    prefix: list
    env: dict
    identity: str


def save_execution(out, name, result):
    (out / (name + '.stdout')).write_bytes(result.stdout)
    (out / (name + '.stderr')).write_bytes(result.stderr)
    (out / (name + '.json')).write_text(json.dumps(result.summary(), indent=2) + '\n')


def build_model(source_root, attempt, submission=None, expected_identities=None):
    source_root, attempt = Path(source_root).resolve(), Path(attempt).resolve()
    if not attempt.is_relative_to(ROOT / '.artifacts/runs/workspaces'):
        raise ValueError('Build attempt must be within registered workspace scratch')
    attempt.mkdir(parents=True, exist_ok=False)
    source, scratch = attempt / 'source', attempt / 'scratch'
    source.mkdir()
    scratch.mkdir()
    paths = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Leanux.lean']
    paths += [str(p.relative_to(source_root)) for p in (source_root / 'Leanux').rglob('*.lean')]
    manifest = file_manifest(source_root, paths)
    for name in paths:
        target = source / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_root / name, target)
    if submission is not None:
        policy = json.loads((ROOT / 'contracts/submission-v1.json').read_text())
        validate_submission(submission, expected_identities, policy)
        for name, content in submission['files'].items():
            target = source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content)
    final_paths = [str(p.relative_to(source)) for p in source.rglob('*') if p.is_file()]
    final_manifest = file_manifest(source, final_paths)
    identity = digest(canonical(final_manifest))
    (attempt / 'inputs.json').write_text(json.dumps(dict(base=manifest, candidate=final_manifest,
                                                       candidate_sha256=identity), indent=2) + '\n')
    (scratch / 'lake').mkdir()
    (source / '.lake').symlink_to(scratch / 'lake', target_is_directory=True)
    prefix, env = prepare(source, scratch, attempt / 'profile.json')
    result = run(prefix + ['lake', '--no-cache', 'build', 'leanux-model'],
                 cwd=source, env=env, timeout=900, cpu_seconds=900, address_space=LEAN_ADDRESS_SPACE)
    save_execution(attempt, 'build', result)
    if result.outcome != 'success':
        raise RuntimeError(f'model build {result.outcome}: {result.stderr.decode(errors="replace")[-4000:]}')
    if file_manifest(source, final_paths) != final_manifest:
        raise RuntimeError('model source changed during build')
    return Model(source, scratch, prefix, env, identity)


def run_model(model, traces, out):
    if not traces:
        return dict(outcome='invalid_input', detail='empty required test batch'), None
    from harness.trace import validate_trace, InvalidTrace, UnsupportedTrace
    try:
        traces = [validate_trace(trace) for trace in traces]
    except UnsupportedTrace as exc:
        return dict(outcome='unsupported_input', detail=str(exc)), None
    except InvalidTrace as exc:
        return dict(outcome='invalid_input', detail=str(exc)), None
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    payload = b''.join(canonical(trace) + b'\n' for trace in traces)
    (out / 'inputs.jsonl').write_bytes(payload)
    result = run(model.prefix + [model.scratch / 'lake/build/bin/leanux-model'],
                 cwd=model.source, env=model.env, input_data=payload, timeout=120,
                 cpu_seconds=120, address_space=LEAN_ADDRESS_SPACE)
    save_execution(out, 'model', result)
    if result.outcome != 'success':
        return dict(outcome=result.outcome, execution=result.summary()), None
    try:
        observations = parse_batch(traces, result.stdout)
    except ValueError as exc:
        return dict(outcome='invalid_output', detail=str(exc)), None
    return dict(outcome='success', candidate_sha256=model.identity), observations
