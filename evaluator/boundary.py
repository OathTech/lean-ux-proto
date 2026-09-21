"""Local nono profiles for read-only model inputs and private build outputs."""
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def environment(cache, artifacts):
    # Do not pass agent credentials, loader hooks, or unrelated tool configuration.
    result = {key: os.environ[key] for key in ('HOME', 'USER', 'LOGNAME') if key in os.environ}
    result.update(PATH='/usr/bin:/bin', LANG='C', LC_ALL='C', LEAN_NUM_THREADS='1',
                  LEANUX_SHARED_ROOT=str(ROOT), LEANUX_CACHE_ROOT=str(cache),
                  LEANUX_ARTIFACTS=str(artifacts))
    return result


def profile(path, source, scratch, extra_read=()):
    source, scratch = Path(source).resolve(), Path(scratch).resolve()
    for location in (path, source, scratch, *extra_read):
        if not Path(location).resolve().is_relative_to(ROOT):
            raise ValueError('Evaluation paths must remain within this project')
    value = {
        'extends': 'default', 'meta': {'name': 'leanux-evaluation', 'version': '1.0.0'},
        'workdir': {'access': 'read'},
        'filesystem': {
            'read': ['/usr', '/proc', '/etc/localtime', '/etc/python3.12',
                     str(ROOT / '.tools'), str(ROOT / '.deps/go-mod'),
                     str(ROOT / 'scripts'), str(source), *map(str, extra_read)],
            'allow': [str(scratch)]},
        'network': {'block': True}}
    Path(path).write_text(json.dumps(value, indent=2) + '\n')
    return value


def prepare(source, scratch, profile_path, extra_read=()):
    scratch = Path(scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    env = environment(scratch / 'cache', scratch / 'artifacts')
    # Trusted wrapper initialization happens outside candidate execution. The
    # wrapper source is read-only and outside the candidate's writable grants.
    subprocess.run([ROOT / 'scripts/in-bundle', 'true'], env=env, check=True,
                   cwd=source, capture_output=True)
    profile(profile_path, source, scratch, extra_read)
    nono = shutil.which('nono') or '/home/dev/.cargo/bin/nono'
    prefix = [nono, 'wrap', '--silent', '--profile', str(profile_path),
              '--workdir', str(source), '--allow-cwd', '--', str(ROOT / 'scripts/in-bundle')]
    return prefix, env
