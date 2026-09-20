#!/usr/bin/python3
"""Exercise worktree isolation, recovery, protected cleanup, and evidence replay."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MANAGER = ROOT / 'scripts/worktrees'
RUNS = ROOT / '.artifacts/runs'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--prefix', default='bootstrap-' + datetime.now().strftime('%Y%m%d%H%M%S'))
args = parser.parse_args()
PREFIX = args.prefix
OUT = RUNS / 'evidence' / PREFIX
OUT.mkdir(parents=True, exist_ok=False)
steps = []


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def call(name, command, code=0, timeout=180, env=None):
    result = subprocess.run([str(c) for c in command], cwd=ROOT, env=env,
                            capture_output=True, text=True, timeout=timeout)
    log = OUT / (name + '.log')
    log.write_text(result.stdout + result.stderr)
    steps.append({'check': name, 'command': [str(c) for c in command],
                  'expected_exit': code, 'exit_code': result.returncode,
                  'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log)})
    if result.returncode != code:
        raise AssertionError(f'{name}: expected {code}, got {result.returncode}\n{log.read_text()[-8000:]}')
    return result


def ledger():
    return json.loads((RUNS / 'campaign.json').read_text())


def record(task):
    return next(r for r in ledger()['worktrees'] if r['id'] == task)


def wait_file(path, process):
    deadline = time.monotonic() + 10
    while not path.exists():
        if process.poll() is not None or time.monotonic() > deadline:
            raise AssertionError('Test process did not become ready')
        time.sleep(0.02)


def save_report(status, error=None):
    report = {'status': status, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'steps': steps, 'error': error}
    (OUT / 'report.json').write_text(json.dumps(report, indent=2) + '\n')


try:
    base = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    identities = {p: sha(ROOT / p) for p in (
        '.tools/lean/bin/lean', '.tools/lean/bin/lake',
        '.tools/sysroot/usr/bin/gcc-13', '.tools/sysroot/usr/bin/python3.12',
        'dependencies/sources.lock.json', 'dependencies/toolchains.lock.json')}
    manifest = {'base': base, 'shared_root': str(ROOT), 'shared_identities': identities,
                'checker_sha256': sha(__file__), 'manager_sha256': sha(MANAGER)}
    (OUT / 'inputs.json').write_text(json.dumps(manifest, indent=2) + '\n')
    tasks = [PREFIX + '-a', PREFIX + '-b']
    existing = [r['id'] for r in ledger()['worktrees'] if r['state'] != 'removed']
    if tasks[0] not in existing:
        call('create-a', [MANAGER, 'create', tasks[0]])
    else:
        assert record(tasks[0])['state'] == 'idle' and record(tasks[0])['base'] == base
    call('interrupt-creation-b', [MANAGER, 'create', tasks[1], '--interrupt-after-add'], code=75)
    assert record(tasks[1])['state'] == 'creating'
    call('resume-creation', [MANAGER, 'reconcile'])
    assert record(tasks[1])['state'] == 'idle'
    tree_a, tree_b = [Path(record(task)['path']) for task in tasks]
    sentinels = OUT / 'decoys'
    sentinels.mkdir()
    sentinel = sentinels / 'shared-input'
    sentinel.write_text('preserve this disposable shared-input decoy\n')
    sentinel_sha = sha(sentinel)
    cache_paths = []
    for index, task in enumerate(tasks):
        rec = record(task)
        tree, scratch = Path(rec['path']), Path(rec['scratch'])
        assert rec['base'] == base
        assert not any((tree / name).exists() for name in ('.tools', '.deps', '.cache', '.artifacts'))
        profile = OUT / f'profile-{index}.json'
        profile.write_text(json.dumps({
            'extends': 'default', 'meta': {'name': f'bootstrap-{index}', 'version': '1.0.0'},
            'workdir': {'access': 'read'},
            'filesystem': {'read': ['/usr', '/proc', '/etc/localtime', '/etc/python3.12',
                                    str(ROOT / '.tools'), str(ROOT / '.deps/go-mod'),
                                    str(tree), str(sentinels)], 'allow': [str(scratch)]},
            'network': {'block': True}}, indent=2) + '\n')
        command = [shutil.which('nono'), 'wrap', '--silent', '--profile', profile,
                   '--workdir', tree, '--allow-cwd', '--', tree / 'scripts/in-bundle']
        call(f'toolchains-{index}', command + ['python3', tree / 'scripts/probe-toolchains.py'])
        check = (
            'import errno,json,os,socket; from pathlib import Path; '
            f'p=Path({str(sentinel)!r}); denied=False\n'
            'try: p.write_text("changed")\n'
            'except OSError as e: assert e.errno in (errno.EACCES,errno.EPERM); denied=True\n'
            'assert denied\n'
            'for af in (socket.AF_INET,socket.AF_INET6):\n'
            ' for kind in (socket.SOCK_STREAM,socket.SOCK_DGRAM):\n'
            '  try: s=socket.socket(af,kind)\n'
            '  except OSError as e: assert e.errno in (errno.EACCES,errno.EPERM)\n'
            '  else: s.close(); raise AssertionError("network socket allowed")\n'
            'print(json.dumps({k:os.environ[k] for k in '
            '("LEANUX_ROOT","LEANUX_SHARED_ROOT","LEANUX_CACHE_ROOT","LEANUX_ARTIFACTS","GOMODCACHE")}))')
        result = call(f'boundary-{index}', command + ['python3', '-c', check])
        environment = json.loads(result.stdout)
        cache_paths.append(environment['LEANUX_CACHE_ROOT'])
        assert Path(environment['LEANUX_ARTIFACTS']).is_relative_to(scratch)
        assert environment['LEANUX_SHARED_ROOT'] == str(ROOT)
        assert environment['GOMODCACHE'] == str(ROOT / '.deps/go-mod')
        assert sha(sentinel) == sentinel_sha
    assert cache_paths[0] != cache_paths[1]

    nested = call('nested-launcher', [tree_a / 'scripts/in-bundle', tree_b / 'scripts/in-bundle',
        'python3', '-c', 'import os; print(os.environ["LEANUX_CACHE_ROOT"])'])
    assert nested.stdout.strip() == cache_paths[1]
    original = (tree_a / 'README.md').read_bytes()
    (tree_a / 'README.md').write_bytes(original + b'\nTemporary isolated task change.\n')
    assert (tree_b / 'README.md').read_bytes() == original
    assert (ROOT / 'README.md').read_bytes() == original

    # Promote immutable inputs/logs and replay sources before requesting cleanup.
    source_probe = next((Path(record(tasks[0])['scratch']) / 'artifacts/probes').glob('toolchains-*'))
    for filename in ('Main.lean', 'probe.c'):
        shutil.copyfile(source_probe / filename, OUT / filename)
    retained = [{'path': str(path.relative_to(ROOT)), 'sha256': sha(path)} for path in
                [OUT / 'inputs.json', OUT / 'Main.lean', OUT / 'probe.c',
                 OUT / 'toolchains-0.log', OUT / 'toolchains-1.log']]
    receipts = []
    for task in tasks:
        receipt = OUT / f'{task}-receipt.json'
        receipt.write_text(json.dumps({'worktree_id': task, 'retained': retained}, indent=2) + '\n')
        receipts.append(receipt)
    remove_a = [MANAGER, 'remove', tasks[0], '--receipt', receipts[0]]
    result = call('reject-dirty', remove_a, code=1)
    assert 'Dirty worktree' in result.stderr and tree_a.exists()
    (tree_a / 'README.md').write_bytes(original)
    call('acquire-owner', [MANAGER, 'acquire', tasks[0], '--owner', 'bootstrap'])
    result = call('reject-active', remove_a, code=1)
    assert 'active owner' in result.stderr
    call('release-owner', [MANAGER, 'release', tasks[0], '--owner', 'bootstrap'])
    result = call('reject-unregistered', [MANAGER, 'remove', 'not-registered', '--receipt', receipts[0]], code=1)
    assert 'Not an active registered' in result.stderr
    (tree_a / '.lake').symlink_to(sentinels, target_is_directory=True)
    result = call('reject-symlink', remove_a, code=1)
    assert sentinel.exists() and sha(sentinel) == sentinel_sha and tree_a.exists()
    (tree_a / '.lake').unlink()
    (tree_a / '.cache').mkdir()
    (tree_a / '.cache/unknown').write_text('unregistered ignored work')
    result = call('reject-unknown-ignored', remove_a, code=1)
    assert 'Unregistered ignored contents' in result.stderr
    (tree_a / '.cache/unknown').unlink()
    (tree_a / '.cache').rmdir()

    # A surviving child holds an output FD while its cwd is the main checkout.
    scratch_a = Path(record(tasks[0])['scratch'])
    ready, release = scratch_a / 'child-ready', scratch_a / 'parent-release'
    child_code = (
        'import os,time; from pathlib import Path\n'
        'pid=os.fork()\n'
        'if pid == 0:\n'
        f' f=open({str(scratch_a / "held-output")!r},"w")\n'
        f' Path({str(ready)!r}).write_text(str(os.getpid()))\n'
        ' while True: time.sleep(0.1)\n'
        f'while not Path({str(release)!r}).exists(): time.sleep(0.01)\n')
    parent = subprocess.Popen(['/usr/bin/python3', '-c', child_code], cwd=ROOT,
                              start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
        wait_file(ready, parent)
        call('acquire-process', [MANAGER, 'acquire', tasks[0], '--owner', 'process-probe', '--pid', parent.pid])
        release.touch()
        parent.wait(timeout=10)
        call('reconcile-surviving-child', [MANAGER, 'reconcile'])
        assert record(tasks[0])['state'] == 'active'
        result = call('reject-release-live-child', [MANAGER, 'release', tasks[0], '--owner', 'process-probe'], code=1)
        assert 'live process' in result.stderr
    finally:
        os.killpg(parent.pid, signal.SIGTERM)
        parent.wait(timeout=10)
    time.sleep(0.1)
    call('release-ended-process', [MANAGER, 'release', tasks[0], '--owner', 'process-probe'])

    # Enforce aggregate admission budget without allocating large data.
    path = RUNS / 'campaign.json'
    before = ledger()
    altered = json.loads(json.dumps(before))
    altered['operating_limits']['additional_bytes'] = 0
    path.write_text(json.dumps(altered, indent=2) + '\n')
    try:
        result = call('reject-disk-budget', [MANAGER, 'create', PREFIX + '-over-budget'], code=1)
        assert 'Aggregate additional-artifact budget' in result.stderr
    finally:
        path.write_text(json.dumps(before, indent=2) + '\n')

    call('remove-a', remove_a)
    call('interrupt-removal-b', [MANAGER, 'remove', tasks[1], '--receipt', receipts[1],
                                '--interrupt-after-git-remove'], code=75)
    assert record(tasks[1])['state'] == 'removing'
    call('resume-removal', [MANAGER, 'reconcile'])
    for task in tasks:
        rec = record(task)
        assert rec['state'] == 'removed'
        assert not Path(rec['path']).exists() and not Path(rec['scratch']).exists()
        assert 'task/' + task not in subprocess.check_output(['git', 'worktree', 'list', '--porcelain'], cwd=ROOT, text=True)

    with tempfile.TemporaryDirectory(prefix='bootstrap-replay-', dir=RUNS) as temporary:
        env = os.environ.copy()
        env.pop('LEANUX_ROOT', None)
        env['LEANUX_CACHE_ROOT'] = temporary + '/cache'
        env['LEANUX_ARTIFACTS'] = temporary + '/artifacts'
        call('replay-lean', [ROOT / 'scripts/in-bundle', 'lean', '--run', OUT / 'Main.lean'], env=env)
        call('replay-c-build', [ROOT / 'scripts/in-bundle', 'gcc', '-static', OUT / 'probe.c', '-o', temporary + '/probe'], env=env)
        call('replay-c', [temporary + '/probe'])
    for filename, identity in identities.items():
        assert sha(ROOT / filename) == identity, filename
    assert sha(sentinel) == sentinel_sha
    call('git-metadata-audit', ['git', 'worktree', 'prune', '--dry-run', '--verbose'])
    save_report('pass')
    print(f'PASS: worktree bootstrap ({len(steps)} checks); evidence in {OUT.relative_to(ROOT)}')
except BaseException as exc:
    save_report('fail', repr(exc))
    raise
