#!/usr/bin/python3
"""Check the declared evaluation fixture using disposable files and processes."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from evaluator.boundary import prepare
from evaluator.process import run, group_alive


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    if not out.is_relative_to(ROOT / '.artifacts/runs/evidence'):
        raise ValueError('Use a fresh evidence directory')
    out.mkdir(parents=True, exist_ok=False)
    source, scratch, protected, private = [out / x for x in ('source', 'scratch', 'protected-decoys', 'private-decoys')]
    for path in (source, scratch, protected, private):
        path.mkdir()
    for name in ('tool', 'evaluator-input', 'accepted-result'):
        (protected / name).write_text('disposable protected fixture\n')
    (source / 'frozen-source-decoy').write_text('disposable frozen source fixture\n')
    (private / 'outside-allowlist').write_text('disposable private fixture\n')
    identities = {str(p): sha(p) for parent in (source, protected, private) for p in parent.iterdir()}
    (scratch / 'link-to-protected').symlink_to(protected / 'tool')
    (scratch / 'link-to-private').symlink_to(private / 'outside-allowlist')
    steps = []
    prefix, env = prepare(source, scratch, out / 'profile.json', [protected])

    def execute(name, command, **kwargs):
        result = run(prefix + command, cwd=source, env=env, **kwargs)
        (out / (name + '.stdout')).write_bytes(result.stdout)
        (out / (name + '.stderr')).write_bytes(result.stderr)
        steps.append(dict(name=name, **result.summary()))
        return result

    # Sacrificial sibling/parent fixture. SIGUSR1 only toggles a recorded marker;
    # a failed restriction cannot harm any existing coordinator or agent process.
    ready = private / 'ready'
    signal_record = private / 'signal-received'
    process_code = (
        'import os,signal,time;from pathlib import Path\n'
        f'signal.signal(signal.SIGUSR1,lambda *_:Path({str(signal_record)!r}).write_text("received"))\n'
        f'Path({str(ready)!r}).write_text(str(os.getpid()))\n'
        'while True: time.sleep(.1)\n')
    sibling = subprocess.Popen(['/usr/bin/python3', '-c', process_code], cwd=ROOT,
                               start_new_session=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    leaked_fd = os.open(private / 'outside-allowlist', os.O_RDONLY)
    os.set_inheritable(leaked_fd, True)
    try:
        deadline = time.monotonic() + 5
        while not ready.exists():
            if time.monotonic() > deadline:
                raise RuntimeError('fixture process did not start')
            time.sleep(.01)
        probe = source / 'probe.py'
        probe.write_text('''import errno,json,os,signal,socket
from pathlib import Path
results=[]
def denied(name, action):
 try: action()
 except OSError as e: results.append({'name':name,'denied':e.errno in (errno.EACCES,errno.EPERM,errno.EBADF),'errno':e.errno})
 else: results.append({'name':name,'denied':False})
''' + '\n'.join(
            f'denied({("write-" + p.name)!r},lambda:Path({str(p)!r}).write_text("test"))'
            for p in protected.iterdir()) + '\n' +
            f'denied("source-write",lambda:Path({str(source / "frozen-source-decoy")!r}).write_text("test"))\n' +
            f'denied("private-read",lambda:Path({str(private / "outside-allowlist")!r}).read_bytes())\n' +
            f'denied("symlink-write",lambda:Path({str(scratch / "link-to-protected")!r}).write_text("test"))\n' +
            f'denied("symlink-read",lambda:Path({str(scratch / "link-to-private")!r}).read_bytes())\n' +
            f'denied("inherited-fd",lambda:os.read({leaked_fd},1))\n' +
            f'denied("sibling-signal",lambda:os.kill({sibling.pid},signal.SIGUSR1))\n' +
            'for af in (socket.AF_INET,socket.AF_INET6):\n'
            ' for kind in (socket.SOCK_STREAM,socket.SOCK_DGRAM):\n'
            '  denied(f"socket-{af}-{kind}",lambda:socket.socket(af,kind))\n'
            f'Path({str(scratch / "valid-output")!r}).write_text("allowed")\n'
            'print(json.dumps(results))\n')
        result = execute('permissions', ['python3', probe], timeout=15)
        checks = json.loads(result.stdout) if result.outcome == 'success' else []
        steps[-1]['checks'] = checks
        steps[-1]['passed'] = (result.outcome == 'success' and len(checks) == 13 and
                               all(c['denied'] for c in checks) and not signal_record.exists() and
                               (scratch / 'valid-output').read_text() == 'allowed')

        parent_probe = source / 'parent-probe.py'
        parent_probe.write_text('import errno,os,signal\n'
                               'try: os.kill(os.getppid(),signal.SIGUSR1)\n'
                               'except OSError as e: print("denied" if e.errno==errno.EPERM else "unexpected")\n'
                               'else: print("allowed")\n')
        parent_host = out / 'sacrificial-parent.py'
        parent_host.write_text('import signal,subprocess,json\nreceived=[]\n'
                              'signal.signal(signal.SIGUSR1,lambda *_:received.append(True))\n'
                              f'p=subprocess.run({list(map(str,prefix + ["python3", parent_probe]))!r},capture_output=True,text=True,close_fds=True)\n'
                              'print(json.dumps({"returncode":p.returncode,"stdout":p.stdout,"stderr":p.stderr,"received":received}))\n')
        result = run(['/usr/bin/python3', parent_host], cwd=source, env=env, timeout=15)
        parent_check = json.loads(result.stdout) if result.outcome == 'success' else {}
        steps.append(dict(name='parent-signal', **result.summary(), result=parent_check,
                          passed=result.outcome == 'success' and parent_check.get('stdout') == 'denied\n'
                          and not parent_check.get('received')))

        # The private session is the supervised unit. This child retains stdout,
        # including when the leader exits, so a timeout must terminate both.
        descendant = source / 'descendant.py'
        descendant.write_text('import os,time\np=os.fork()\nif p: os._exit(0)\nprint(f"child-ready:{os.getpid()}",flush=True)\nwhile True: time.sleep(.1)\n')
        result = execute('timeout-descendant', ['python3', descendant], timeout=1)
        time.sleep(.1)
        steps[-1]['passed'] = (result.outcome == 'timeout' and result.stdout.startswith(b'child-ready:')
                               and not group_alive(result.pid))
        result = execute('bounded-output', ['python3', '-c', 'while True: print("x"*4096,flush=True)'],
                         timeout=10, max_output=65536)
        steps[-1]['passed'] = result.outcome == 'output_limit' and len(result.stdout) <= 65536
        c_source = source / 'probe.c'
        c_source.write_text('#include <stdio.h>\nint main(void){puts("C build works");return 0;}\n')
        result = execute('c-build', ['gcc', '-static', c_source, '-o', scratch / 'probe'])
        steps[-1]['passed'] = result.outcome == 'success'
        result = execute('c-execute', [scratch / 'probe'])
        steps[-1]['passed'] = result.outcome == 'success' and result.stdout == b'C build works\n'
        lean_source = source / 'Main.lean'
        lean_source.write_text('import Std\ndef main : IO Unit := IO.println "Lean build works"\n')
        result = execute('lean-build-execute', ['/usr/bin/time', '-v', 'lean', '-j1', '--run', lean_source], timeout=90,
                         address_space=8 * 1024**3)
        steps[-1]['passed'] = result.outcome == 'success' and result.stdout == b'Lean build works\n'
        import re
        measured = re.search(rb'Maximum resident set size \(kbytes\): (\d+)', result.stderr)
        steps[-1]['measured_max_rss_kib'] = int(measured[1]) if measured else None
        steps[-1]['passed'] = steps[-1]['passed'] and measured is not None
        unchanged = all(sha(Path(p)) == value for p, value in identities.items())
        passed = all(step.get('passed') for step in steps) and unchanged
        report = dict(status='pass' if passed else 'fail', checked_at_utc=datetime.now(timezone.utc).isoformat(),
                      steps=steps, protected_decoys_unchanged=unchanged, identities=identities,
                      lean_address_space_bytes=8 * 1024**3,
                      calibration='2/3/4 GiB failed Lean runtime startup; 6 GiB passed lean -j1 but failed lake startup; 8 GiB with fixed -j1 compiled the integrated native model.',
                      limitations=['Current agent tool hosts retain broader project access.',
                                   'Default nono runtime grants (including temporary paths) are inherited.',
                                   'Process checks cover disposable parent/sibling signals and a supervised process group.',
                                   'Detached sessions and all possible process-information channels are not covered.',
                                   'No external network service is contacted; socket creation is checked.'])
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2))
        return 0 if passed else 1
    finally:
        os.close(leaked_fd)
        sibling.terminate()
        sibling.wait(timeout=10)


if __name__ == '__main__':
    sys.exit(main())
