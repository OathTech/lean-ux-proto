"""Bounded command execution with private sessions and explicit output limits."""
from dataclasses import dataclass
import os
from pathlib import Path
import resource
import selectors
import signal
import subprocess
import time


@dataclass
class Execution:
    outcome: str
    returncode: int
    stdout: bytes
    stderr: bytes
    elapsed_seconds: float
    pid: int

    def summary(self):
        return dict(outcome=self.outcome, returncode=self.returncode,
                    stdout_bytes=len(self.stdout), stderr_bytes=len(self.stderr),
                    elapsed_seconds=self.elapsed_seconds, pid=self.pid)


def group_alive(pgid):
    """Ignore zombies, which cannot perform work or hold descriptors."""
    for path in Path('/proc').glob('[0-9]*/stat'):
        try:
            fields = path.read_text().rsplit(')', 1)[1].split()
            if int(fields[2]) == pgid and fields[0] != 'Z':
                return True
        except (OSError, ValueError, IndexError):
            continue
    return False


def run(command, *, cwd, env=None, input_data=b'', timeout=60,
        max_output=16 * 1024 * 1024, address_space=2 * 1024**3, cpu_seconds=120):
    """No shell; no inherited extra FDs. Limits include both output streams.

    A private process group is terminated even after its leader exits. The
    declared fixture checks descendants that remain in this group; detached
    sessions are not silently claimed to be covered by this supervision alone.
    """
    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2, 256 * 1024**2))
        if address_space:
            resource.setrlimit(resource.RLIMIT_AS, (address_space, address_space))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))

    started = time.monotonic()
    proc = subprocess.Popen([str(x) for x in command], cwd=cwd, env=env,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            close_fds=True, start_new_session=True, preexec_fn=limits)
    selector = selectors.DefaultSelector()
    streams = {'stdout': bytearray(), 'stderr': bytearray()}
    pending = memoryview(input_data)
    for stream, name in ((proc.stdout, 'stdout'), (proc.stderr, 'stderr')):
        os.set_blocking(stream.fileno(), False)
        selector.register(stream, selectors.EVENT_READ, name)
    os.set_blocking(proc.stdin.fileno(), False)
    if pending:
        selector.register(proc.stdin, selectors.EVENT_WRITE, 'stdin')
    else:
        proc.stdin.close()
    outcome = 'success'
    try:
        while selector.get_map() or proc.poll() is None:
            if time.monotonic() - started > timeout:
                outcome = 'timeout'
                break
            for key, _ in selector.select(timeout=min(0.1, timeout)):
                if key.data == 'stdin':
                    try:
                        sent = os.write(key.fd, pending[:65536])
                        pending = pending[sent:]
                    except BrokenPipeError:
                        pending = pending[:0]
                    if not pending:
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
                else:
                    chunk = os.read(key.fd, 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
                    else:
                        remaining = max_output - sum(map(len, streams.values()))
                        streams[key.data].extend(chunk[:max(0, remaining)])
                        if len(chunk) > remaining:
                            outcome = 'output_limit'
                            break
            if outcome != 'success':
                break
    finally:
        selector.close()
        # Kill the harness-owned group, never any caller/agent process group.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait(timeout=10)
        for stream in (proc.stdin, proc.stdout, proc.stderr):
            if not stream.closed:
                stream.close()
    if outcome == 'success' and proc.returncode:
        outcome = 'crash' if proc.returncode < 0 else 'command_failure'
    return Execution(outcome, proc.returncode, bytes(streams['stdout']), bytes(streams['stderr']),
                     time.monotonic() - started, proc.pid)
