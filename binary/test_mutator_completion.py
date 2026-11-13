"""A continued capture must finish the same complete workload, fail noisily otherwise."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from capture_index_mutator import finish_workload


class Remote:
    def __init__(self, reply=b'OK'):
        self.reply = reply
        self.socket = self
        self.closed = False

    def command(self, command):
        if command != 'D':
            raise AssertionError(command)
        return self.reply

    def close(self):
        self.closed = True


class Process:
    def __init__(self, code=0):
        self.code = code

    def wait(self, *, timeout):
        if timeout <= 0:
            raise AssertionError(timeout)
        return self.code


class CompletionTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.boot = Path(self.directory.name) / 'boot.log'
        self.trace = dict(id='sample', ops=[{}, {}])
        self.lines = ['LEANUX_COVERAGE {"id":"sample","index":0}',
                      'LEANUX_COVERAGE {"id":"sample","index":1}',
                      'LEANUX_BATCH_DONE traces=1 failures=0', 'LEANUX_GUEST_EXIT=0']
        self.write()

    def write(self):
        self.boot.write_text('\r\n'.join(self.lines) + '\r\n')

    def test_complete(self):
        remote = Remote()
        self.assertEqual(finish_workload(remote, Process(), self.boot, self.trace, 10),
                         dict(completedOperations=[0, 1], qemuReturncode=0))
        self.assertTrue(remote.closed)

    def test_refused_detach(self):
        with self.assertRaisesRegex(ValueError, 'refused detach'):
            finish_workload(Remote(b'E01'), Process(), self.boot, self.trace, 10)

    def test_failed_process(self):
        with self.assertRaisesRegex(ValueError, 'status 9'):
            finish_workload(Remote(), Process(9), self.boot, self.trace, 10)

    def test_missing_operation(self):
        self.lines.pop(1)
        self.write()
        with self.assertRaisesRegex(ValueError, 'every operation'):
            finish_workload(Remote(), Process(), self.boot, self.trace, 10)

    def test_missing_guest_exit(self):
        self.lines.pop()
        self.write()
        with self.assertRaisesRegex(ValueError, 'successful batch'):
            finish_workload(Remote(), Process(), self.boot, self.trace, 10)

    def test_different_trace(self):
        self.lines[0] = self.lines[0].replace('sample', 'different')
        self.write()
        with self.assertRaisesRegex(ValueError, 'isolated trace'):
            finish_workload(Remote(), Process(), self.boot, self.trace, 10)


if __name__ == '__main__':
    unittest.main()
