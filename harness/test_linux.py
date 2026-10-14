"""Process/output contract checks; no modeled operations run on the host."""
from pathlib import Path
import sys
import tempfile
import time
import unittest

import os
from unittest import mock

from .linux import (ARTIFACTS, GUEST_VARIANTS, IDENTITY, KERNEL, LinuxRunError, _bounded_process, approved_kernel_identity,
                    kernel_identity, run_linux, verify_kernel)


class BoundedProcessTests(unittest.TestCase):
    def setUp(self):
        ARTIFACTS.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="capture-check-", dir=ARTIFACTS)
        self.path = Path(self.temp.name) / "output.log"

    def tearDown(self):
        self.temp.cleanup()

    def test_complete_output(self):
        result = _bounded_process([sys.executable, "-c", "print('hello')"], self.path, 5, 100)
        self.assertEqual(result, 0)
        self.assertEqual(self.path.read_text(), "hello\n")

    def test_oversized_output_is_bounded(self):
        with self.assertRaises(LinuxRunError) as result:
            _bounded_process([sys.executable, "-c", "print('x'*10000)"], self.path, 5, 128)
        self.assertEqual(result.exception.kind, "output_limit")
        self.assertEqual(self.path.stat().st_size, 128)

    def test_timeout_reaps_group_after_leader_exits(self):
        program = "import subprocess,sys; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']); print(p.pid,flush=True)"
        with self.assertRaises(LinuxRunError) as result:
            _bounded_process([sys.executable, "-c", program], self.path, 0.3, 128)
        self.assertEqual(result.exception.kind, "timeout")
        child = int(self.path.read_text())
        # A terminated orphan can briefly remain a zombie pending init's reap.
        status = Path(f"/proc/{child}/stat")
        deadline = time.monotonic() + 1
        while status.exists() and time.monotonic() < deadline:
            try:
                if status.read_text().split(") ", 1)[1].split()[0] == "Z":
                    break
            except FileNotFoundError:
                break
            time.sleep(0.01)
        if status.exists():
            self.assertEqual(status.read_text().split(") ", 1)[1].split()[0], "Z")


class GuestVariantTests(unittest.TestCase):
    def test_only_named_variants(self):
        # a negative control's guest build (D3's wait-0) is named, never free-form flags
        self.assertEqual(GUEST_VARIANTS["advance-wait-0"], ("-DADVANCE_WAIT_US=0", "-DADVANCE_ABSORB=0"))
        trace = {"version": 1, "id": "v", "ops": [{"op": "eventfd2", "init": 0, "flags": 0}]}
        with self.assertRaises(ValueError):
            run_linux([trace], ARTIFACTS / "never-created", guest_variant="-DADVANCE_WAIT_US=0")


class KernelIdentityTests(unittest.TestCase):
    """The identity check before a boot (harness.linux.verify_kernel): the
    selected build must be the approved oracle, or the build named by
    LEANUX_KERNEL_IDENTITY; "unchecked" is the loud opt-out. The kernel this
    test environment selects (LEANUX_KERNEL_DIR) need not be the oracle, so the
    comparisons use a mocked identity; only the parser and the computation
    touch real files."""
    A = "a" * 64
    B = "b" * 64

    def test_approved_identity_is_parsed_from_the_first_non_comment_line(self):
        self.assertRegex(approved_kernel_identity(), IDENTITY)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "identity.txt"
            path.write_text("# comment\n\n" + self.A + "\n" + self.B + "\n")
            self.assertEqual(approved_kernel_identity(path), self.A)
            path.write_text("# only a comment\n")
            with self.assertRaises(ValueError):
                approved_kernel_identity(path)
            path.write_text("not-an-identity\n")
            with self.assertRaises(ValueError):
                approved_kernel_identity(path)

    def test_identity_of_the_selected_build_is_computed(self):
        if not (KERNEL / "vmlinux").is_file():
            self.skipTest(f"no kernel build at {KERNEL}")
        self.assertRegex(kernel_identity(), IDENTITY)

    def test_the_approved_build_passes_and_is_recorded(self):
        with mock.patch("harness.linux.kernel_identity", return_value=self.A), \
             mock.patch("harness.linux.approved_kernel_identity", return_value=self.A), \
             mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("LEANUX_KERNEL_IDENTITY", None)
            record = verify_kernel("/k")
        self.assertEqual(record, {"kernel": "/k", "checked": True, "expected": self.A, "actual": self.A,
                                  "source": "identity-x86_64-net-choice.txt"})

    def test_another_build_is_refused_before_any_boot(self):
        with mock.patch("harness.linux.kernel_identity", return_value=self.B), \
             mock.patch("harness.linux.approved_kernel_identity", return_value=self.A), \
             mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("LEANUX_KERNEL_IDENTITY", None)
            with self.assertRaises(LinuxRunError) as caught:
                verify_kernel("/k")
        self.assertEqual(caught.exception.kind, "kernel_mismatch")
        self.assertIn(self.B, str(caught.exception))
        self.assertIn("LEANUX_KERNEL_DIR", str(caught.exception))

    def test_a_control_kernel_is_named_explicitly(self):
        with mock.patch("harness.linux.kernel_identity", return_value=self.B), \
             mock.patch.dict(os.environ, {"LEANUX_KERNEL_IDENTITY": self.B}):
            record = verify_kernel("/k")
            self.assertEqual((record["checked"], record["expected"], record["source"]), (True, self.B, "LEANUX_KERNEL_IDENTITY"))
        with mock.patch("harness.linux.kernel_identity", return_value=self.A), \
             mock.patch.dict(os.environ, {"LEANUX_KERNEL_IDENTITY": self.B}):
            with self.assertRaises(LinuxRunError):
                verify_kernel("/k")
        with mock.patch("harness.linux.kernel_identity", return_value=self.A), \
             mock.patch.dict(os.environ, {"LEANUX_KERNEL_IDENTITY": "approved"}):
            with self.assertRaises(LinuxRunError):   # neither an identity nor the opt-out
                verify_kernel("/k")

    def test_unchecked_is_loud_and_recorded(self):
        with mock.patch("harness.linux.kernel_identity", return_value=self.B), \
             mock.patch.dict(os.environ, {"LEANUX_KERNEL_IDENTITY": "unchecked"}), \
             mock.patch("sys.stderr") as stderr:
            record = verify_kernel("/k")
        self.assertEqual((record["checked"], record["actual"], record["source"]), (False, self.B, "unchecked"))
        self.assertTrue(any("UNCHECKED" in str(c) for c in stderr.write.call_args_list))

    def test_run_linux_refuses_another_build_before_taking_a_slot(self):
        trace = {"version": 1, "id": "v", "ops": [{"op": "eventfd2", "init": 0, "flags": 0}]}
        with tempfile.TemporaryDirectory(dir=ARTIFACTS) as tmp, \
             mock.patch("harness.linux.kernel_identity", return_value=self.B), \
             mock.patch("harness.linux.approved_kernel_identity", return_value=self.A), \
             mock.patch("harness.linux._run_locked", side_effect=AssertionError("a slot was taken")), \
             mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("LEANUX_KERNEL_IDENTITY", None)
            with self.assertRaises(LinuxRunError) as caught:
                run_linux([trace], Path(tmp) / "run")
            self.assertEqual(caught.exception.kind, "kernel_mismatch")


if __name__ == "__main__":
    unittest.main()


class ObservationOrder(unittest.TestCase):
    """wg_observe's datagrams keep arrival order within a peer session and
    are free across peers (pre-release review, finding 5)."""

    def test_within_session_order_kept_across_sessions_free(self):
        from harness.linux import attach_observed
        data = lambda idx, counter: '04000000' + idx.to_bytes(4, 'little').hex() + counter.to_bytes(8, 'little').hex()
        # one session (index 7): two data messages arriving counter 1 then 0 stay in that order
        a, b = [4, 16, 4, 0, data(7, 1)], [4, 16, 4, 0, data(7, 0)]
        # a second session (index 3) interleaved: it sorts to its own key, order inside it kept
        c, d = [4, 16, 4, 0, data(3, 5)], [4, 16, 4, 0, data(3, 4)]
        results = [{'id': 'o', 'observations': [{}]}]
        traces = [{'id': 'o', 'ops': [{'op': 'wg_observe'}]}]
        records = [{'id': 'o', 'index': 0, 'datagrams': [a, c, b, d], 'replies': [],
                    'stats': {k: 0 for k in ('tx_errors', 'tx_dropped', 'rx_frame_errors', 'rx_length_errors',
                                             'rx_packets', 'rx_bytes', 'tx_packets', 'tx_bytes')}}]
        attach_observed(results, traces, records)
        self.assertEqual(results[0]['observations'][0]['datagrams'], [c, d, a, b])

