"""Process/output contract checks; no modeled operations run on the host."""
from pathlib import Path
import sys
import tempfile
import time
import unittest

from .linux import ARTIFACTS, GUEST_VARIANTS, LinuxRunError, _bounded_process, run_linux


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


if __name__ == "__main__":
    unittest.main()
