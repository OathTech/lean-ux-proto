"""Contract-boundary checks; no host experiment syscalls."""
from copy import deepcopy
import hashlib
from pathlib import Path
import json
import os
import random
import shutil
import subprocess
import unittest

from .trace import InvalidTrace, UnsupportedTrace, loads_trace, serialize_wire, validate_trace

ROOT = Path(__file__).resolve().parents[1]


class TraceContractTests(unittest.TestCase):
    def setUp(self):
        self.trace = {"version": 1, "id": "case", "ops": [
            {"op": "eventfd2", "init": 0, "flags": 2048},
            {"op": "write", "fd": {"ref": 0}, "count": 8, "value": "18446744073709551615"},
        ]}

    def test_corpus_is_valid_and_ids_unique(self):
        paths = sorted((Path(__file__).resolve().parents[1] / "corpus/handwritten").glob("*.json"))
        traces = [loads_trace(path.read_text()) for path in paths]
        self.assertGreaterEqual(len(traces), 20)
        self.assertEqual(len({t['id'] for t in traces}), len(traces))
        self.assertTrue(serialize_wire(traces).startswith(f"LEANUX_WIRE_V2\n{len(traces)}\nD 0\n"))

    def test_accepts_phase4_domain(self):
        # Amended 2026-09-29: blocking creation and getter arguments are valid.
        trace = deepcopy(self.trace)
        trace['ops'][0].update(flags=0)
        trace['ops'].append({"op": "fcntl", "fd": {"ref": 0}, "cmd": "F_GETFD", "arg": 1})
        trace['ops'].append({"op": "fcntl", "fd": {"ref": 0}, "cmd": "F_GETFL", "arg": 4294967295})
        self.assertEqual(validate_trace(trace), trace)

    def test_rejects_normative_boundary_violations(self):
        mutations = [
            lambda t: t.update(version=True),
            lambda t: t.update(extra=1),
            lambda t: t.update(id="non ASCII é"),
            lambda t: t['ops'][0].update(init=2**32),
            lambda t: t['ops'][1].update(count=True),
            lambda t: t['ops'][1].update(count=69633),
            lambda t: t['ops'][1].update(value="18446744073709551616"),
            lambda t: t['ops'][1].update(value="00"),
            lambda t: t['ops'][1].update(value=0),
            lambda t: t['ops'][1].update(fd={"literal": 7}),
            lambda t: t['ops'][1].update(fd={"literal": -(2**31)-1}),
            lambda t: t['ops'][1].update(fd={"ref": 1}),
            lambda t: t['ops'][1].update(fd={"ref": 0, "literal": 8}),
            lambda t: t['ops'].append({"op": "close", "fd": {"ref": 1}}),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                trace = deepcopy(self.trace)
                mutation(trace)
                with self.assertRaises(InvalidTrace):
                    validate_trace(trace)

    def test_json_duplicates_and_constants_rejected(self):
        for text in ['{"version":1,"version":1}', 'NaN', 'Infinity', '{']:
            with self.assertRaises(InvalidTrace):
                loads_trace(text)

    def test_unsupported_is_explicit(self):
        self.trace['ops'].append({'op': 'socket'})
        with self.assertRaises(UnsupportedTrace):
            validate_trace(self.trace)

    def test_wire_preserves_widths_and_reference_modes(self):
        self.trace['ops'].append({'op': 'dup3', 'fd': {'literal': -2147483648}, 'newfd': {'ref': 0}, 'flags': 4294967295})
        self.assertEqual(serialize_wire([self.trace]),
                         'LEANUX_WIRE_V2\n1\nD 0\nT case 3 32 0 0\n1 0 -1 0 -1 0 2048 0 0\n6 1 0 0 -1 8 0 18446744073709551615 0\n3 0 -2147483648 1 0 0 4294967295 0 0\n')

    PIPES = {"version": 1, "id": "pipes", "ops": [
        {"op": "pipe2", "flags": 2048},
        {"op": "write", "fd": {"pipe": 0, "end": 1}, "count": 69632, "value": "7", "pause_ms": 5},
        {"op": "read", "fd": {"pipe": 0, "end": 0}, "count": 69632},
        {"op": "fcntl", "fd": {"pipe": 0, "end": 1}, "cmd": "F_SETPIPE_SZ", "arg": 4096},
        {"op": "dup3", "fd": {"pipe": 0, "end": 0}, "newfd": {"literal": 20}, "flags": 0},
        {"op": "fcntl", "fd": {"ref": 4}, "cmd": "F_GETPIPE_SZ", "arg": 0},
    ]}

    def test_pipes_contract(self):
        trace = validate_trace(self.PIPES)
        self.assertEqual(serialize_wire([trace]).splitlines()[3:], [
            'T pipes 6 32 0 0', '14 0 -1 0 -1 0 2048 0 0', '6 3 0 0 -1 69632 0 7 5', '5 2 0 0 -1 69632 0 0 0',
            '7 3 0 0 -1 1031 4096 0 0', '3 2 0 0 20 0 0 0 0', '7 1 4 0 -1 1032 0 0 0'])
        mutations = [
            lambda t: t['ops'][1].update(fd={"ref": 0}),                 # a ref may not name a pipe2
            lambda t: t['ops'][5].update(fd={"pipe": 4, "end": 0}),      # a pipe end must name a pipe2
            lambda t: t['ops'][1].update(fd={"pipe": 0, "end": 2}),
            lambda t: t['ops'][1].update(fd={"pipe": 1, "end": 0}),      # not earlier
            lambda t: t['ops'][1].update(fd={"pipe": 0}),
            lambda t: t['ops'][1].update(pause_ms=0),
            lambda t: t['ops'][1].update(pause_ms=21),
            lambda t: t['ops'][2].update(count=69633),
            lambda t: t['ops'][0].update(flags=-1),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                altered = deepcopy(self.PIPES)
                mutation(altered)
                with self.assertRaises(InvalidTrace):
                    validate_trace(altered)


@unittest.skipUnless(shutil.which("gcc"), "needs gcc")
class GuestHashTests(unittest.TestCase):
    """harness/guest.c's BLAKE2s-256 and write pattern, compiled on the host
    into a driver that includes the guest source with its main renamed; no
    trace operation runs (only the guest's pure helpers)."""

    DRIVER = r"""
#define main guest_main
#include "guest.c"
#undef main
int main(void)
{
    blake2s_self_test();
    static char text[2 * MAX_IO + 16];
    static unsigned char data[MAX_IO];
    while (fgets(text, sizeof(text), stdin)) {
        unsigned i, count;
        unsigned long long value;
        if (sscanf(text, "W %u %llu %u", &i, &value, &count) == 3) {
            fill_write_buffer(i, value, count);
            print_hex_bytes(write_buffer, count < 8 ? 8 : count);
            printf("\n");
            continue;
        }
        size_t n = strcspn(text, "\n") / 2;
        for (size_t k = 0; k < n; ++k) { unsigned b; sscanf(text + 2 * k, "%2x", &b); data[k] = (unsigned char)b; }
        unsigned char digest[32];
        blake2s256(data, n, digest);
        print_hex_bytes(digest, 32);
        printf("\n");
    }
    return 0;
}
"""

    @classmethod
    def setUpClass(cls):
        cls.dir = ROOT / ".cache" / "tmp" / f"guest-hash-{os.getpid()}"
        cls.dir.mkdir(parents=True, exist_ok=True)
        (cls.dir / "driver.c").write_text(cls.DRIVER)
        subprocess.run(["gcc", "-O2", "-Wall", "-Wextra", "-Werror", "-std=c11", "-I", str(ROOT / "harness"),
                        str(cls.dir / "driver.c"), "-o", str(cls.dir / "driver")], check=True)

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.dir)

    def run_driver(self, lines):
        out = subprocess.run([str(self.dir / "driver")], input="".join(l + "\n" for l in lines),
                             capture_output=True, text=True, check=True)
        return out.stdout.splitlines()

    def test_blake2s_matches_hashlib(self):
        rng = random.Random(3)
        sizes = [0, 1, 7, 8, 63, 64, 65, 127, 128, 129, 4095, 4096, 4097, 65536, 69632] + [rng.randrange(1, 69633) for _ in range(8)]
        inputs = [bytes(rng.randrange(256) for _ in range(n)) for n in sizes]
        self.assertEqual(self.run_driver([d.hex() for d in inputs]), [hashlib.blake2s(d).hexdigest() for d in inputs])

    def test_write_pattern(self):
        def pattern(i, value, count):
            return bytes(value >> (8 * k) & 0xff if k < 8 else (7 * i + 13 * k + 17 * (k >> 8)) % 256
                         for k in range(max(count, 8)))
        cases = [(0, 1, 8), (3, 2**64 - 1, 0), (63, 12345678901234567, 69632), (17, 5, 4097), (1, 0, 300)]
        self.assertEqual(self.run_driver([f"W {i} {v} {c}" for i, v, c in cases]),
                         [pattern(i, v, c).hex() for i, v, c in cases])


if __name__ == '__main__':
    unittest.main()
