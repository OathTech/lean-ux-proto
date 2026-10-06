"""Contract-boundary checks; no host experiment syscalls."""
from copy import deepcopy
from pathlib import Path
import json
import re
import unittest

from .trace import KCOV_CAPACITY, OPCODES, InvalidTrace, UnsupportedTrace, loads_trace, serialize_wire, validate_trace


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
            lambda t: t['ops'][1].update(count=17),
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
                         'LEANUX_WIRE_V2\n1\nD 0\nT case 3 32 0 0\n1 0 -1 0 -1 0 2048 0\n6 1 0 0 -1 8 0 18446744073709551615\n3 0 -2147483648 1 0 0 4294967295 0\n')

    def test_lifecycle_operations_and_bare_fixture(self):
        # L (docs/2026-10-05-l-lifecycle.md section 6): opcodes 15-17, the
        # bare fixture as the wire's net 2, only on network traces.
        self.assertEqual([OPCODES[n] for n in ("wg_create", "wg_down", "wg_delete")], [15, 16, 17])
        self.assertEqual(len(set(OPCODES.values())), len(OPCODES))
        trace = {"version": 1, "id": "life", "net_fixture": "bare",
                 "ops": [{"op": "wg_create"}, {"op": "wg_down"}, {"op": "wg_delete"}]}
        self.assertEqual(validate_trace(trace), trace)
        wire = serialize_wire([trace], dispatch=[1])
        self.assertIn("\nT life 3 32 2 0\n15 0 -1 0 -1 0 0 0\n16 0 -1 0 -1 0 0 0\n17 0 -1 0 -1 0 0 0\n", wire)
        del trace["net_fixture"]
        self.assertIn("\nT life 3 32 1 0\n", serialize_wire([trace], dispatch=[1]))
        for bad in ({"net_fixture": "wg0"}, {"net_fixture": True}, {"net_fixture": "bare", "ops": [{"op": "dup", "fd": {"literal": 8}}]}):
            with self.subTest(bad=bad):
                with self.assertRaises(InvalidTrace):
                    validate_trace(dict(trace, **bad))
        with self.assertRaises(InvalidTrace):
            validate_trace(dict(trace, ops=[{"op": "wg_create", "extra": 1}]))

    def test_guest_capacity_matches_host_bounds(self):
        guest = (Path(__file__).resolve().parent / "guest.c").read_text()
        match = re.search(r"#define CAPACITY \((\d+)UL \* 1024\)", guest)
        self.assertIsNotNone(match)
        self.assertEqual(int(match.group(1)) * 1024, KCOV_CAPACITY)


if __name__ == '__main__':
    unittest.main()
