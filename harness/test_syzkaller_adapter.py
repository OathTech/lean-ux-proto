"""Restricted syzkaller import checks; programs are never executed here."""
from pathlib import Path
import json
import unittest

from .syzkaller_adapter import SyzkallerImportError, import_program, parse_program
from .trace import validate_trace

TYPED = """# Saved sequential eventfd example
r0 = eventfd2(0x7, 0x80800)
r1 = dup(r0)
write$eventfd(r1, &(0x7f0000000080)=0x5, 0x8)
close(r0)
read$eventfd(r1, &(0x7f0000000100), 0x8)
fcntl$getflags(r1, 0x1)
fcntl$setflags(r1, 0x2, 0x1)
fcntl$getflags(r1, 0x3)
r2 = dup3(r1, 0x14, 0x80000)
close(r2)
"""


class SyzkallerAdapterTests(unittest.TestCase):
    def test_typed_program_import(self):
        result = parse_program(TYPED, "typed-import")
        self.assertEqual(len(result["ops"]), 10)
        self.assertEqual(result["ops"][2], {"op": "write", "fd": {"ref": 1}, "count": 8, "value": "5"})
        self.assertEqual(result["ops"][8], {"op": "dup3", "fd": {"ref": 1}, "newfd": {"literal": 20}, "flags": 524288})
        self.assertEqual(result["ops"][9]["fd"], {"ref": 8})

    def test_generic_buffers(self):
        text = 'r0 = eventfd2(0x0, 0x800)\nwrite(r0, &(0x7f0000000000)="00010000000000000000000000000000", 0x8)\nread(r0, &(0x7f0000000200)=""/16, 0x10)\n'
        result = parse_program(text, "generic-import")
        self.assertEqual(result['ops'][1]['value'], '256')
        self.assertEqual(result['ops'][2]['count'], 16)

    def test_fd_width_and_failed_reference_are_preserved(self):
        text = 'r0 = eventfd2(0x0, 0x802)\nr1 = dup(r0)\nclose(r1)\nclose(0xffffffffffffffff)\nclose(0x80000000)\n'
        operations = parse_program(text, 'width-import')['ops']
        self.assertEqual(operations[1]['fd'], {'ref': 0})
        self.assertEqual(operations[3]['fd'], {'literal': -1})
        self.assertEqual(operations[4]['fd'], {'literal': -2147483648})

    def test_rejects_unsupported_features_without_dropping_calls(self):
        suffixes = [
            'socket(0x2, 0x1, 0x0)',
            'dup(r0+0x1)',
            'dup(r0/0x2)',
            'dup(r4)',
            'r0 = dup(r0)',
            'r1 = close(r0)',
            'close(0x7)',
            'eventfd2(0x100000000, 0x800)',
            'read$eventfd(r0, 0x0, 0x8)',
            'read$eventfd(r0, &(0x7f0000000000)=0x1, 0x8)',
            'read$eventfd(r0, &(0x7f0001000000), 0x8)',
            'read$eventfd(r0, &AUTO, 0x8)',
            'write$eventfd(r0, &(0x7f0000000000), 0x8)',
            'write$eventfd(r0, &(0x7f0000000000)=r0, 0x8)',
            'read$eventfd(r0, &(0x7f0000000000), 0x11)',
            'read(r0, &(0x7f0000000000)=""/4, 0x8)',
            'write(r0, &(0x7f0000000000)="0", 0x0)',
            'write(r0, &(0x7f0000000000)="010000000000000001", 0x8)',
            'write(r0, &(0x7f0000000000)="0100", 0x8)',
            'fcntl$getflags(r0, 0x5)',
            'fcntl$setflags(r0, 0x4, 0x800)',
            'dup(r0) (async)',
            'dup(r0) (fail_nth: 1)',
        ]
        for suffix in suffixes:
            with self.subTest(suffix=suffix):
                record = import_program('r0 = eventfd2(0x0, 0x800)\n' + suffix + '\n', 'rejected')
                self.assertEqual(record['status'], 'rejected')
                self.assertNotIn('trace', record)
                self.assertEqual(record['reason']['line'], 2)

    def test_target_and_program_bounds(self):
        with self.assertRaises(SyzkallerImportError):
            parse_program(TYPED, 'target', target='linux/arm64')
        for text in ['', '# comment only', 'é', ' ' * 65537, 'eventfd2(0x0, 0x800)\n' * 65]:
            with self.subTest(text=text[:20]):
                self.assertEqual(import_program(text, 'bounds')['status'], 'rejected')

    def test_independent_corpus_dimensions(self):
        paths = sorted((Path(__file__).resolve().parents[1] / 'corpus/critic').glob('*.json'))
        self.assertEqual(len(paths), 32)
        traces = [validate_trace(json.loads(path.read_text())) for path in paths]
        self.assertEqual(len({json.dumps(t['ops'], sort_keys=True) for t in traces}), 32)
        for trace in traces:
            # Main object follows at least one unrelated allocation; its FD is not8.
            creations = [op for op in trace['ops'] if op['op'] == 'eventfd2']
            self.assertGreaterEqual(len(creations), 2)
            self.assertTrue(all(op['init'] > 1 for op in creations))


if __name__ == '__main__':
    unittest.main()
