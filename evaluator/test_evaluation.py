import copy
import json
from pathlib import Path
import re
import unittest

from evaluator.generate import generate, identity, remove_operations
from evaluator.protocol import InvalidOutput, compare, parse_batch, validate_coverage
from evaluator import check
from evaluator.check import control_flow
from harness.trace import validate_trace

ROOT = Path(__file__).resolve().parents[1]


class EvaluationChecks(unittest.TestCase):
    def setUp(self):
        self.trace = {'version': 1, 'id': 'check', 'ops': [{'op': 'eventfd2', 'init': 0, 'flags': 2048}]}
        self.result = {'version': 1, 'id': 'check', 'observations': [{'index': 0, 'ret': 8, 'errno': None, 'bytes': ''}], 'branches': []}

    def test_observation_controls(self):
        self.assertEqual(compare(self.trace, self.result, self.result)['outcome'], 'agreement')
        malformed = []
        for field, value in [('index', False), ('ret', True), ('errno', 9), ('bytes', 'a0')]:
            result = copy.deepcopy(self.result)
            result['observations'][0][field] = value
            malformed.append(json.dumps(result))
        malformed += ['{}', '{', json.dumps(self.result).replace('"version": 1', '"version": 1, "version": 1')]
        for output in malformed:
            with self.assertRaises(InvalidOutput):
                parse_batch([self.trace], output)
        with self.assertRaises(InvalidOutput):
            parse_batch([], '')
        with self.assertRaises(InvalidOutput):
            parse_batch([self.trace], '')

    def test_resource_failures_are_not_agreement(self):
        for error in (4, 5, 12, 14, 19, 23, 28, 38, 105, 512):
            result = copy.deepcopy(self.result)
            result['observations'][0].update(ret=-error, errno=error)
            self.assertEqual(compare(self.trace, result, result)['outcome'], 'environment_failure')
        result['observations'][0].update(ret=-24, errno=24)
        self.assertEqual(compare(self.trace, result, result)['outcome'], 'agreement')

    def test_coverage_controls(self):
        valid = [{'id': 'check', 'index': 0, 'count': 1, 'pcs': ['0xffffffff81000001']}]
        validate_coverage([self.trace], valid)
        for change in ({'index': False}, {'pcs': 'not-pcs'}, {'pcs': [None]}, {'count': 65535}, {'pcs': []}):
            altered = copy.deepcopy(valid)
            altered[0].update(change)
            with self.assertRaises(InvalidOutput):
                validate_coverage([self.trace], altered)

    CONFIG = {'files': ['fs/eventfd.c'], 'known_gaps': []}

    def decision(self, label, line, true, false, why_true=None, why_false=None):
        return {'label': label, 'file': 'fs/eventfd.c', 'line': line,
                'when_true': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in true],
                'when_false': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in false],
                'unobservable_true': why_true, 'unobservable_false': why_false}

    def control_flow_fixture(self):
        table = check.parse_decisions([
            self.decision('eventfd_read.short_buffer', 220, [(221, 221)], [(222, 222)], why_true='no_instrumentation'),
            self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)]),
            self.decision('eventfd_ctx_do_read.semaphore', 180, [], [], 'branch_free', 'branch_free')], self.CONFIG)
        instrumented = {'fs/eventfd.c:222', 'fs/eventfd.c:224', 'fs/eventfd.c:235'}
        functions = {'eventfd_read', 'eventfd_ctx_do_read'}
        witnesses = check.witness_table(table, instrumented, functions)
        loc = {f'0x{n}': [{'function': 'eventfd_read', 'source': f'/x/.deps/linux/fs/eventfd.c:{n}'}]
               for n in (221, 222, 224, 235)}
        loc['0x999'] = [{'function': 'kmalloc', 'source': '/x/.deps/linux/mm/slub.c:999'}]
        trace = {'version': 1, 'id': 'cf', 'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}]}
        def run(labels, lines):
            model = {'branches': [{'index': 0, 'label': l} for l in labels]}
            coverage = [{'id': 'cf', 'index': 0, 'count': len(lines), 'pcs': [f'0x{n}' for n in lines]}]
            return control_flow(trace, model, coverage, loc, self.CONFIG, table, witnesses, instrumented, functions)[0]
        return run

    def test_control_flow_controls(self):
        run = self.control_flow_fixture()
        ready = ['eventfd_read.short_buffer=0', 'eventfd_read.empty=0', 'eventfd_ctx_do_read.semaphore=1']
        self.assertEqual(run(ready, [222, 235]), [])
        # A wrong outcome, an unknown or malformed label, and no label at all are rejected.
        self.assertTrue(run(['eventfd_read.short_buffer=0', 'eventfd_read.empty=1'], [222, 235]))
        self.assertTrue(run(ready + ['made_up=1'], [222, 235]))
        self.assertTrue(run(['eventfd_read.empty'], [222, 235]))
        self.assertTrue(run([], [222, 235]))

    def test_control_flow_completeness(self):
        run = self.control_flow_fixture()
        # Omitting a decision whose witnesses Linux covered is rejected.
        self.assertTrue(run(['eventfd_read.short_buffer=0'], [222, 235]))
        # Coverage only outside anchored files, or inside a span but unknown to
        # the instrumentation map, is rejected.
        self.assertTrue(run(['eventfd_read.short_buffer=1'], [999]))
        self.assertTrue(run(['eventfd_read.short_buffer=1'], [221]))
        # Reporting both outcomes of a decision is rejected (no exemption).
        both = ['eventfd_read.short_buffer=0', 'eventfd_read.empty=0', 'eventfd_read.empty=1']
        self.assertTrue(run(both, [222, 224, 235]))

    def test_decision_table_controls(self):
        good = self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)])
        check.parse_decisions([good], self.CONFIG)
        broken = [
            [good, good],                                                        # duplicate label
            [self.decision('eventfd_read.empty', 223, [(224, 235)], [(235, 235)])],  # overlapping outcomes
            [self.decision('eventfd_read.empty', 223, [(100, 100)], [])],       # far from its condition
            [self.decision('eventfd_read.empty', 223, [(224, 9999)], [])],      # beyond the file
            [dict(good, unobservable_true=3)],                                   # malformed reason
            [dict(good, file='mm/slub.c')],                                      # unanchored file
        ]
        for table in broken:
            with self.assertRaises(InvalidOutput):
                check.parse_decisions(table, self.CONFIG)
        blank = [self.decision('eventfd_read.empty', 219, [(224, 224)], [])]  # line 219 is blank
        with self.assertRaises(InvalidOutput):
            check.parse_decisions(blank, self.CONFIG)

    def test_unobservable_reasons_match_the_binary(self):
        table = check.parse_decisions([self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)])], self.CONFIG)
        check.witness_table(table, {'fs/eventfd.c:224', 'fs/eventfd.c:235'}, {'eventfd_read'})
        # A side without witnesses needs a reason ...
        with self.assertRaises(InvalidOutput):
            check.witness_table(table, {'fs/eventfd.c:224'}, {'eventfd_read'})
        # ... a reason must not hide a witnessed side ...
        hidden = check.parse_decisions([self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)],
                                                      why_false='no_instrumentation')], self.CONFIG)
        with self.assertRaises(InvalidOutput):
            check.witness_table(hidden, {'fs/eventfd.c:224', 'fs/eventfd.c:235'}, {'eventfd_read'})
        # ... and the decision's C function must own instrumentation.
        with self.assertRaises(InvalidOutput):
            check.witness_table(table, {'fs/eventfd.c:224', 'fs/eventfd.c:235'}, {'eventfd_write'})

    def test_non_statement_lines_leave_spans(self):
        text = (check.SOURCE / 'fs/eventfd.c').read_text().splitlines()
        self.assertTrue(text[243].strip().startswith('return'))   # eventfd.c:244: a statement, kept
        self.assertFalse(check.non_statement('fs/eventfd.c:244'))
        self.assertTrue(check.non_statement('fs/eventfd.c:245'))   # closing brace
        self.assertTrue(check.non_statement('fs/eventfd.c:97'))    # comment continuation
        self.assertFalse(check.non_statement('fs/eventfd.c:180'))  # '*cnt = ...' is code

    def test_empty_run_is_not_a_pass(self):
        class Args:
            generated_count, seed, trace = 0, 0, None
        out = ROOT / '.cache' / 'tmp' / 'empty-report'
        out.mkdir(parents=True, exist_ok=True)
        status = check.write_report(out, [], {}, {}, None, None, 'now', [], Args)
        self.assertEqual(status, 'fail')
        (out / 'report.json').unlink()
        out.rmdir()

    def test_generator_and_reference_reduction(self):
        traces = generate(29, 1000)
        self.assertEqual(len({identity(t) for t in traces}), 1000)
        for trace in traces:
            validate_trace(trace)
            reduced = remove_operations(trace, [0, 2])
            if reduced['ops']:
                validate_trace(reduced)
        self.assertEqual(traces, generate(29, 1000))


if __name__ == '__main__':
    unittest.main()
