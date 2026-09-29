import copy
import json
from pathlib import Path
import unittest

from evaluator.generate import generate, identity, remove_operations
from evaluator.protocol import InvalidOutput, compare, parse_batch, validate_coverage
from evaluator.check import control_flow, load_anchors
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

    def test_control_flow_controls(self):
        anchors = load_anchors()
        trace = {'version': 1, 'id': 'cf', 'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}]}
        loc = {'0x1': [{'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:216'}],
               '0x2': [{'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:224'}],
               '0x3': [{'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:235 (discriminator 1)'}]}
        empty = [{'id': 'cf', 'index': 0, 'count': 2, 'pcs': ['0x1', '0x2']}]
        ready = [{'id': 'cf', 'index': 0, 'count': 2, 'pcs': ['0x1', '0x3']}]
        def model(*labels):
            return {'branches': [{'index': 0, 'label': label} for label in labels]}
        good = model('read.dispatch', 'eventfd_read.empty_nonblocking')
        self.assertEqual(control_flow(trace, good, empty, loc, anchors)[0], [])
        # A wrong arm, an unknown label and a missing label are all rejected.
        self.assertTrue(control_flow(trace, good, ready, loc, anchors)[0])
        self.assertTrue(control_flow(trace, model('read.dispatch', 'eventfd_read.ready'), empty, loc, anchors)[0])
        self.assertTrue(control_flow(trace, model('read.dispatch', 'made_up'), empty, loc, anchors)[0])
        self.assertTrue(control_flow(trace, model(), empty, loc, anchors)[0])
        self.assertTrue(control_flow(trace, model('read.bad_fd'), empty, loc, anchors)[0])

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
