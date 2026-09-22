import copy
import json
from pathlib import Path
import unittest

from evaluator.generate import generate, identity, remove_operations
from evaluator.protocol import InvalidOutput, compare, parse_batch, validate_coverage
from evaluator.submission import ContractViolation, validate_submission
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

    def test_submission_controls(self):
        policy = json.loads((ROOT / 'contracts/submission-v1.json').read_text())
        identities = {key: 'a' * (40 if key == 'base_commit' else 64) for key in policy['required_identity_fields']}
        valid = dict(version=1, identities=identities, files={'Leanux/FS/Eventfd.lean': '-- valid text\n'})
        validate_submission(valid, identities, policy)
        for key in ('evaluator/protocol.py', 'contracts/trace-v1.md', 'Leanux/Proofs/Extra.lean',
                    'lakefile.toml', 'Leanux/FS/FileTypes.lean', 'Leanux/FS/a\x00.lean'):
            bad = dict(valid, files={key: '-- changed\n'})
            with self.assertRaises(ContractViolation):
                validate_submission(bad, identities, policy)
        with self.assertRaises(ContractViolation):
            validate_submission(dict(valid, files={'Leanux/FS/Eventfd.lean': '\ud800'}), identities, policy)
        for missing in (None, {}):
            with self.assertRaises(ContractViolation):
                validate_submission(dict(valid, identities=missing), missing, policy)

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
