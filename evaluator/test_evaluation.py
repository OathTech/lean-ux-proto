from unittest import mock
import os
import copy
from collections import Counter
import json
from pathlib import Path
import re
import unittest

from evaluator.generate import generate, identity, remove_operations
from evaluator.protocol import InvalidOutput, compare, parse_batch, validate_coverage
from evaluator import check
from evaluator.check import control_flow
from harness.trace import KCOV_CAPACITY, validate_trace

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

    def test_fired_timer_sections_field(self):
        # D3: the mirror's optional `fired` list, validated strictly
        result = dict(copy.deepcopy(self.result), fired=[{'index': 0, 'symbol': 'wg_expired_new_handshake'}])
        self.assertEqual(parse_batch([self.trace], json.dumps(result))[0]['fired'][0]['index'], 0)
        for fired in ([], [{'index': 1, 'symbol': 'wg_expired_new_handshake'}], [{'index': 0}],
                      [{'index': 0, 'symbol': 'Bad Symbol'}], {}):
            with self.assertRaises(InvalidOutput):
                parse_batch([self.trace], json.dumps(dict(copy.deepcopy(self.result), fired=fired)))

    def test_pipes_observation_fields(self):
        """P design section 6: a read's head and digest, a write's sigpipe, a
        pipe2's fds, on both sides (protocol) and on the Linux side
        (harness/linux.py, which also recomputes short reads' digests)."""
        import hashlib
        from harness.linux import _check_observation
        trace = {'version': 1, 'id': 'p', 'ops': [
            {'op': 'pipe2', 'flags': 2048},
            {'op': 'write', 'fd': {'pipe': 0, 'end': 1}, 'count': 100, 'value': '0'},
            {'op': 'read', 'fd': {'pipe': 0, 'end': 0}, 'count': 69632},
            {'op': 'read', 'fd': {'pipe': 0, 'end': 0}, 'count': 5},
            {'op': 'pipe2', 'flags': 1}]}
        head = bytes(range(100))
        result = {'version': 1, 'id': 'p', 'branches': [], 'observations': [
            {'index': 0, 'ret': 0, 'errno': None, 'bytes': '', 'fds': [8, 9]},
            {'index': 1, 'ret': 100, 'errno': None, 'bytes': '', 'sigpipe': 0},
            {'index': 2, 'ret': 100, 'errno': None, 'bytes': head[:64].hex(), 'digest': hashlib.blake2s(head).hexdigest()},
            {'index': 3, 'ret': 3, 'errno': None, 'bytes': 'aabbcc', 'digest': hashlib.blake2s(bytes.fromhex('aabbcc')).hexdigest()},
            {'index': 4, 'ret': -22, 'errno': 22, 'bytes': '', 'fds': None}]}
        self.assertEqual(compare(trace, result, result)['outcome'], 'agreement')
        _check_observation(copy.deepcopy(result), trace)
        broken = [
            (2, {'bytes': head.hex()}),                    # more than the 64-byte head
            (2, {'digest': None}),                         # a successful read without a digest
            (2, {'digest': 'AB' * 32}),
            (1, {'sigpipe': 2}),
            (1, {'sigpipe': True}),
            (0, {'fds': [8, 8]}),
            (0, {'fds': None}),
            (4, {'fds': [8, 9]}),                          # descriptors after a failure
        ]
        for index, change in broken:
            with self.subTest(change=change):
                altered = copy.deepcopy(result)
                altered['observations'][index].update(change)
                with self.assertRaises(InvalidOutput):
                    parse_batch([trace], json.dumps(altered))
                with self.assertRaises(ValueError):
                    _check_observation(altered, trace)
        for index, field in ((1, 'sigpipe'), (2, 'digest'), (0, 'fds')):
            altered = copy.deepcopy(result)
            del altered['observations'][index][field]
            with self.assertRaises(InvalidOutput):
                parse_batch([trace], json.dumps(altered))
        # Linux side only: a short read's digest is recomputed with hashlib,
        # and a read cannot return more than its count.
        for index, change in ((3, {'digest': hashlib.blake2s(b'x').hexdigest()}), (3, {'ret': 6, 'bytes': 'aa' * 6})):
            altered = copy.deepcopy(result)
            altered['observations'][index].update(change)
            with self.assertRaises(ValueError):
                _check_observation(altered, trace)
        # A semantic difference in a digest or sigpipe is a mismatch.
        for index, change in ((2, {'digest': '00' * 32}), (1, {'sigpipe': 1})):
            model = copy.deepcopy(result)
            model['observations'][index].update(change)
            self.assertEqual(compare(trace, result, model)['outcome'], 'semantic_mismatch')

    def test_guest_timeout_counts_pauses_and_bytes(self):
        # D3 merge: the budget is rounded to whole seconds (fixed waits plus
        # CONTENTION_FACTOR x compute), so the traces are long enough to show
        # each term: 50 pauses of 20 ms are slept in both children (2 s, not
        # scaled); 20 writes of 69632 bytes get 1 s/MiB per child, scaled.
        plain = [{'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}] * 50}]
        paused = [{'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8, 'pause_ms': 20}] * 50}]
        large = [{'ops': [{'op': 'write', 'fd': {'literal': 8}, 'count': 69632, 'value': '0'}] * 50}]
        self.assertEqual(check.guest_timeout(paused) - check.guest_timeout(plain), 2)
        self.assertGreater(check.guest_timeout(large), check.guest_timeout(plain) + 15)

    def test_resource_failures_are_not_agreement(self):
        for error in (4, 5, 14, 19, 23, 28, 38, 105, 512):
            result = copy.deepcopy(self.result)
            result['observations'][0].update(ret=-error, errno=error)
            self.assertEqual(compare(self.trace, result, result)['outcome'], 'environment_failure')
        result['observations'][0].update(ret=-24, errno=24)
        self.assertEqual(compare(self.trace, result, result)['outcome'], 'agreement')
        # A2: eventfd2's ENOMEM is compared (an allocation outcome the mirror
        # consumes), so a mirror that did not take the arm disagrees
        nomem = copy.deepcopy(self.result)
        nomem['observations'][0].update(ret=-12, errno=12)
        self.assertEqual(compare(self.trace, nomem, nomem)['outcome'], 'agreement')
        self.assertEqual(compare(self.trace, nomem, self.result)['outcome'], 'semantic_mismatch')

    def test_observe_without_device(self):
        # L: wg_observe's stats are null exactly when there is no wg0; any
        # other non-object is invalid.
        trace = {'version': 1, 'id': 'gone', 'ops': [{'op': 'wg_observe'}]}
        obs = {'version': 1, 'id': 'gone', 'branches': [], 'observations': [
            {'index': 0, 'ret': -11, 'errno': 11, 'bytes': '', 'datagrams': [], 'replies': [], 'stats': None}]}
        self.assertEqual(compare(trace, obs, obs)['outcome'], 'agreement')
        for bad in ([], 0, 'null'):
            altered = copy.deepcopy(obs)
            altered['observations'][0]['stats'] = bad
            with self.assertRaises(InvalidOutput):
                parse_batch([trace], json.dumps(altered))

    def test_coverage_controls(self):
        valid = [{'id': 'check', 'index': 0, 'count': 1, 'pcs': ['0xffffffff81000001']}]
        validate_coverage([self.trace], valid)
        for change in ({'index': False}, {'pcs': 'not-pcs'}, {'pcs': [None]}, {'count': 2 * (KCOV_CAPACITY - 1)}, {'pcs': []}):
            altered = copy.deepcopy(valid)
            altered[0].update(change)
            with self.assertRaises(InvalidOutput):
                validate_coverage([self.trace], altered)

    CONFIG = {'files': ['fs/eventfd.c'], 'functions': ['eventfd_read', 'eventfd_ctx_do_read'], 'known_gaps': [],
              'shared_exits': [], 'operand_exclusions': [], 'data_only_operations': [],
              'branch_free_functions': [], 'helper_cuts': []}

    def decision(self, label, line, true, false, terminal=None, repeatable=False):
        return {'label': label, 'file': 'fs/eventfd.c', 'line': line,
                'when_true': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in true],
                'when_false': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in false],
                'repeatable': repeatable, 'comparison': None, 'terminal': terminal or []}

    def control_flow_fixture(self):
        table = check.parse_decisions([
            self.decision('eventfd_read.short_buffer', 220, [(221, 221)], [(222, 222)]),
            self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)]),
            self.decision('eventfd_ctx_do_read.semaphore', 180, [], [])], self.CONFIG)
        instrumented = {'fs/eventfd.c:222', 'fs/eventfd.c:224', 'fs/eventfd.c:235'}
        functions = {'eventfd_read', 'eventfd_ctx_do_read'}
        witnesses = check.witness_table(table, instrumented, functions)
        loc = {f'0x{n}': [{'function': 'eventfd_read', 'source': f'/x/.deps/linux/fs/eventfd.c:{n}'}]
               for n in (221, 222, 224, 235)}
        loc['0x999'] = [{'function': 'kmalloc', 'source': '/x/.deps/linux/mm/slub.c:999'}]
        # eventfd.c:224 inlined into a function the configuration does not list
        loc['0x1224'] = [{'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:224'},
                         {'function': 'unlisted', 'source': '/x/.deps/linux/net/core/skbuff.c:1'}]
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

    def test_header_lines_count_only_through_inline_frames(self):
        from evaluator.coverage import attributable
        inlined = [{'function': 'fdput', 'source': '/x/.deps/linux/include/linux/file.h:63'},
                   {'function': '__sys_recvfrom', 'source': '/x/.deps/linux/net/socket.c:2235'}]
        merged = [{'function': '__sys_recvfrom', 'source': '/x/.deps/linux/include/linux/file.h:63'}]
        self.assertTrue(attributable(inlined))
        self.assertFalse(attributable(merged))

    def test_control_flow_rejects_unlisted_functions_in_c_files(self):
        run = self.control_flow_fixture()
        ready = ['eventfd_read.short_buffer=0', 'eventfd_read.empty=0', 'eventfd_ctx_do_read.semaphore=1']
        # An unlisted function running a span line of an anchored C file fails,
        # even when the line is mapped through a listed function.
        problems = run(ready, [222, 235, 1224])
        self.assertEqual([p['problem'] for p in problems],
                         ['span lines covered by an unlisted function', 'covered code outside the declared boundary'])

    def test_control_flow_rejects_unlisted_functions_outside_declared_spans(self):
        # Pre-release review, finding 1: an unlisted function covering an
        # anchored C line outside every declared span passed the span rule;
        # the boundary rule rejects it, naming the function and the line.
        run = self.control_flow_fixture()
        cells = dict(zip(run.__code__.co_freevars, (c.cell_contents for c in run.__closure__)))
        cells['loc']['0x999'] = [{'function': 'unlisted_function', 'source': '/x/.deps/linux/fs/eventfd.c:999'}]
        ready = ['eventfd_read.short_buffer=0', 'eventfd_read.empty=0', 'eventfd_ctx_do_read.semaphore=1']
        problems = run(ready, [222, 235, 999])
        self.assertEqual([p['problem'] for p in problems], ['covered code outside the declared boundary'])
        self.assertEqual(problems[0]['functions'], [{'function': 'unlisted_function', 'lines': ['fs/eventfd.c:999']}])
        # a helper cut named in the configuration is inside the boundary
        config = dict(self.CONFIG, helper_cuts=[{'function': 'unlisted_function', 'file': 'fs/eventfd.c',
                                                'note': 'a test cut'}])
        model = {'branches': [{'index': 0, 'label': l} for l in ready]}
        coverage = [{'id': 'cf', 'index': 0, 'count': 3, 'pcs': ['0x222', '0x235', '0x999']}]
        table = check.parse_decisions([
            self.decision('eventfd_read.short_buffer', 220, [(221, 221)], [(222, 222)]),
            self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)]),
            self.decision('eventfd_ctx_do_read.semaphore', 180, [], [])], config)
        instrumented = {'fs/eventfd.c:222', 'fs/eventfd.c:224', 'fs/eventfd.c:235'}
        functions = {'eventfd_read', 'eventfd_ctx_do_read'}
        witnesses = check.witness_table(table, instrumented, functions)
        trace = {'version': 1, 'id': 'cf', 'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}]}
        self.assertEqual(control_flow(trace, model, coverage, cells['loc'], config, table, witnesses,
                                      instrumented, functions)[0], [])

    def test_control_flow_requires_reached_functions(self):
        run = self.control_flow_fixture()
        # eventfd_read ran (222, 235) but the mirror reported only another function.
        problems = run(['eventfd_ctx_do_read.semaphore=1'], [222, 235])
        self.assertIn('Linux ran a decision function the mirror reported nothing in', [p['problem'] for p in problems])

    def test_branch_free_exemption_needs_the_allowlist(self):
        table = check.parse_decisions([self.decision('fls128.high_nonzero', 180, [], [])],
                                      self.CONFIG)
        check.witness_table(table, set(), set(), ['fls128'])
        with self.assertRaises(check.InvalidOutput):
            check.witness_table(table, set(), set(), [])

    def test_decision_table_controls(self):
        good = self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)])
        check.parse_decisions([good], self.CONFIG)
        broken = [
            [good, good],                                                        # duplicate label
            [self.decision('eventfd_read.empty', 223, [(224, 235)], [(235, 235)])],  # overlapping outcomes
            [self.decision('eventfd_read.empty', 223, [(100, 100)], [])],       # far from its condition
            [self.decision('eventfd_read.empty', 223, [(224, 9999)], [])],      # beyond the file
            [dict(good, unobservable_true='no_instrumentation')],               # retired field
            [dict(good, file='mm/slub.c')],                                      # unanchored file
        ]
        for table in broken:
            with self.assertRaises(InvalidOutput):
                check.parse_decisions(table, self.CONFIG)
        blank = [self.decision('eventfd_read.empty', 219, [(224, 224)], [])]  # line 219 is blank
        with self.assertRaises(InvalidOutput):
            check.parse_decisions(blank, self.CONFIG)

    def test_witnesses_come_from_the_binary(self):
        table = check.parse_decisions([self.decision('eventfd_read.empty', 223, [(224, 224)], [(235, 235)])], self.CONFIG)
        witnesses = check.witness_table(table, {'fs/eventfd.c:224'}, {'eventfd_read'})
        self.assertEqual(witnesses['eventfd_read.empty'], {True: {'fs/eventfd.c:224'}, False: set()})
        # The decision's C function must own instrumentation.
        with self.assertRaises(InvalidOutput):
            check.witness_table(table, {'fs/eventfd.c:224', 'fs/eventfd.c:235'}, {'eventfd_write'})

    def test_non_statement_lines_leave_spans(self):
        text = (check.SOURCE / 'fs/eventfd.c').read_text().splitlines()
        self.assertTrue(text[243].strip().startswith('return'))   # eventfd.c:244: a statement, kept
        self.assertFalse(check.non_statement('fs/eventfd.c:244'))
        self.assertTrue(check.non_statement('fs/eventfd.c:245'))   # closing brace
        self.assertTrue(check.non_statement('fs/eventfd.c:97'))    # comment continuation
        self.assertFalse(check.non_statement('fs/eventfd.c:180'))  # '*cnt = ...' is code

    def test_operand_matching(self):
        match = check.operands_match
        lt_const = {'rel': 'lt', 'const_rhs': True}
        ge_var = {'rel': 'ge', 'const_rhs': False}
        eq_const = {'rel': 'eq', 'const_rhs': True}
        self.assertTrue(match(9, 32, (4, 9, 32), ge_var))              # non-constant: either order
        self.assertTrue(match(9, 32, (4, 32, 9), ge_var))
        self.assertFalse(match(9, 31, (4, 9, 32), ge_var))
        self.assertTrue(match(8, 8, (7, 8, 8), lt_const))              # x < 8 recorded as x < 8 ...
        self.assertTrue(match(8, 8, (7, 7, 8), lt_const))              # ... or as x <= 7
        self.assertFalse(match(8, 8, (7, 9, 8), lt_const))             # but not x <= 9
        self.assertFalse(match(9, 8, (7, 8, 8), lt_const))             # the variable must match exactly
        self.assertFalse(match(8, 8, (6, 7, 8), lt_const))             # shifts only for constant records
        self.assertFalse(match(8, 8, (7, 8, 8), ge_var))               # constant record, no declared constant
        self.assertFalse(match(0, 1, (5, 0, 0), eq_const))             # equality: no shift
        self.assertTrue(match(-1, 0, (5, 0, 0xffffffff), {'rel': 'lt', 'const_rhs': True}))  # negative, 4 bytes
        self.assertFalse(match(0x100, 0, (1, 0, 0), {'rel': 'flag', 'const_rhs': True}))    # does not fit 1 byte

    def test_operand_agreement(self):
        cmp = {'rel': 'ge', 'const_rhs': False, 'site': None}
        decisions = {'alloc_fd.at_limit': dict(site='fs/file.c:514', comparison=cmp),
                     'alloc_fd.o_cloexec': dict(site='fs/file.c:532', comparison=None)}
        loc = {'0x1': [{'function': 'alloc_fd', 'source': '/x/.deps/linux/fs/file.c:514'}],
               '0x2': [{'function': 'alloc_fd', 'source': '/x/.deps/linux/fs/file.c:506'}],
               '0x3': [{'function': 'helper', 'source': '/x/.deps/linux/include/linux/x.h:9'},
                       {'function': 'alloc_fd', 'source': '/x/.deps/linux/fs/file.c:514'}]}
        trace = {'ops': [{'op': 'dup'}]}
        def run(branch, records):
            model = {'branches': [dict(index=0, **branch)]}
            return check.operand_agreement(trace, model, [{'records': records}], loc, decisions)
        at_limit = dict(label='alloc_fd.at_limit=0', operands=[8, 32])
        self.assertEqual(run(at_limit, [[4, '0x8', '0x20', '0x1']]), ([], 1))
        self.assertTrue(run(dict(at_limit, operands=[8, 33]), [[4, '0x8', '0x20', '0x1']])[0])  # wrong operand
        self.assertTrue(run(at_limit, [[4, '0x8', '0x20', '0x2']])[0])    # comparison at another line only
        self.assertTrue(run(at_limit, [[4, '0x8', '0x20', '0x3']])[0])    # only in an inlined helper
        self.assertTrue(run(at_limit, [])[0])                             # no comparison recorded
        self.assertTrue(run(dict(label='alloc_fd.at_limit=0'), [[4, '0x8', '0x20', '0x1']])[0])   # operands omitted
        self.assertTrue(run(dict(label='alloc_fd.o_cloexec=0', operands=[0, 0]), [])[0])         # undeclared
        self.assertEqual(run(dict(label='made_up=1', operands=[1, 2]), []), ([], 0))             # left to control_flow

    def test_two_declared_comparisons_cannot_share_one_kernel_comparison(self):
        # The mutation campaign's finding 2 (2026-10-14): setfl's `&&` declares
        # two decisions at one condition line; a mirror evaluating the second
        # test when Linux skipped it reported a pair that matched the single
        # kernel row the first test left. A C comparison is an instruction:
        # distinct decisions must match distinct PCs.
        cmp = {'rel': 'flag', 'const_rhs': True, 'site': None}
        decisions = {'setfl.o_append_changed': dict(site='fs/fcntl.c:48', comparison=cmp),
                     'setfl.is_append': dict(site='fs/fcntl.c:48', comparison=cmp)}
        loc = {'0x1': [{'function': 'do_fcntl', 'source': '/x/.deps/linux/fs/fcntl.c:48'}],
               '0x2': [{'function': 'do_fcntl', 'source': '/x/.deps/linux/fs/fcntl.c:48'}]}
        trace = {'ops': [{'op': 'fcntl'}]}
        both = {'branches': [dict(index=0, label='setfl.o_append_changed=0', operands=[0, 0]),
                             dict(index=0, label='setfl.is_append=0', operands=[0, 0])]}
        one_row = [{'records': [[5, '0x0', '0x0', '0x1']]}]
        problems, _ = check.operand_agreement(trace, both, one_row, loc, decisions)
        self.assertEqual([p['problem'] for p in problems], ['two declared comparisons matched one kernel comparison'])
        two_rows = [{'records': [[5, '0x0', '0x0', '0x1'], [5, '0x0', '0x0', '0x2']]}]
        self.assertEqual(check.operand_agreement(trace, both, two_rows, loc, decisions)[0], [])

    def test_operand_agreement_matches_within_the_branch_section(self):
        # The mutation campaign's finding 4: a branch stamped with a NET_RX
        # section ordinal matches only the records the guest tagged with that
        # section's block, and a branch outside any section only records
        # outside the NET_RX blocks.
        cmp = {'rel': 'ge', 'const_rhs': False, 'site': None}
        decisions = {'wg_packet_rx_poll.counter': dict(site='drivers/net/wireguard/receive.c:300', comparison=cmp)}
        loc = {'0x1': [{'function': 'wg_packet_rx_poll',
                        'source': '/x/.deps/linux/drivers/net/wireguard/receive.c:300'}]}
        trace = {'id': 't', 'ops': [{'op': 'wg_inject'}]}
        sections = {('t', 0): {3: 1}}   # dispatch block 3 is NET_RX section 1
        def run(section, block):
            branch = dict(index=0, label='wg_packet_rx_poll.counter=1', operands=[8, 32])
            if section:
                branch['section'] = section
            records = [{'records': [[4, '0x8', '0x20', '0x1', block]]}]
            return check.operand_agreement(trace, {'branches': [branch]}, records, loc, decisions, sections=sections)
        self.assertEqual(run(1, '3'), ([], 1))
        self.assertTrue(run(1, '2')[0])          # the record lies in another block
        self.assertTrue(run(0, '3')[0])          # a branch outside any section cannot use a NET_RX block's record
        self.assertEqual(run(0, '2'), ([], 1))
        self.assertEqual(check.operand_agreement(trace, {'branches': [dict(index=0, label='wg_packet_rx_poll.counter=1',
                                                                            operands=[8, 32])]},
                                                 [{'records': [[4, '0x8', '0x20', '0x1', '3']]}], loc, decisions),
                         ([], 1))                # without the map, the old relation

    def test_decision_after_the_function_returned(self):
        # The mutation campaign's finding 3: a removed early return makes the
        # mirror report a decision past the point where Linux returned, which
        # no witness shows when that outcome is unwitnessed. After a terminal
        # outcome the function's next decision is a new call, from the top.
        table = check.parse_decisions([
            self.decision('eventfd_read.short_buffer', 220, [(221, 221)], [(222, 222)], terminal=[True], repeatable=True),
            self.decision('eventfd_read.empty', 223, [], [(224, 224)], terminal=[True], repeatable=True)], self.CONFIG)
        instrumented = {'fs/eventfd.c:221', 'fs/eventfd.c:222', 'fs/eventfd.c:224'}
        functions = {'eventfd_read'}
        witnesses = check.witness_table(table, instrumented, functions)
        loc = {f'0x{n}': [{'function': 'eventfd_read', 'source': f'/x/.deps/linux/fs/eventfd.c:{n}'}]
               for n in (221, 222, 224)}
        trace = {'version': 1, 'id': 'tr', 'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}]}
        def run(labels, lines):
            model = {'branches': [{'index': 0, 'label': l} for l in labels]}
            coverage = [{'id': 'tr', 'index': 0, 'count': len(lines), 'pcs': [f'0x{n}' for n in lines]}]
            return control_flow(trace, model, coverage, loc, self.CONFIG, table, witnesses, instrumented, functions)[0]
        self.assertEqual(run(['eventfd_read.short_buffer=1'], [221]), [])
        self.assertEqual([p['problem'] for p in run(['eventfd_read.short_buffer=1', 'eventfd_read.empty=1'], [221])],
                         ['decision reported after the function returned'])
        # a second call after the return starts from the top
        self.assertEqual(run(['eventfd_read.short_buffer=1', 'eventfd_read.short_buffer=0', 'eventfd_read.empty=0'],
                             [221, 222, 224]), [])

    def test_section_agreement_two_runs(self):
        # W7 stream H (13.2 (ii), T1): the (c') placement of an inline NAPI
        # poll changes the operands inside that poll's NET_RX section and of
        # the enqueue's put right after it. Linux's remote comparison
        # records carry their block (fifth element), the mirror's branches
        # their NET_RX section ordinal; each open poll's span agrees under
        # one run, everything else is the same in both runs and agrees.
        cmp = {'rel': 'ge', 'const_rhs': False, 'site': None}
        decisions = {'poll.refcount': dict(site='net/x.c:10', comparison=cmp),
                     'put.refcount': dict(site='net/x.c:30', comparison=cmp),
                     'task.cmp': dict(site='fs/y.c:20', comparison=cmp)}
        loc = {'0x1': [{'function': 'poll', 'source': '/x/.deps/linux/net/x.c:10'}],
               '0x2': [{'function': 'task', 'source': '/x/.deps/linux/fs/y.c:20'}],
               '0x3': [{'function': 'worker', 'source': '/x/.deps/linux/net/x.c:30'}]}
        trace = {'id': 't', 'ops': [{'op': 'wg_inject'}]}
        # blocks 1 and 3 are NET_RX sections (ordinals 1, 2); block 2 is the worker's
        sections = {('t', 0): {1: 1, 3: 2}}
        def run(poll1, put1, poll2, put2, task=(7, 9), ambiguous=2):
            return {'branches': [dict(index=0, label='task.cmp=0', operands=list(task)),
                                 dict(index=0, label='poll.refcount=1', operands=list(poll1), section=1),
                                 dict(index=0, label='put.refcount=1', operands=list(put1)),
                                 dict(index=0, label='task.cmp=0', operands=list(task)),   # the next item's work
                                 dict(index=0, label='poll.refcount=1', operands=list(poll2), section=2),
                                 dict(index=0, label='put.refcount=1', operands=list(put2))],
                    'observations': [{'ret': 0}], 'napi_irq_ambiguous': ambiguous}
        after, before = run((1, 2), (3, 2), (1, 2), (3, 2)), run((1, 3), (2, 1), (1, 3), (2, 1))
        # Linux: poll 1 after the put (block 1: 1 vs 2; the worker's put 3 vs 2),
        # poll 2 before it (block 3: 1 vs 3; its put 2 vs 1)
        linux = {'records': [[4, '0x7', '0x9', '0x2'], [4, '0x1', '0x2', '0x1', '1'], [4, '0x3', '0x2', '0x3', '2'],
                             [4, '0x1', '0x3', '0x1', '3'], [4, '0x2', '0x1', '0x3', '2']]}
        # poll 1 after the put, poll 2 before it: the selection the caller
        # replays as the mirror's vector
        self.assertEqual(check.section_agreement(trace, [after, before], [linux], sections, loc, decisions),
                         ([], [2], [False, True]))
        # poll 2's section under the before-put run but its put under the
        # after-put one is no execution: the span is taken as a whole
        mixed = {'records': linux['records'][:4] + [[4, '0x3', '0x2', '0x3', '2']]}
        self.assertTrue(check.section_agreement(trace, [after, before], [mixed], sections, loc, decisions)[0])
        # neither placement matches poll 1: the trace fails
        wrong = {'records': [linux['records'][0], [4, '0x1', '0x5', '0x1', '1']] + linux['records'][2:]}
        self.assertTrue(check.section_agreement(trace, [after, before], [wrong], sections, loc, decisions)[0])
        # the runs differ where no placement reaches: independence failed
        elsewhere = run((1, 3), (2, 1), (1, 3), (2, 1), task=(7, 8))
        problems, _, _ = check.section_agreement(trace, [after, elsewhere], [linux], sections, loc, decisions)
        self.assertTrue(any(p['label'] == 'napi placement' for p in problems))
        # a control-flow difference between the runs is never accepted
        shifted = dict(before, branches=before['branches'][1:] + before['branches'][:1])
        problems, _, _ = check.section_agreement(trace, [after, shifted], [linux], sections, loc, decisions)
        self.assertTrue(any(p['label'] == 'napi placement' for p in problems))
        # a record outside its section's block does not serve it
        moved = {'records': [linux['records'][0], linux['records'][1], linux['records'][2],
                             [4, '0x1', '0x3', '0x1', '2'], linux['records'][4]]}
        problems, _, _ = check.section_agreement(trace, [after, before], [moved], sections, loc, decisions)
        self.assertTrue(any(p['problem'] == 'no comparison recorded at condition' for p in problems))

    def test_selected_placement_replay_compares_per_section(self):
        # The selected placement's replay (419872d) is one execution of the
        # placement runs: a before-put placement runs the poll's NET_RX
        # section before the worker's put, so the flat branch order differs
        # from the after-put run while the control flow per section is the
        # same; that, the open polls and the returns are what the replay must
        # share (int-r: rx_duplicate with the vector [True] was rejected
        # against the after-put run's flat order).
        def run(order):
            branches = {'task': dict(index=4, label='task.cmp=0', operands=[7, 9]),
                        'poll': dict(index=4, label='poll.refcount=1', operands=[1, 3], section=1),
                        'put': dict(index=4, label='put.refcount=1', operands=[2, 1]),
                        'put2': dict(index=4, label='put.refcount=0', operands=[0, 1])}
            return {'branches': [dict(branches[k]) for k in order], 'observations': [{'ret': 0}],
                    'napi_irq_ambiguous': 1}
        after = run(['task', 'put', 'put2', 'poll'])
        selected = run(['task', 'poll', 'put', 'put2'])   # the vector [True]: the poll before the put
        self.assertEqual(check.placement_shape(after), check.placement_shape(selected))
        self.assertIsNone(check.replay_problem(selected, after, 1))
        self.assertIsNone(check.replay_problem(after, after, 1))
        # a different branch, order within a section, poll count or return is not an execution of the runs
        self.assertTrue(check.replay_problem(run(['task', 'poll', 'put2', 'put']), after, 1))
        changed = run(['task', 'poll', 'put', 'put2'])
        changed['branches'][1]['label'] = 'poll.refcount=0'
        self.assertTrue(check.replay_problem(changed, after, 1))
        self.assertTrue(check.replay_problem(selected, after, 2))
        self.assertTrue(check.replay_problem(dict(selected, observations=[{'ret': -1}]), after, 1))

    def test_netrx_sections_from_the_remote_rows(self):
        # the comparison child's remote rows, in area order: block numbers
        # count every section start; NET_RX blocks get ordinals by sequence
        start = check.SECTION_START
        netrx, worker = 0xabc, 0xdef
        def rec(kind, seq, func):
            return [kind, '0x0', seq, 16, func.to_bytes(8, 'little').hex() + '00' * 8]
        rows = [{'id': 't', 'index': 0, 'mode': 'cmp', 'stream': 'remote',
                 'records': [rec(start, 30, netrx), [check.SECTION_STOP, '0x0', 31, 8, '00' * 8],   # block 1, later
                             rec(start, 10, worker), [check.SECTION_STOP, '0x0', 40, 8, '00' * 8],   # block 2
                             rec(start, 20, netrx), [check.SECTION_STOP, '0x0', 21, 8, '00' * 8]]},  # block 3, earlier
                {'id': 't', 'index': 0, 'mode': 'pc', 'stream': 'remote', 'records': [rec(start, 1, netrx)]}]
        self.assertEqual(check.netrx_sections(rows, {netrx: 'net_rx_action', worker: 'wg_packet_decrypt_worker'}),
                         {('t', 0): {3: 1, 1: 2}})

    def test_operand_exclusion_is_one_call_site(self):
        # A declared exclusion (kcov.json operand_exclusions) stands for a
        # Linux comparison at the condition line whose outermost frame is the
        # declared call line; nothing else is accepted without operands. The
        # guest keeps one row per (kind, operands, PC), so two reports of one
        # exclusion may share one row (epoll stream S: a recursive walk
        # meeting the same two counters twice).
        cmp = {'rel': 'eq', 'const_rhs': True, 'site': None}
        decisions = {'__refcount_add.old_zero': dict(site='include/linux/refcount.h:189', comparison=cmp),
                     'alloc_fd.o_cloexec': dict(site='fs/file.c:532', comparison=None)}
        inner = {'function': '__refcount_add', 'source': '/x/.deps/linux/include/linux/refcount.h:189'}
        loc = {'0x1': [inner, {'function': 'alloc_pipe_info', 'source': '/x/.deps/linux/fs/pipe.c:794'}],
               '0x2': [inner, {'function': 'alloc_pipe_info', 'source': '/x/.deps/linux/fs/pipe.c:830'}]}
        exclusions = [{'label': '__refcount_add.old_zero', 'operand': 'root_user.__count', 'call': 'fs/pipe.c:794',
                       'note': ''}]
        trace = {'ops': [{'op': 'pipe2'}]}
        def run(branches, records):
            model = {'branches': [dict(index=0, **b) for b in branches]}
            excluded = Counter()
            problems, checked = check.operand_agreement(trace, model, [{'records': records}], loc, decisions,
                                                        None, exclusions, excluded)
            return problems, checked, sum(excluded.values())
        at_call = [5, '0x0', '0x1a', '0x1']
        elsewhere = [5, '0x0', '0x1a', '0x2']
        ok = dict(label='__refcount_add.old_zero=0', operands_excluded='root_user.__count')
        self.assertEqual(run([ok], [at_call]), ([], 0, 1))
        self.assertTrue(run([ok], [elsewhere])[0])                     # the comparison at another call site
        self.assertTrue(run([ok], [])[0])                              # no comparison recorded
        self.assertEqual(run([ok, ok], [at_call]), ([], 0, 2))         # two exclusions, one deduplicated row
        self.assertTrue(run([dict(ok, operands_excluded='nr_files')], [at_call])[0])     # undeclared operand
        self.assertTrue(run([dict(ok, operands=[2, 0])], [at_call])[0])                  # both forms at once
        self.assertTrue(run([dict(label='alloc_fd.o_cloexec=0', operands_excluded='root_user.__count')], [])[0])
        self.assertTrue(run([dict(label='__refcount_add.old_zero=0')], [at_call])[0])    # plain omission

    def test_shared_exit_needs_the_early_return_path(self):
        # A declared shared exit (kcov.json shared_exits) does not count its
        # helper as having run, but only when the block entering the helper
        # (unless_covered) was not covered in the operation.
        decisions = {'file_end_write.not_regular': dict(function='file_end_write'),
                     'vfs_write.not_fmode_write': dict(function='vfs_write')}
        loc = {'0xa': [{'function': 'vfs_write', 'source': '/x/.deps/linux/fs/read_write.c:667'}],
               '0xb': [{'function': 'vfs_write', 'source': '/x/.deps/linux/fs/read_write.c:691'}],
               '0xc': [{'function': 'file_end_write', 'source': '/x/.deps/linux/include/linux/fs.h:3018 (discriminator 1)'},
                       {'function': 'vfs_write', 'source': '/x/.deps/linux/fs/read_write.c:691 (discriminator 1)'}]}
        config = {'files': ['fs/read_write.c', 'include/linux/fs.h'], 'functions': ['vfs_write'],
                  'shared_exits': [{'function': 'file_end_write',
                                    'frames': ['include/linux/fs.h:3018', 'fs/read_write.c:691'],
                                    'unless_covered': ['fs/read_write.c:691'], 'note': ''}]}
        early = check.decision_functions_run({'pcs': ['0xa', '0xc']}, loc, config, decisions)
        self.assertEqual(early, ({'vfs_write'}, 1))
        full = check.decision_functions_run({'pcs': ['0xa', '0xb', '0xc']}, loc, config, decisions)
        self.assertEqual(full, ({'vfs_write', 'file_end_write'}, 0))
        undeclared = check.decision_functions_run({'pcs': ['0xa', '0xc']}, loc, dict(config, shared_exits=[]),
                                                  decisions)
        self.assertEqual(undeclared, ({'vfs_write', 'file_end_write'}, 0))

    def test_shared_exit_witnesses_nothing_on_the_early_return_path(self):
        # The merged-return-block class (int-r: file_update_time's "nothing"
        # return shares its block with the inlined __file_update_time, whose
        # frame at the call line witnesses the opposite outcome): a declared
        # shared exit reached by an early return neither counts as the helper
        # running nor witnesses an outcome; with the entering block covered,
        # or undeclared, it does both.
        config = {'files': ['fs/eventfd.c'], 'functions': ['eventfd_read'], 'known_gaps': [], 'data_only_operations': [],
                  'shared_exits': [{'function': 'helper', 'frames': ['fs/eventfd.c:230', 'fs/eventfd.c:222'],
                                    'unless_covered': ['fs/eventfd.c:231', 'fs/eventfd.c:222'], 'note': ''}],
                  'operand_exclusions': []}
        table = check.parse_decisions([self.decision('eventfd_read.short_buffer', 220, [(221, 221)], [(222, 222)])],
                                      config)
        instrumented = {'fs/eventfd.c:221', 'fs/eventfd.c:222'}
        witnesses = check.witness_table(table, instrumented, {'eventfd_read'})
        loc = {'0xa': [{'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:221'}],
               '0xs': [{'function': 'helper', 'source': '/x/.deps/linux/fs/eventfd.c:230'},
                       {'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:222'}],
               '0xe': [{'function': 'helper', 'source': '/x/.deps/linux/fs/eventfd.c:231'},
                       {'function': 'eventfd_read', 'source': '/x/.deps/linux/fs/eventfd.c:222'}]}
        trace = {'version': 1, 'id': 'se', 'ops': [{'op': 'read', 'fd': {'literal': 8}, 'count': 8}]}
        def run(pcs, cfg=config):
            model = {'branches': [{'index': 0, 'label': 'eventfd_read.short_buffer=1'}]}
            coverage = [{'id': 'se', 'index': 0, 'count': len(pcs), 'pcs': pcs}]
            problems, gaps = control_flow(trace, model, coverage, loc, cfg, table, witnesses, instrumented,
                                          {'eventfd_read'})
            return [p['problem'] for p in problems], gaps
        self.assertEqual(check.shared_exit_points({'pcs': ['0xa', '0xs']}, loc, config), {'0xs': 'helper'})
        self.assertEqual(check.shared_exit_points({'pcs': ['0xa', '0xs', '0xe']}, loc, config), {})
        # the early return's path: the point is exempt and counted with the gaps
        problems, gaps = run(['0xa', '0xs'])
        self.assertEqual(problems, [])
        self.assertEqual(gaps['shared exits reached by an early return (kcov.json)'], 1)
        # the helper's own path covers the entering block: the point witnesses the opposite outcome
        self.assertIn('opposite outcome covered', run(['0xa', '0xs', '0xe'])[0])
        # undeclared: the same
        self.assertIn('opposite outcome covered', run(['0xa', '0xs'], dict(config, shared_exits=[]))[0])

    def test_order_within_a_function(self):
        config = {'files': ['fs/eventfd.c'], 'functions': ['eventfd_write'], 'known_gaps': [],
                  'shared_exits': [], 'operand_exclusions': [], 'data_only_operations': []}
        table = check.parse_decisions([
            self.decision('eventfd_write.wrong_size', 254, [(255, 255)], [(256, 256)]),
            self.decision('eventfd_write.ullong_max', 258, [(259, 259)], [(260, 260)])], config)
        instrumented = {f'fs/eventfd.c:{n}' for n in (255, 256, 259, 260)}
        witnesses = check.witness_table(table, instrumented, {'eventfd_write'})
        loc = {f'0x{n}': [{'function': 'eventfd_write', 'source': f'/x/.deps/linux/fs/eventfd.c:{n}'}]
               for n in (256, 260)}
        trace = {'ops': [{'op': 'write'}]}
        def run(labels, pcs):
            model = {'branches': [{'index': 0, 'label': l} for l in labels]}
            coverage = [{'pcs': pcs}]
            return control_flow(trace, model, coverage, loc, config, table, witnesses, instrumented,
                                {'eventfd_write'})[0]
        in_order = ['eventfd_write.wrong_size=0', 'eventfd_write.ullong_max=0']
        self.assertEqual(run(in_order, ['0x256', '0x260']), [])
        self.assertTrue(run(list(reversed(in_order)), ['0x256', '0x260']))   # mirror order reversed

    def test_generator_profiles(self):
        v2 = generate(7, 300)
        self.assertEqual(v2, generate(7, 300))                                    # deterministic
        self.assertEqual(generate(7, 5, profile='v1'), generate(7, 5, profile='v1'))
        with self.assertRaises(ValueError):
            generate(7, 5, profile='v3')
        creations = [op for t in v2 for op in t['ops'] if op['op'] == 'eventfd2']
        self.assertTrue(any(not op['flags'] & 2048 for op in creations))          # blocking mode
        self.assertTrue(any(op['op'] == 'fcntl' and op['cmd'] != 'F_SETFD' and op['arg']
                            for t in v2 for op in t['ops']))                        # getter arguments
        self.assertTrue(any(sum(op['op'] in ('eventfd2', 'dup') for op in t['ops']) > 24 for t in v2))  # bursts
        for trace in v2:
            validate_trace(trace)

    def test_section_records_pair_in_area_order(self):
        # A worker's block follows the block of a NET_RX section nested in
        # it (moved at its own stop); stops carry only the dropped count.
        f, g = 0xffffffff81000010, 0xffffffff81000020
        le = lambda v: v.to_bytes(8, 'little').hex()
        area = [[300, '0x1', 5, 16, le(g) + le(0x21)], [301, '0x2', 6, 8, le(0)],
                [300, '0x3', 4, 16, le(f) + le(0x11)], [104, '0x4', 7, 4, '01020304'], [301, '0x5', 8, 8, le(0)]]
        paired = check.pair_sections(area)
        self.assertEqual([r[5] for r in paired], [g, g, f, None, f])
        rows = [dict(id='t', mode='pc', index=0, stream='task', records=[[104, '0x6', 3, 4, '00000000']]),
                dict(id='t', mode='pc', index=0, stream='remote', records=area),
                dict(id='t', mode='cmp', index=0, stream='task', records=[])]
        ordered = check.hidden_records([{'id': 't', 'ops': [{}]}], rows)[('t', 'pc')][0]
        self.assertEqual([(r[0], r[5]) for r in ordered],
                         [(104, None), (300, f), (300, g), (301, g), (104, None), (301, f)])
        sites = {('section', 'f:0'): dict(id=40, label='section_start:f', len=16, role='mirror'),
                 ('section', 'f:1'): dict(id=41, label='section_stop:f', len=8, role='mirror'),
                 ('section', 'g:0'): dict(id=48, label='section_start:g', len=16, role='mirror'),
                 ('section', 'g:1'): dict(id=49, label='section_stop:g', len=8, role='mirror')}
        resolved, problems, _, _ = check.resolve_choices({('t', 'pc'): [[r for r in ordered if r[0] >= 300]]},
                                                         sites, {}, {f: 'f', g: 'g'})
        self.assertEqual([r[0] for r in resolved[('t', 'pc')][0]], [40, 48, 49, 41])
        self.assertEqual(problems, {})
        # a lossy section, an unpaired stop, a section record in the task stream
        lossy = [[300, '0x1', 1, 16, le(f) + le(0x11), f], [301, '0x2', 2, 8, le(3), f]]
        _, problems, _, _ = check.resolve_choices({('t', 'pc'): [lossy]}, sites, {}, {f: 'f'})
        self.assertEqual(problems['t'][0]['problem'], 'records dropped in a dispatch section')
        with self.assertRaises(InvalidOutput):
            check.pair_sections(area[1:])
        with self.assertRaises(InvalidOutput):
            check.pair_sections(area[:1])
        with self.assertRaises(InvalidOutput):
            check.hidden_records([{'id': 't', 'ops': [{}]}], [dict(rows[1], stream='task')])
        with self.assertRaises(InvalidOutput):   # a start record without the unit word (a kernel before 2026-10-11)
            check.pair_sections([[300, '0x1', 5, 8, le(g)], [301, '0x2', 6, 8, le(0)]])

    def test_dispatch_order_records_resolve_and_pair(self):
        # Dispatch order: a queue record {work, func} resolves to class
        # 'queue' at the queued function's symbol; the section that runs
        # the unit names it; dispatch_problems pairs them in sequence order
        f, w1, w2 = 0xffffffff81000010, 0xffff888000001000, 0xffff888000002000
        le = lambda v: v.to_bytes(8, 'little').hex()
        sites = {('queue', 'f:0'): dict(id=300, label='queued:f', len=16, role='mirror'),
                 ('section', 'f:0'): dict(id=40, label='section_start:f', len=16, role='mirror'),
                 ('section', 'f:1'): dict(id=41, label='section_stop:f', len=8, role='mirror')}
        op = [[307, '0x9', 1, 16, le(w1) + le(f), None], [307, '0x9', 2, 16, le(w2) + le(f), None],
              [300, '0x1', 3, 16, le(f) + le(w2), f], [301, '0x2', 4, 8, le(0), f],
              [300, '0x1', 5, 16, le(f) + le(w1), f], [301, '0x2', 6, 8, le(0), f]]
        resolved, problems, _, _ = check.resolve_choices({('t', 'pc'): [op]}, sites, {}, {f: 'f'})
        self.assertEqual([r[0] for r in resolved[('t', 'pc')][0]], [300, 300, 40, 41, 40, 41])
        self.assertEqual(problems, {})
        self.assertEqual(check.dispatch_problems({('t', 'pc'): [op]}), ({}, {}))
        # dispatched but never queued; a work section without its unit; a leftover
        never = [[300, '0x1', 3, 16, le(f) + le(w2), f], [301, '0x2', 4, 8, le(0), f]]
        found, left = check.dispatch_problems({('t', 'pc'): [never]})
        self.assertEqual([p['problem'] for p in found['t']], ['a dispatched unit that was never queued or armed'])
        bare = [[300, '0x1', 3, 16, le(f) + le(0), f], [301, '0x2', 4, 8, le(0), f]]
        found, _ = check.dispatch_problems({('t', 'pc'): [bare]})
        self.assertEqual([p['problem'] for p in found['t']], ['a dispatch section without its unit'])
        queued = [[307, '0x9', 1, 16, le(w1) + le(f), None]]
        found, left = check.dispatch_problems({('t', 'pc'): [queued]})
        self.assertEqual((found, left), ({}, {('t', 'pc'): {'work': 1}}))
        # a second queue record while an instance is pending is a second instance (the
        # kernel's PENDING bit cleared by process_one_work before the first section):
        # two sections consume two instances; one section leaves one; a third is never queued
        twice = [[307, '0x9', 1, 16, le(w1) + le(f), None], [307, '0x9', 2, 16, le(w1) + le(f), None],
                 [300, '0x1', 3, 16, le(f) + le(w1), f], [301, '0x2', 4, 8, le(0), f],
                 [300, '0x1', 5, 16, le(f) + le(w1), f], [301, '0x2', 6, 8, le(0), f]]
        self.assertEqual(check.dispatch_problems({('t', 'pc'): [twice]}), ({}, {}))
        self.assertEqual(check.dispatch_problems({('t', 'pc'): [twice[:4]]}), ({}, {('t', 'pc'): {'work': 1}}))
        found, _ = check.dispatch_problems({('t', 'pc'): [twice + twice[2:4]]})
        self.assertEqual([p['problem'] for p in found['t']], ['a dispatched unit that was never queued or armed'])
        # a timer: armed (24 bytes, its address last), then its section; an unfired one is left armed
        t1 = 0xffff888000003000
        armed = [[303, '0xa', 1, 24, le(5) + le(9) + le(t1), None], [300, '0x1', 2, 16, le(f) + le(t1), f],
                 [301, '0x2', 3, 8, le(0), f], [303, '0xa', 4, 24, le(9) + le(20) + le(t1), None]]
        self.assertEqual(check.dispatch_problems({('t', 'pc'): [armed]}), ({}, {('t', 'pc'): {'timer': 1}}))

    def test_d3_timer_and_advance_records_resolve(self):
        # D3: kind 303 resolves by its consumer frame to class 'timer', kind
        # 304 to class 'advance'; a 303 record elsewhere is undeclared
        sites = {('timer', 'drivers/net/wireguard/timers.c:37'): dict(id=100, label='mod_timer_arm', len=24, role='mirror'),
                 ('advance', 'fs/ioctl.c:51'): dict(id=101, label='time_advance', len=16, role='mirror')}
        frame = lambda src: [{'source': f'/x/.deps/linux/{src} (discriminator 1)'}]
        locations = {'0xa': frame('drivers/net/wireguard/timers.c:37') + frame('drivers/net/wireguard/timers.c:61'),
                     '0xb': frame('fs/ioctl.c:51'), '0xc': frame('fs/ioctl.c:51')}
        op = [[304, '0xb', 1, 16, '00' * 16, None], [303, '0xa', 2, 24, '11' * 24, None]]
        resolved, problems, _, _ = check.resolve_choices({('t', 'pc'): [op]}, sites, locations)
        self.assertEqual([r[0] for r in resolved[('t', 'pc')][0]], [101, 100])
        self.assertEqual(problems, {})
        _, problems, _, _ = check.resolve_choices({('t', 'pc'): [[[303, '0xc', 1, 24, '00' * 24, None]]]}, sites, locations)
        self.assertEqual(problems['t'][0]['problem'], 'choice from an undeclared consumer')

    def test_empty_run_is_not_a_pass(self):
        class Args:
            generated_count, wireguard_count, seed, trace = 0, 0, 0, None
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


    def test_timer_advances(self):
        # D3 (section 7): the advance for a target timer, past the wheel's rounding
        from evaluator.generate import fire_advance, quiet_limit, wheel_granularity
        self.assertEqual([wheel_granularity(d) for d in (62, 63, 503, 504, 4031, 4032, 32256)],
                         [1, 8, 8, 64, 64, 512, 4096])
        self.assertEqual([fire_advance(d) for d in (1250 + 83, 2500, 3750 + 83, 1250, 135000)],
                         [1450, 2600, 3950, 1350, 139150])
        self.assertEqual(quiet_limit(6250), 3975)

    def test_timers_share_zero_keeps_the_stream(self):
        from evaluator.generate import generate_wireguard
        a = generate_wireguard(11, 160, steered=0.3, data=0.2)
        self.assertEqual(a, generate_wireguard(11, 160, steered=0.3, data=0.2, timers=0.0))
        b = generate_wireguard(11, 160, steered=0.3, data=0.2, timers=0.2)
        timer = lambda t: any(op['op'] == 'wg_advance' for op in t['ops'])
        others = [t['ops'] for t in b if not timer(t)]
        self.assertGreater(len(b) - len(others), 15)
        self.assertEqual(others, [t['ops'] for t in a][:len(others)])

    def test_steered_timer_traces(self):
        import random
        from evaluator.generate import WAIT_BUDGET_SECONDS, steered_timers, wait_after_up
        rng = random.Random(7)
        fired = set()
        for i in range(300):
            trace = validate_trace(steered_timers(rng, f't{i}'))
            self.assertLessEqual(wait_after_up(trace['ops']), WAIT_BUDGET_SECONDS)
            sites = [s for s, _ in trace['steer']]
            # the first initiation's values (after a response's two draws),
            # then three draws per later initiation
            head = 2 if sites[0] == 'resp_ephemeral' else 0
            self.assertEqual(sites[head:head + 3], ['init_ephemeral', 'tai64n_now', 'index_draw'])
            later = trace['steer'][head + 3:]
            self.assertEqual(later, [[s, 'draw'] for s in ('init_ephemeral', 'tai64n_now', 'index_draw')]
                             * (len(later) // 3))
            self.assertTrue(any(op['op'] == 'wg_advance' for op in trace['ops']))
            fired.update(e for e in trace['expect'] if e.startswith('fired:'))
        self.assertEqual(fired, {f'fired:wg_expired_{n}' for n in (
            'retransmit_handshake', 'send_keepalive', 'new_handshake', 'zero_key_material',
            'send_persistent_keepalive')})

    def test_jiffies_progress(self):
        def rec(kind, seq, a, b, func=None):
            data = a.to_bytes(8, 'little').hex() + b.to_bytes(8, 'little').hex()
            if kind == 303:   # the arm record names its timer (dispatch order): a third word
                data += (0).to_bytes(8, 'little').hex()
            return [kind, 0, seq, len(data) // 2, data, func]
        trace = {'version': 1, 'id': 'j', 'ops': [{'op': 'wg_up'}, {'op': 'wg_advance', 'ticks': 1450},
                                                   {'op': 'wg_observe'}]}
        J = 2**32 - 100
        good = [[rec(303, 1, J, J + 1300)],
                [rec(304, 2, J + 10, J + 1460), rec(300, 3, 0, 0), rec(303, 4, J + 1461, J + 2800)],
                []]
        self.assertEqual(check.jiffies_problems([trace], {('j', 'pc'): good}), {})
        def problems(ops):
            return [p['problem'] for p in check.jiffies_problems([trace], {('j', 'pc'): ops}).get('j', [])]
        # the jump recorded by another amount (a tick handler re-counting it)
        self.assertEqual(problems([good[0], [rec(304, 2, J + 10, J + 2910)] + good[1][1:], []]),
                         ['the advance moved jiffies by another amount', 'jiffies went back',
                          'an arm after an advance before its absorbing tick'])
        # a timer section before the advance record (a tick between the two)
        self.assertEqual(problems([good[0], [good[1][1], good[1][0], good[1][2]], []]),
                         ['records before the advance record'])
        # an arm in the advance's operation before its absorbing tick
        self.assertEqual(problems([good[0], [good[1][0], rec(303, 4, J + 1460, J + 2800)], []]),
                         ['an arm after an advance before its absorbing tick'])
        # natural progress beyond the real-time bound; an advance record elsewhere
        self.assertEqual(problems([good[0], good[1], [rec(303, 5, J + 1461 + 1250, J + 9000)]]),
                         ['jiffies progressed beyond the real-time bound'])
        self.assertEqual(problems([good[0], [], [rec(304, 5, J + 10, J + 1460)]]),
                         ['an advance without exactly one advance record', 'an advance record outside wg_advance'])


class CappedWrapperTests(unittest.TestCase):
    """The memory-cap wrapper is a box matter [USER 2026-10-12]: used when
    installed at its usual place, skipped with one notice when absent, and
    required only when LEANUX_CAPPED names it."""

    def setUp(self):
        import evaluator.check as check
        self.check = check
        check._capped_notice = False

    def test_named_wrapper_must_exist(self):
        with mock.patch.dict(os.environ, {"LEANUX_CAPPED": "/nonexistent/capped"}):
            with self.assertRaises(RuntimeError):
                self.check.capped(["lake", "build"])

    def test_named_wrapper_is_used(self):
        with mock.patch.dict(os.environ, {"LEANUX_CAPPED": "/bin/true"}):
            self.assertEqual(self.check.capped(["lake", "build"]), ["/bin/true", "--", "lake", "build"])

    def test_installed_wrapper_is_used_by_default(self):
        with mock.patch.dict(os.environ, {}, clear=False), \
             mock.patch.object(self.check, "CAPPED_DEFAULT", Path("/bin/true")):
            os.environ.pop("LEANUX_CAPPED", None)
            self.assertEqual(self.check.capped(["lake", "build"]), ["/bin/true", "--", "lake", "build"])

    def test_absent_wrapper_runs_uncapped_with_one_notice(self):
        with mock.patch.dict(os.environ, {}, clear=False), \
             mock.patch.object(self.check, "CAPPED_DEFAULT", Path("/nonexistent/capped")), \
             mock.patch("sys.stderr") as stderr:
            os.environ.pop("LEANUX_CAPPED", None)
            self.assertEqual(self.check.capped(["lake", "build"]), ["lake", "build"])
            self.assertEqual(self.check.capped(["lake", "build"]), ["lake", "build"])
        notices = [c for c in stderr.write.call_args_list if "running uncapped" in str(c)]
        self.assertEqual(len(notices), 1)


if __name__ == '__main__':
    unittest.main()


class D2GeneratorChecks(unittest.TestCase):
    """Stage D2's steered data-plane traces (evaluator/generate.py, steered_data)."""

    def test_data_share_zero_keeps_the_stream(self):
        from evaluator.generate import generate_wireguard
        a = generate_wireguard(11, 160, steered=0.3)
        self.assertEqual(a, generate_wireguard(11, 160, steered=0.3, data=0.0))
        # with D2 traces drawn first, every other trace keeps its content and order
        b = generate_wireguard(11, 160, steered=0.3, data=0.25)
        d2 = lambda t: any(op['op'] == 'wg_xmit' and 'payload' in op['packet'] for op in t['ops']) or any(
            op['op'] == 'wg_inject' and op['message'][:2] == '04' and 'steer' in t for op in t['ops'])
        others = [t['ops'] for t in b if not d2(t)]
        self.assertGreater(len(b) - len(others), 20)
        self.assertEqual(others, [t['ops'] for t in a][:len(others)])

    def test_lifecycle_routing_netns_shares_keep_the_stream(self):
        import json
        from evaluator.generate import generate_wireguard
        a = generate_wireguard(11, 120, steered=0.3, data=0.2)
        self.assertEqual(a, generate_wireguard(11, 120, steered=0.3, data=0.2, lifecycle=0.0, routing=0.0, netns=0.0))
        base = {json.dumps(t['ops'], sort_keys=True) for t in a}
        for share in ('lifecycle', 'routing', 'netns'):
            # the class's traces come from their own generator: the others keep
            # their content and order, only their identifiers shift
            b = generate_wireguard(11, 120, steered=0.3, data=0.2, **{share: 0.3})
            others = [t['ops'] for t in b if json.dumps(t['ops'], sort_keys=True) in base]
            self.assertGreater(len(b) - len(others), 15, share)
            self.assertEqual(others, [t['ops'] for t in a][:len(others)], share)

    def test_lifecycle_routing_netns_multi_peer_traces(self):
        import random
        from evaluator.generate import (WAIT_BUDGET_SECONDS, lifecycle_trace, multi_peer_timers, netns_trace,
                                        routing_trace, wait_after_up)
        for name, fn in (('lifecycle', lifecycle_trace), ('routing', routing_trace), ('netns', netns_trace),
                         ('multi', multi_peer_timers)):
            rng = random.Random(7)
            shapes = set()
            for i in range(200):
                trace = validate_trace(fn(rng, f'{name}{i}'))
                self.assertLessEqual(wait_after_up(trace['ops']), WAIT_BUDGET_SECONDS, name)
                shapes.add(tuple(op['op'] for op in trace['ops']))
            self.assertGreater(len(shapes), 1 if name != 'multi' else 0, name)
        rng = random.Random(7)
        trace = multi_peer_timers(rng, 'm')
        sites = [s for s, _ in trace['steer']]
        n = len(trace['ops'][0]['config']['peers'])
        # each of the 2n initiations: three draws, then the jitter, in encounter order
        self.assertEqual(sites, ['init_ephemeral', 'tai64n_now', 'index_draw', 'retransmit_jitter'] * (2 * n))
        rng = random.Random(7)
        self.assertTrue(any(t.get('net_fixture') == 'bare' for t in (lifecycle_trace(rng, f'l{i}') for i in range(100))))

    def test_steered_data_traces(self):
        import random
        from harness import noise
        from evaluator.generate import WAIT_BUDGET_SECONDS, steered_data, wait_after_up
        rng = random.Random(5)
        local = {bytes(noise.WG0_ADDR4), bytes(noise.WG0_ADDR6)}
        seen = set()
        for i in range(400):
            trace = steered_data(rng, f't{i}')
            self.assertLessEqual(wait_after_up(trace['ops']), WAIT_BUDGET_SECONDS)
            self.assertLessEqual(len(trace['ops']), 64)
            sites = [s for s, _ in trace['steer']]
            self.assertIn(sites, (['resp_ephemeral', 'index_draw'], ['init_ephemeral', 'tai64n_now', 'index_draw']))
            for op in trace['ops']:
                if op['op'] == 'wg_xmit':
                    dst = bytes.fromhex(op['packet']['dst'])
                    self.assertNotIn(dst, local)
                    self.assertFalse(dst[0] == 0xfe and dst[1] & 0xc0 == 0x80)
                    n = len(op['packet']['payload']) // 2
                    self.assertTrue(1 <= n <= (1392 if op['packet']['family'] == 4 else 1372))
                    seen.add('xmit')
                if op['op'] == 'wg_inject':
                    self.assertLessEqual(len(op['message']) // 2, 1400)
                    if op['message'][:2] == '04':
                        seen.add('data')
            # every operation but the payload's is valid today (stream A extends validate_packet)
            stripped = copy.deepcopy(trace)
            for op in stripped['ops']:
                op.get('packet', {}).pop('payload', None)
            validate_trace(stripped)
        self.assertEqual(seen, {'xmit', 'data'})


class AllocChecks(unittest.TestCase):
    """A1 (docs/2026-10-05-a-alloc.md): the alloc_fail class and the armed site set."""

    def test_alloc_share_zero_keeps_the_stream(self):
        from evaluator.generate import generate_wireguard
        a = generate_wireguard(11, 120, steered=0.15, data=0.15)
        self.assertEqual(a, generate_wireguard(11, 120, steered=0.15, data=0.15, alloc=0.0))
        b = generate_wireguard(11, 120, steered=0.15, data=0.15, alloc=0.2)
        alloc = [t for t in b if any(s in ('sendBufSkb', 'keepaliveSkb') for s, _ in t.get('steer', []))]
        self.assertGreater(len(alloc), 10)
        others = [t['ops'] for t in b if t not in alloc]
        self.assertEqual(others, [t['ops'] for t in a][:len(others)])
        for t in alloc:
            validate_trace(t)
            self.assertIn('0000000000000000', [v for _, v in t['steer']])

    def test_armed_labels(self):
        from harness.steer import ALLOC_SITES, SteeringError, alloc_armed_labels
        sites = {('direct', row['consumer']): {'ips': [0x10000 + 16 * k], 'functions': ['f']}
                 for k, row in enumerate(ALLOC_SITES.values()) if row['helper'] is None}
        sites[('direct', 'fs/eventfd.c:393')] = {'ips': [0x200, 0x300], 'functions': ['g']}
        sites[('tail_jumps', '')] = []
        ranges = {'__alloc_skb': (0x1000, 0x1100), 'kmalloc_reserve': (0x2000, 0x2100),
                  'pskb_expand_head': (0x3000, 0x3100), '__d_alloc': (0x4000, 0x4100),
                  '__kvmalloc_node_noprof': (0x5000, 0x5100)}
        armed = alloc_armed_labels([(0x1000, 0x1100), (0x2000, 0x2100)], (sites, ranges))
        self.assertEqual(armed, ['keepaliveSkb', 'replySkb', 'sendBufSkb'])
        self.assertIn('kmallocEventfdCtx', alloc_armed_labels([(0x200, 0x201), (0x300, 0x301)], (sites, ranges)))
        with self.assertRaises(SteeringError):   # one of two call sites armed
            alloc_armed_labels([(0x200, 0x201)], (sites, ranges))
class WgMutantScoringChecks(unittest.TestCase):
    """scripts/wg-mutants.py: only a mirror-side verdict rejects a sentinel; an
    infrastructure outcome is no verdict; the sentinel set is one entry per
    channel, each applicable to the tree."""
    @classmethod
    def setUpClass(cls):
        import importlib.util
        spec = importlib.util.spec_from_file_location('wg_mutants', ROOT / 'scripts/wg-mutants.py')
        cls.m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.m)   # main() is not run on import

    def report(self, *outcomes, aborted=None):
        return dict(status='pass' if not outcomes and not aborted else 'fail', aborted=aborted,
                    failures=[dict(id=f't{i}', outcome=o) for i, o in enumerate(outcomes)])

    def test_mismatches_reject(self):
        for outcome in self.m.MISMATCH_OUTCOMES:
            self.assertEqual(self.m.classify(self.report(outcome))[0], 'rejected')
        self.assertEqual(self.m.classify(self.report('hidden_mismatch', 'semantic_mismatch'))[0], 'rejected')
        # a mismatch beside an infrastructure outcome is no verdict
        status, mismatches, other = self.m.classify(self.report('hidden_mismatch', 'environment_failure'))
        self.assertEqual((status, mismatches, other), ('no_verdict', ['hidden_mismatch'], ['environment_failure']))

    def test_infrastructure_is_no_verdict(self):
        for outcome in ('environment_failure', 'timeout', 'resource_busy', 'output_limit', 'crash',
                        'invalid_output', 'invalid_coverage', 'not_run', 'some_new_kind'):
            self.assertEqual(self.m.classify(self.report(outcome)), ('no_verdict', [], [outcome]))
        self.assertEqual(self.m.classify(None)[0], 'no_verdict')
        self.assertEqual(self.m.classify(self.report('semantic_mismatch', aborted='KeyboardInterrupt'))[0],
                         'no_verdict')
        self.assertEqual(self.m.classify(dict(status='fail', aborted=None, failures=[]))[0], 'no_verdict')

    def test_clean_pass_survives(self):
        self.assertEqual(self.m.classify(self.report()), ('survived', [], []))

    def test_sentinels_one_per_channel_and_applicable(self):
        # the sentinel set: every entry names its channel, its pattern is present
        # exactly once in the file it mutates, and the channels are distinct
        sentinels = self.m.SENTINELS
        self.assertGreaterEqual(len(sentinels), 10)
        channels = [e[1] for e in sentinels]
        self.assertEqual(len(channels), len(set(channels)))
        for name, channel, what, path, old, new, subset, suite in sentinels:
            text = (ROOT / path).read_text()
            self.assertEqual(text.count(old), 1, name)
            self.assertNotEqual(old, new, name)
            self.assertIn(suite, ('wireguard', 'alloc', 'pipes'), name)
        self.assertEqual(self.m.tally({'a': dict(status='survived'), 'b': dict(status='no_verdict'),
                                       'c': dict(status='rejected')}),
                         {'no_verdict': 1, 'rejected': 1, 'survived': 1})


class SeccompChecks(unittest.TestCase):
    """seccomp stream X: the generator profile stays inside the trace contract
    and the chunking keeps a guest's child probes under the console budget."""

    def test_seccomp_profile(self):
        traces = generate(20260920, 60, profile='seccomp')
        self.assertEqual(traces, generate(20260920, 60, profile='seccomp'))
        for trace in traces:
            validate_trace(trace)
            self.assertLessEqual(sum(op['op'] == 'seccomp_probe' and op['where'] == 'child' for op in trace['ops']), 3)
        kinds = Counter('checker' if not any(op['op'] == 'seccomp_probe' for op in t['ops'])
                        else 'child' if t.get('seccomp_child') else 'self' for t in traces)
        self.assertEqual(set(kinds), {'checker', 'child', 'self'})

    def test_seccomp_console_budget_per_chunk(self):
        probe = {'op': 'seccomp_probe', 'nr': 102, 'where': 'child'}
        install = {'op': 'seccomp_install', 'via': 'seccomp', 'flags': [], 'filter': [[6, 0, 0, 0x7fff0000]] * 768}
        child = [dict(version=1, id=f'c{i}', ops=[probe] * 2, seccomp_child=True) for i in range(6)]
        long = [dict(version=1, id=f'l{i}', ops=[install] * 4) for i in range(3)]
        plain = [dict(version=1, id=f'p{i}', ops=[{'op': 'seccomp_prctl', 'cmd': 'get_seccomp'}]) for i in range(5)]
        chunks = check.chunk_traces(plain + child + long)
        for _start, traces, _name in chunks:
            self.assertLessEqual(sum(check.seccomp_console_cost(t) for t in traces), check.CHUNK_CONSOLE_BUDGET)
        self.assertEqual([t['id'] for _s, ts, _n in chunks for t in ts], [t['id'] for t in plain + child + long])
        # two child probes are 8.9 MB: one child trace per chunk, and a 2.1 MB install trace (four of 768) joins the last
        self.assertEqual([len(ts) for _s, ts, _n in chunks], [6, 1, 1, 1, 1, 2, 2])


class ReviewProbes(unittest.TestCase):
    """The pre-release review's checker probes (docs/2026-10-14-pre-release-review.md)."""

    def test_operand_agreement_counts_distinct_rows_beside_obligations(self):
        # finding 5: three identical obligations met by one kernel row; a
        # second, unmatched row needs no counterpart: 3 obligations, 1 row
        comparison = {'rel': 'ge', 'const_rhs': False, 'site': None}
        decisions = {'alloc_fd.at_limit': {'site': 'fs/file.c:514', 'comparison': comparison}}
        loc = {'0x1': [{'function': 'alloc_fd', 'source': '/x/.deps/linux/fs/file.c:514'}]}
        model = {'branches': [{'index': 0, 'label': 'alloc_fd.at_limit=0', 'operands': [8, 32]}] * 3}
        records = [{'records': [[4, '0x8', '0x20', '0x1'], [4, '0x9', '0x20', '0x1']]}]
        distinct = set()
        problems, checked = check.operand_agreement({'ops': [{'op': 'dup'}]}, model, records, loc, decisions,
                                                    distinct=distinct)
        self.assertEqual((problems, checked), ([], 3))
        self.assertEqual(len(distinct), 1)

    def test_select_in_domain_accounts_for_every_candidate(self):
        # finding 3: the account covers all candidates, not only those before
        # the last selected one, and names every rejection reason
        candidates = [{'id': f't{i}'} for i in range(6)]
        verdicts = [{'in_domain': True}, {'in_domain': False, 'site': 'a', 'what': 'x'}, {'in_domain': True},
                    {'in_domain': True}, {'in_domain': False, 'site': 'b', 'what': 'y'},
                    {'in_domain': False, 'site': 'a', 'what': 'x'}]
        kept, account = check.select_in_domain(candidates, verdicts, 2)
        self.assertEqual([t['id'] for t in kept], ['t0', 't2'])
        self.assertEqual(account, dict(candidates=6, in_domain=3, selected=2, rejected={'a: x': 2, 'b: y': 1}))

