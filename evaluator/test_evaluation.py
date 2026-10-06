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

    def test_fired_timer_sections_field(self):
        # D3: the mirror's optional `fired` list, validated strictly
        result = dict(copy.deepcopy(self.result), fired=[{'index': 0, 'symbol': 'wg_expired_new_handshake'}])
        self.assertEqual(parse_batch([self.trace], json.dumps(result))[0]['fired'][0]['index'], 0)
        for fired in ([], [{'index': 1, 'symbol': 'wg_expired_new_handshake'}], [{'index': 0}],
                      [{'index': 0, 'symbol': 'Bad Symbol'}], {}):
            with self.assertRaises(InvalidOutput):
                parse_batch([self.trace], json.dumps(dict(copy.deepcopy(self.result), fired=fired)))

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

    CONFIG = {'files': ['fs/eventfd.c'], 'functions': ['eventfd_read', 'eventfd_ctx_do_read'], 'known_gaps': []}

    def decision(self, label, line, true, false):
        return {'label': label, 'file': 'fs/eventfd.c', 'line': line,
                'when_true': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in true],
                'when_false': [{'file': 'fs/eventfd.c', 'lo': lo, 'hi': hi} for lo, hi in false],
                'repeatable': False, 'comparison': None}

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
        self.assertEqual([p['problem'] for p in problems], ['span lines covered by an unlisted function'])

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

    def test_order_within_a_function(self):
        config = {'files': ['fs/eventfd.c'], 'functions': ['eventfd_write'], 'known_gaps': []}
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
        area = [[300, '0x1', 5, 8, le(g)], [301, '0x2', 6, 8, le(0)],
                [300, '0x3', 4, 8, le(f)], [104, '0x4', 7, 4, '01020304'], [301, '0x5', 8, 8, le(0)]]
        paired = check.pair_sections(area)
        self.assertEqual([r[5] for r in paired], [g, g, f, None, f])
        rows = [dict(id='t', mode='pc', index=0, stream='task', records=[[104, '0x6', 3, 4, '00000000']]),
                dict(id='t', mode='pc', index=0, stream='remote', records=area),
                dict(id='t', mode='cmp', index=0, stream='task', records=[])]
        ordered = check.hidden_records([{'id': 't', 'ops': [{}]}], rows)[('t', 'pc')][0]
        self.assertEqual([(r[0], r[5]) for r in ordered],
                         [(104, None), (300, f), (300, g), (301, g), (104, None), (301, f)])
        sites = {('section', 'f:0'): dict(id=40, label='section_start:f', len=8, role='mirror'),
                 ('section', 'f:1'): dict(id=41, label='section_stop:f', len=8, role='mirror'),
                 ('section', 'g:0'): dict(id=48, label='section_start:g', len=8, role='mirror'),
                 ('section', 'g:1'): dict(id=49, label='section_stop:g', len=8, role='mirror')}
        resolved, problems, _, _ = check.resolve_choices({('t', 'pc'): [[r for r in ordered if r[0] >= 300]]},
                                                         sites, {}, {f: 'f', g: 'g'})
        self.assertEqual([r[0] for r in resolved[('t', 'pc')][0]], [40, 48, 49, 41])
        self.assertEqual(problems, {})
        # a lossy section, an unpaired stop, a section record in the task stream
        lossy = [[300, '0x1', 1, 8, le(f), f], [301, '0x2', 2, 8, le(3), f]]
        _, problems, _, _ = check.resolve_choices({('t', 'pc'): [lossy]}, sites, {}, {f: 'f'})
        self.assertEqual(problems['t'][0]['problem'], 'records dropped in a dispatch section')
        with self.assertRaises(InvalidOutput):
            check.pair_sections(area[1:])
        with self.assertRaises(InvalidOutput):
            check.pair_sections(area[:1])
        with self.assertRaises(InvalidOutput):
            check.hidden_records([{'id': 't', 'ops': [{}]}], [dict(rows[1], stream='task')])

    def test_d3_timer_and_advance_records_resolve(self):
        # D3: kind 303 resolves by its consumer frame to class 'timer', kind
        # 304 to class 'advance'; a 303 record elsewhere is undeclared
        sites = {('timer', 'drivers/net/wireguard/timers.c:37'): dict(id=100, label='mod_timer_arm', len=16, role='mirror'),
                 ('advance', 'fs/ioctl.c:51'): dict(id=101, label='time_advance', len=16, role='mirror')}
        frame = lambda src: [{'source': f'/x/.deps/linux/{src} (discriminator 1)'}]
        locations = {'0xa': frame('drivers/net/wireguard/timers.c:37') + frame('drivers/net/wireguard/timers.c:61'),
                     '0xb': frame('fs/ioctl.c:51'), '0xc': frame('fs/ioctl.c:51')}
        op = [[304, '0xb', 1, 16, '00' * 16, None], [303, '0xa', 2, 16, '11' * 16, None]]
        resolved, problems, _, _ = check.resolve_choices({('t', 'pc'): [op]}, sites, locations)
        self.assertEqual([r[0] for r in resolved[('t', 'pc')][0]], [101, 100])
        self.assertEqual(problems, {})
        _, problems, _, _ = check.resolve_choices({('t', 'pc'): [[[303, '0xc', 1, 16, '00' * 16, None]]]}, sites, locations)
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
        self.assertEqual(quiet_limit(6250), 4225)

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
            return [kind, 0, seq, 16, data, func]
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
        self.assertEqual(problems([good[0], good[1], [rec(303, 5, J + 1461 + 1100, J + 9000)]]),
                         ['jiffies progressed beyond the real-time bound'])
        self.assertEqual(problems([good[0], [], [rec(304, 5, J + 10, J + 1460)]]),
                         ['an advance without exactly one advance record', 'an advance record outside wg_advance'])


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
