"""Build the mirror, run traces on the pinned Linux guest and the mirror, compare.

    scripts/in-bundle python3 -m evaluator.check
        [--suite handwritten,critic,wireguard,alloc,generated,wireguard-generated,pipes,pipes-generated]
        [--generated-count N] [--wireguard-count N] [--pipes-count N] [--seed S] [--trace ID] [--out DIR]
        [--no-build] [--alloc-share F]

The command fails unless every trace agrees on observations (A1) and every
operation's model branch labels are consistent with Linux KCOV coverage (A2).
Timeouts, crashes, invalid output, unknown labels and environment failures
never count as agreement. `--trace ID` replays a single case.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from harness.linux import (ARTIFACTS as LINUX_ARTIFACTS, ARM_RECORDS, DISPATCH_SYMBOLS, GUEST_VARIANTS, KERNEL, LinuxRunError, verify_kernel,
                          dispatch_addresses, run_linux)
from harness.steer import SteeringError, call_sites, resolve as resolve_steering
from harness.trace import InvalidTrace, loads_trace, uses_wireguard, validate_trace
from .coverage import attributable, instrumented_lines, symbolize
from .generate import generate, generate_wireguard
from .protocol import InvalidOutput, compare, loads, parse_batch, validate_coverage

ROOT = Path(__file__).resolve().parents[1]
ANCHORS = ROOT / 'correspondence/kcov.json'
SUITES = ('handwritten', 'critic', 'wireguard', 'alloc', 'generated', 'wireguard-generated', 'pipes', 'pipes-generated')
# Corpus suites whose traces pass the domain filter first: the pipes corpus
# holds a hang control (a blocking read) that must never reach the guest.
# There, a trace named `*_filtered` must be outside the domain and every
# other trace inside it; anything else fails the run.
# The share of generated WireGuard traces that are steered handshakes (the
# initiator role, stage D1).
STEERED_SHARE = 0.15
# The share that are steered data-plane traces (stage D2, steered_data):
# payload transmissions and received data messages.
DATA_SHARE = 0.15
# The share that are steered timer traces (stage D3, steered_timers): the
# virtual time advance firing WireGuard's timers, and the key-expiry arms.
TIMERS_SHARE = 0.1
# The share that steer allocation failures (A1, alloc_fail): the chunks that
# hold one are armed, so every network trace in them runs armed.
ALLOC_SHARE = 0.05
# Suites run only on request: traces that must fail (negative controls).
# (L: lifecycle-controls, the random port steered onto a fixture port, which
# the mirror must refuse: a stopped mirror fails its whole chunk, so it runs
# apart)
# (E-B: underload-controls, the merged-injection control, which the mirror's
# section-bracket discard must reject — docs/2026-10-05-e-dos.md §4.1)
CONTROL_SUITES = ('steering-controls', 'timer-controls', 'lifecycle-controls', 'underload-controls')
CHUNK = 100


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def chunk_traces(traces):
    """Split traces into chunks of at most CHUNK. E-B isolation
    (docs/2026-10-05-e-dos.md §4.2): a `wg_flood` sets the kernel-global
    `last_under_load` (receive.c:100), which teardown does not reset and which
    decays over one second, so an under-load trace can leak `under_load` into a
    later trace in the same VM boot (one chunk). Each under-load trace therefore
    runs in a chunk by itself; every normal trace keeps the constant-false decay
    (the cross-trace guard). Yields `(start, chunk, name)`."""
    def under_load(trace):
        return any(op['op'] == 'wg_flood' for op in trace['ops'])
    pending, current, cur_start = [], [], 0
    def flush():
        nonlocal current
        if current:
            pending.append((cur_start, current, f'chunk-{len(pending):03}'))
            current = []
    for i, trace in enumerate(traces):
        if under_load(trace):
            flush()
            pending.append((i, [trace], f'chunk-{len(pending):03}'))
        else:
            if not current:
                cur_start = i
            current.append(trace)
            if len(current) == CHUNK:
                flush()
    flush()
    return pending


def model_identity():
    paths = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'Leanux.lean']
    paths += sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'Leanux').rglob('*.lean'))
    return {path: sha256((ROOT / path).read_bytes()) for path in paths}


def git_state():
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True, text=True, check=True)
    dirty = subprocess.run(['git', 'status', '--porcelain'], cwd=ROOT, capture_output=True, text=True, check=True)
    return dict(head=head.stdout.strip(), dirty=bool(dirty.stdout.strip()))


CANDIDATES_PER_TRACE = 3


def domain_filter(traces):
    """`leanux-model --domain`: whether each trace stays inside the modeled
    domain (a blocking wait, for example, does not). A mirror invariant
    failure aborts: it is a defect, not a filtering decision."""
    payload = ''.join(json.dumps(t, separators=(',', ':'), sort_keys=True) + '\n' for t in traces)
    result = subprocess.run([MODEL, '--domain'], input=payload.encode(), capture_output=True, timeout=600)
    if result.returncode or result.stderr.strip():   # a Lean panic prints and continues: a mirror defect too
        raise InvalidOutput(f'domain filter failed: {result.stderr.decode(errors="replace")[-2000:]}')
    verdicts = [loads(line) for line in result.stdout.decode().splitlines()]
    if [v.get('id') for v in verdicts] != [t['id'] for t in traces]:
        raise InvalidOutput('domain filter verdicts do not match the candidates')
    return verdicts


def load_traces(suites, counts, seed, only, filtered, alloc_share=ALLOC_SHARE):
    """The selected suites. Generated traces are drawn from a fixed number of
    seeded candidates, keeping those the mirror places inside the domain;
    `filtered` receives the rejected candidates' reasons."""
    traces = []
    for suite in suites:
        if suite in ('generated', 'wireguard-generated', 'pipes-generated'):
            source = {'generated': generate,
                      'wireguard-generated': lambda s, n: generate_wireguard(s, n, steered=STEERED_SHARE, data=DATA_SHARE,
                                                                             timers=TIMERS_SHARE, alloc=alloc_share),
                      'pipes-generated': lambda s, n: generate(s, n, profile='pipes')}[suite]
            count = counts[suite]
            candidates = [validate_trace(t) for t in source(seed, count * CANDIDATES_PER_TRACE)]
            verdicts = domain_filter(candidates)
            kept = [t for t, v in zip(candidates, verdicts) if v['in_domain']][:count]
            if len(kept) < count:
                raise ValueError(f'only {len(kept)} of {count} generated traces are inside the domain')
            last = candidates.index(kept[-1])
            filtered.update(f"{v['site']}: {v['what']}" for v in verdicts[:last + 1] if not v['in_domain'])
            traces += kept
        else:
            files = sorted((ROOT / 'corpus' / suite).glob('*.json'))
            if not files:
                raise ValueError(f'empty corpus suite {suite}')
            loaded = [loads_trace(path.read_text()) for path in files]
            if suite == 'pipes':
                verdicts = domain_filter([validate_trace(t) for t in loaded])
                wrong = [t['id'] for t, v in zip(loaded, verdicts) if v['in_domain'] == t['id'].endswith('_filtered')]
                if wrong:
                    raise ValueError(f'pipes corpus traces on the wrong side of the domain filter: {wrong}: '
                                     + '; '.join(f"{t['id']}: {v.get('site')}: {v.get('what')}"
                                                 for t, v in zip(loaded, verdicts) if t['id'] in wrong)[:4000])
                filtered.update(f"{t['id']}: {v['site']}: {v['what']}" for t, v in zip(loaded, verdicts)
                                if not v['in_domain'])
                loaded = [t for t, v in zip(loaded, verdicts) if v['in_domain']]
            traces += loaded
    ids = [trace['id'] for trace in traces]
    if len(set(ids)) != len(ids):
        raise ValueError('duplicate trace identifiers')
    if only is not None:
        traces = [trace for trace in traces if trace['id'] == only]
        if not traces:
            raise ValueError(f'no trace {only!r} in the selected suites')
    return [validate_trace(trace) for trace in traces]


MODEL = ROOT / '.lake/build/bin/leanux-model'
# The box-wide memory-cap wrapper (cgroup memory.max; see ~/.claude/CLAUDE.md).
# scripts/in-bundle's PATH has no /usr/local/bin, hence the absolute path.
CAPPED = Path(os.environ.get('LEANUX_CAPPED', '/usr/local/bin/capped'))


def capped(command):
    """Prefix a heavy command with the memory-cap wrapper; no wrapper, no run."""
    if not os.access(CAPPED, os.X_OK):
        raise RuntimeError(f'memory-cap wrapper not found: {CAPPED} (install capped, or point LEANUX_CAPPED at it)')
    return [str(CAPPED), '--'] + command


def build_model(out, rebuild):
    """Build, or with rebuild=False require the existing build to be up to date."""
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    command = capped(['lake', 'build', 'leanux-model'] + ([] if rebuild else ['--no-build']))
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=1800)
    (out / 'build.log').write_bytes(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError('model build failed or is out of date; see build.log')
    return dict(mode='built' if rebuild else 'reused-up-to-date', binary_sha256=sha256(MODEL.read_bytes()))


def run_model(traces, out):
    payload = ''.join(json.dumps(t, separators=(',', ':'), sort_keys=True) + '\n' for t in traces)
    (out / 'inputs.jsonl').write_text(payload)
    result = subprocess.run([MODEL], input=payload.encode(), capture_output=True, timeout=300)
    (out / 'model.stdout').write_bytes(result.stdout)
    (out / 'model.stderr').write_bytes(result.stderr)
    if not result.returncode and result.stderr.strip():
        # A completed run writes nothing to stderr. A Lean panic (an
        # out-of-range `!` access: "index out of bounds", `get!` of none,
        # `panic!`) prints there and continues with a default value: a mirror
        # invariant failure, never a verdict on the default.
        raise ModelStopped('mirror_invariant', result.stderr.decode(errors='replace').strip()[-2000:])
    if result.returncode:
        kind = {3: 'unsupported_path', 4: 'mirror_invariant', 5: 'hidden_mismatch'}.get(result.returncode, 'invalid_output')
        raise ModelStopped(kind, result.stderr.decode(errors='replace').strip()[-2000:])
    return parse_batch(traces, result.stdout)


class ModelStopped(InvalidOutput):
    """The mirror stopped without observations: a path outside its domain
    (exit 3), a mirror invariant failure (exit 4), hidden-input records that
    disagree with its reads (exit 5), or another error."""
    def __init__(self, kind, detail):
        super().__init__(detail)
        self.kind = kind


def load_kcov_config():
    config = json.loads(ANCHORS.read_text())
    if (set(config) != {'version', 'description', 'files', 'functions', 'branch_free_functions', 'known_gaps',
                        'shared_exits', 'operand_exclusions'}
            or config['version'] != 2):
        raise ValueError('kcov config fields or version')
    if any(type(x) is not str or x in config['functions'] for x in config['branch_free_functions']):
        raise ValueError('branch-free functions must be names outside the instrumented functions')
    if not config['files'] or not config['functions'] or any(type(x) is not str for x in config['files'] + config['functions']):
        raise ValueError('kcov config needs anchored files and instrumented functions')
    for gap in config['known_gaps']:
        if set(gap) != {'op', 'name', 'line', 'note'} or gap['line'].rsplit(':', 1)[0] not in config['files']:
            raise ValueError(f'known gap {gap}: fields or file')
    def anchored_line(text):
        return (type(text) is str and text.rsplit(':', 1)[0] in config['files']
                and text.rsplit(':', 1)[-1].isdigit())
    for exit_ in config['shared_exits']:
        if (set(exit_) != {'function', 'frames', 'unless_covered', 'note'} or type(exit_['function']) is not str
                or type(exit_['frames']) is not list or len(exit_['frames']) < 2
                or not all(anchored_line(f) for f in exit_['frames'])
                or type(exit_['unless_covered']) is not list or not exit_['unless_covered']
                or not all(anchored_line(f) for f in exit_['unless_covered'])):
            raise ValueError(f'shared exit {exit_}: fields, frames or file')
    for exclusion in config['operand_exclusions']:
        if (set(exclusion) != {'label', 'operand', 'call', 'note'} or type(exclusion['label']) is not str
                or type(exclusion['operand']) is not str or not anchored_line(exclusion['call'])):
            raise ValueError(f'operand exclusion {exclusion}: fields or file')
    return config


SPAN_WINDOW = (40, 60)
SOURCE = Path(os.environ.get('LEANUX_SHARED_ROOT', ROOT)).resolve() / '.deps/linux'
_source_cache = {}


def non_statement(line):
    """Lines that own no code of their own: braces, labels, blanks and comments."""
    path, number = line.rsplit(':', 1)
    if path not in _source_cache:
        _source_cache[path] = (SOURCE / path).read_text().splitlines()
    lines = _source_cache[path]
    if not 1 <= int(number) <= len(lines):
        raise InvalidOutput(f'span line {line} is beyond the end of the file')
    text = lines[int(number) - 1].strip()
    return (not text or text in ('{', '}', '};') or re.match(r'(/\*|//|\*(\s|/|$))', text) is not None
            or re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*:', text) is not None)


# The random and clock helpers a choice's call chain passes through before
# reaching its consumer (choice-stream strategy, section 4.2): one list, shared
# with the steering resolver.
from harness.steer import (ALLOC_HELPER_FUNCTIONS, ALLOC_HELPER_FILES, ALLOC_KIND, ALLOC_SITES,  # noqa: E402
                           CHOICE_HELPERS, alloc_armed_labels, alloc_call_sites, alloc_ranges)
RANDOM_KINDS = {1, 101, 102, 104, 108, 110}
# Dispatch sections' start and stop records (kernel/patches/choice-stream.patch).
SECTION_START, SECTION_STOP = 300, 301
# A reschedule at a cond_resched inside a task's dispatch section (same patch).
RESCHED = 302
# D3 (docs/2026-10-05-d3-timers.md, sections 3.3-3.4, 13.4): the arm record
# {jiffies, expires} at mod_timer for a dispatch-set timer (class 'timer',
# resolved by its consumer frame, timers.c:37), and the time advance's
# {before, after} (class 'advance', resolved by its consumer frame, the
# ioctl's call site fs/ioctl.c:51, the only caller of kcov_ioctl).
TIMER_ARM, TIME_ADVANCE = 303, 304
# W9 (docs/2026-10-06-w8-w9-netns-routing.md, sections 4.1 and 5): the
# dst-cache `jiffies` records (class 'jiffies', resolved by the consumer
# frame like the clock readers): the value stored at a reset
# (`dst_cache_reset`, the inline in include/net/dst_cache.h) and at the
# refresh of a miss (net/core/dst_cache.c); the mirror computes the cache's
# `time_after` from them. Written only with the arm records (W9-K).
DST_CACHE_JIFFIES = 306
# Dispatch order (docs/2026-10-11-dispatch-order.md): the queue record
# {work, func} written at __queue_work for a work item of the dispatch set
# (class 'queue', resolved by the function's symbol like a section); a
# section start carries {func, unit} and an arm record {jiffies, expires,
# timer}, so every dispatched unit is paired with its queueing or arming
# (dispatch_problems) and the mirror runs the unit the record names.
QUEUE = 307


def load_hidden_sites():
    """The mirror's choice sites (`leanux-model --hidden-sites`):
    (kind, "file:line" of the consumer frame) -> entry."""
    result = subprocess.run([MODEL, '--hidden-sites'], capture_output=True, timeout=60)
    if result.returncode:
        raise InvalidOutput('leanux-model --hidden-sites failed')
    sites = {}
    for entry in loads(result.stdout.decode()):
        if set(entry) != {'id', 'label', 'kind', 'file', 'line', 'len', 'role'} \
                or entry['kind'] not in ('random', 'clock', 'section', 'resched', 'timer', 'advance', 'alloc', 'queue', 'jiffies') \
                or entry['role'] not in ('mirror', 'cut', 'ambient'):
            raise InvalidOutput(f'hidden site fields: {entry}')
        key = (entry['kind'], f"{entry['file']}:{entry['line']}")
        if key in sites:
            raise InvalidOutput(f'duplicate hidden site {key}')
        sites[key] = entry
    return sites


def pair_sections(records):
    """A remote row's records in area order, each with the dispatched
    function's address appended (None outside section records); a start
    record is {func, unit} (the unit is the mirror's and dispatch_problems'). A section's
    records reach the area as one block at its stop (kcov_remote_stop), so in
    area order every block starts with its start record and ends with its
    stop record; a nested softirq section's block precedes its enclosing
    one. The stop record carries only the dropped count, so it is paired with
    its start here, before records are ordered by sequence number."""
    out, open_ = [], []
    for record in records:
        func = None
        if record[0] == SECTION_START:
            if record[3] != 16:
                raise InvalidOutput('section start record length')
            func = int.from_bytes(bytes.fromhex(record[4][:16]), 'little')
            open_.append(func)
        elif record[0] == SECTION_STOP:
            if not open_:
                raise InvalidOutput('section stop record without its start')
            func = open_.pop()
        out.append(list(record) + [func])
    if open_:
        raise InvalidOutput('section start record without its stop')
    return out


def hidden_records(traces, rows):
    """Each child's choice records per operation of each trace, ordered by
    sequence number across the task and remote streams:
    {(id, mode): [[[kind, call site, seq, length, hex, section function], ...]
    per op]}."""
    net = {t['id']: len(t['ops']) for t in traces}
    per, seen = {}, set()
    for row in rows:
        if row['id'] not in net or not 0 <= row['index'] < net[row['id']]:
            raise InvalidOutput('choice record for an unknown operation')
        row_key = (row['id'], row['mode'], row['index'], row['stream'])
        if row_key in seen:
            raise InvalidOutput('duplicate choice row')
        seen.add(row_key)
        ops = per.setdefault((row['id'], row['mode']), [[] for _ in range(net[row['id']])])
        if row['stream'] == 'remote':
            ops[row['index']] += pair_sections(row['records'])
        elif any(r[0] in (SECTION_START, SECTION_STOP) for r in row['records']):
            raise InvalidOutput('section record in the task stream')
        else:
            ops[row['index']] += [list(r) + [None] for r in row['records']]
    # every operation of every trace has a task row in both children
    for trace_id, count in net.items():
        for mode in ('pc', 'cmp'):
            if any((trace_id, mode, i, 'task') not in seen for i in range(count)):
                raise InvalidOutput(f'choice rows missing for {trace_id} ({mode})')
    for key, ops in per.items():
        for op in ops:
            op.sort(key=lambda r: r[2])
            if len({r[2] for r in op}) != len(op):
                raise InvalidOutput('duplicate choice sequence number')
    return per


def resolve_choices(per, sites, locations, dispatch=None):
    """Each record's site, by the consumer frame of its call chain (the first
    frame outside the random and clock helpers), or for a section record by
    the dispatched function's symbol (`dispatch`: address -> symbol):
    {(id, mode): [[[site id, hex padded to whole words], ...] per op]}, and
    per-trace problems for records from undeclared consumers."""
    dispatch = dispatch or {}
    resolved, problems, meta = {}, {}, {}
    skipped = Counter()
    for key, ops in per.items():
        out, labels = [], []
        for index, op in enumerate(ops):
            recs, op_labels = [], []
            for raw_kind, ip, seq, length, data, func in op:
                frames = [f['source'].split('/.deps/linux/')[-1].split(' ')[0] for f in locations.get(ip, [])]
                if raw_kind == 0xffff:   # the kernel's steering mismatch marker
                    problems.setdefault(key[0], []).append(dict(index=index, label='steering',
                        problem='a scheduled site met an entry it does not match', call_chain=frames))
                    continue
                kind, steered = raw_kind & 0x7fff, bool(raw_kind & 0x8000)
                consumer = next((src for src in frames if src.split(':')[0] not in CHOICE_HELPERS), None)
                kind_class = 'random' if kind in RANDOM_KINDS else 'clock' if 200 <= kind <= 216 \
                    else 'resched' if raw_kind == RESCHED else 'timer' if raw_kind == TIMER_ARM \
                    else 'advance' if raw_kind == TIME_ADVANCE else 'alloc' if kind == ALLOC_KIND \
                    else 'queue' if raw_kind == QUEUE else 'jiffies' if raw_kind == DST_CACHE_JIFFIES else None
                if kind_class == 'queue':
                    # {work, func}: the site is the queued function's symbol
                    queued_func = int.from_bytes(bytes.fromhex(data[16:32]), 'little') if length == 16 else 0
                    consumer = f'{dispatch.get(queued_func)}:0'
                    frames = [dispatch.get(queued_func, hex(queued_func))]
                if kind_class == 'alloc':
                    # the consumer frame by the unwound chain (docs/2026-10-05-a-alloc.md 4.2)
                    frames, consumer = alloc_frames(ip, data, locations)
                if raw_kind in (SECTION_START, SECTION_STOP):
                    kind_class = 'section'
                    consumer = f'{dispatch.get(func)}:{raw_kind - SECTION_START}'
                    frames = [dispatch.get(func, hex(func))]
                    if raw_kind == SECTION_STOP and int.from_bytes(bytes.fromhex(data), 'little'):
                        problems.setdefault(key[0], []).append(dict(index=index, label='section',
                            problem='records dropped in a dispatch section', call_chain=frames))
                entry = sites.get((kind_class, consumer)) if kind_class else None
                if entry is None or length != entry['len']:
                    problems.setdefault(key[0], []).append(dict(index=index, label=f'choice kind {kind}',
                        problem='choice from an undeclared consumer', call_chain=frames, length=length))
                    continue
                recs.append([entry['id'], data + '0' * (-len(data) % 16)])
                op_labels.append((entry['label'], steered, data, kind_class))
                if entry['role'] != 'mirror' and key[1] == 'pc':
                    skipped[f"{entry['role']}:{entry['label']}"] += 1
            out.append(recs)
            labels.append(op_labels)
        resolved[key] = out
        meta[key] = labels
    return resolved, problems, skipped, meta


def alloc_chain(data):
    """A kind-305 record's unwound return addresses (words 1-4), as the
    hex addresses the symbolization keys use."""
    words = [int.from_bytes(bytes.fromhex(data[16 * i:16 * i + 16]), 'little') for i in range(1, 5)]
    return [f'0x{w:x}' for w in words if w]


def alloc_frames(ip, data, locations):
    """The symbolized frames of an allocation record (its address, then its
    chain) and its consumer frame: the first frame outside the choice and
    allocation helpers (files, and functions by name)."""
    frames, consumer = [], None
    for address in [ip] + alloc_chain(data):
        for f in locations.get(address, []):
            source = f['source'].split('/.deps/linux/')[-1].split(' ')[0]
            frames.append(source)
            if consumer is None and source.split(':')[0] not in ALLOC_HELPER_FILES + CHOICE_HELPERS \
                    and f['function'] not in ALLOC_HELPER_FUNCTIONS:
                consumer = source
    return frames, consumer


def steering_problems(traces, meta, status_rows):
    """For each steered trace and guest child: the kernel consumed the whole
    schedule with no mismatch, and the records at the scheduled sites are the
    schedule, entry for entry (a value entry: steered, that value; a draw
    entry: not steered). For an allocation entry the value compared is the
    outcome byte of word 0: the rest of the payload (gfp, size, chain) is
    build-specific attribution, not schedule."""
    problems = {}
    status = {(r['id'], r['mode']): r for r in status_rows}
    for trace in traces:
        if 'steer' not in trace:
            continue
        sites = {label for label, _ in trace['steer']}
        want = [(label, value != 'draw', value) for label, value in trace['steer']]
        for mode in ('pc', 'cmp'):
            row = status.get((trace['id'], mode))
            if row is None or row['remaining'] or row['mismatches']:
                problems.setdefault(trace['id'], []).append(dict(index=None, label='steering',
                    problem='the schedule was not consumed exactly', mode=mode, status=row))
            got = [(label, steered, data[:2] if kind_class == 'alloc' else data)
                   for op in meta.get((trace['id'], mode), []) for label, steered, data, kind_class in op
                   if label in sites]
            want_mode = [(label, steered, value[:2] if label in ALLOC_SITES else value) for label, steered, value in want]
            if len(got) != len(want_mode) or any(g[0] != w[0] or g[1] != w[1] or (w[1] and g[2] != w[2])
                                                 for g, w in zip(got, want_mode)):
                problems.setdefault(trace['id'], []).append(dict(index=None, label='steering',
                    problem='the records at scheduled sites are not the schedule', mode=mode,
                    records=[[g[0], g[1]] for g in got][:16]))
    return problems


def section_problems(per, status_rows):
    """For each network trace and guest child: every dispatch section the
    kernel opened reached the trace's records. A section whose block was
    moved after its operation's readout (a worker outliving the guest's
    wait) is otherwise lost without a signal; the mirror would then pass if
    it did not expect that unit either."""
    problems = {}
    for row in status_rows:
        ops = per.get((row['id'], row['mode']))
        starts = sum(1 for op in ops or [] for r in op if r[0] == SECTION_START)
        if ops is None or starts != row['opened']:
            problems.setdefault(row['id'], []).append(dict(index=None, label='section',
                problem='dispatch sections opened but not recorded', mode=row['mode'],
                opened=row['opened'], recorded=starts))
    return problems


# The guest's real-time bound in ticks (REKEY_BOUND_NS, 4.5 s at HZ 250, from
# just before wg_up): the natural progress of `jiffies` over a trace, the
# advances excluded.
JIFFIES_BOUND = 1125
# Slack for the ticks outside the bounded span (the absorbing tick of each
# advance counts as real time; the first record may precede wg_up).
JIFFIES_SLACK = 25


def jiffies_problems(traces, per):
    """The `jiffies`-progress check (D3, section 4.4) over each child's
    arm (303: {jiffies, expires, timer}) and advance (304: {before, after})
    records in sequence order:
    - every wg_advance has exactly one 304, first in its operation, with
      after - before = ticks, and no other operation has one (a 304 after
      the timers it released means a tick ran them between the jump and the
      record: the mirror would consume them in the wrong order);
    - `jiffies` never goes back: each record's value is at least the last
      known one (a 304's `after` becomes the last known);
    - an arm after an advance in the same operation sees at least `after + 1`
      (the tick that absorbs the jump comes before any callback or worker);
    - the natural progress over the trace (the jumps excluded) stays within
      the real-time bound.
    A tick handler that re-counted the jump, or an advance recorded wrongly,
    fails here before any mirror runs."""
    ops_of = {t['id']: t['ops'] for t in traces}
    problems = {}
    for (trace_id, mode), ops in per.items():
        found, last, natural = [], None, 0
        for index, records in enumerate(ops):
            op = ops_of[trace_id][index]
            advances = [r for r in records if r[0] == TIME_ADVANCE]
            if op['op'] == 'wg_advance' and len(advances) != 1:
                found.append(dict(index=index, problem='an advance without exactly one advance record',
                                  records=len(advances)))
            if op['op'] != 'wg_advance' and advances:
                found.append(dict(index=index, problem='an advance record outside wg_advance'))
            if advances and records[0][0] != TIME_ADVANCE:
                # a tick between the jump and its record ran the timers first
                found.append(dict(index=index, problem='records before the advance record',
                                  kinds=[r[0] for r in records[:records.index(advances[0])]][:8]))
            floor = None
            for kind, _ip, _seq, length, data, _func in records:
                if kind not in (TIMER_ARM, TIME_ADVANCE):
                    continue
                if length != (24 if kind == TIMER_ARM else 16):
                    found.append(dict(index=index, problem=f'record kind {kind} length {length}'))
                    continue
                first, second = (int.from_bytes(bytes.fromhex(data[k:k + 16]), 'little') for k in (0, 16))
                if last is not None and first < last:
                    found.append(dict(index=index, problem='jiffies went back', last=last, jiffies=first, kind=kind))
                elif last is not None:
                    natural += first - last
                if kind == TIME_ADVANCE:
                    if op['op'] == 'wg_advance' and second - first != op['ticks']:
                        found.append(dict(index=index, problem='the advance moved jiffies by another amount',
                                          before=first, after=second, ticks=op['ticks']))
                    last = floor = second
                    continue
                if floor is not None and first < floor + 1:
                    found.append(dict(index=index, problem='an arm after an advance before its absorbing tick',
                                      after=floor, jiffies=first))
                last = first
        if natural > JIFFIES_BOUND + JIFFIES_SLACK:
            found.append(dict(index=None, problem='jiffies progressed beyond the real-time bound',
                              natural=natural, bound=JIFFIES_BOUND))
        if found:
            problems.setdefault(trace_id, []).extend(dict(p, label='jiffies', mode=mode) for p in found)
    return problems


def dispatch_problems(per):
    """The dispatch-order pairing (docs/2026-10-11-dispatch-order.md), per
    child, over the records in sequence order: a work item's queue record
    (307: {work, func}) or a timer's arm record (303: {jiffies, expires,
    timer}) names a unit; the section start that dispatches it (300: {func,
    unit}) must name a unit queued or armed earlier in the trace and not
    dispatched since, which it then consumes (a re-arm moves a timer, a
    re-queue of a running item queues it again). A softirq section (unit
    0 for net_rx_action) is paired with nothing; any other section without
    a unit is a kernel without the identity. Returns the problems, and per
    (trace, mode) the units still queued or armed at the trace's end
    (reported, not a failure: an unfired timer, or work the mirror already
    refuses as having outlived the guest's wait)."""
    problems, leftovers = {}, {}
    for (trace_id, mode), ops in per.items():
        pending, found = {}, []
        for index, records in enumerate(ops):
            for kind, _ip, _seq, length, data, func in records:
                raw = kind & 0x7fff
                if raw == QUEUE and length == 16:
                    unit = int.from_bytes(bytes.fromhex(data[:16]), 'little')
                    if unit in pending and pending[unit] == 'work':
                        found.append(dict(index=index, problem='a work item queued while already queued', unit=hex(unit)))
                    pending[unit] = 'work'
                elif raw == TIMER_ARM and length == 24:
                    pending[int.from_bytes(bytes.fromhex(data[32:48]), 'little')] = 'timer'
                elif raw == SECTION_START and length == 16:
                    unit = int.from_bytes(bytes.fromhex(data[16:32]), 'little')
                    if unit == 0:
                        if func is not None and func not in SOFTIRQ_FUNCS:
                            found.append(dict(index=index, problem='a dispatch section without its unit', function=hex(func)))
                    elif unit not in pending:
                        found.append(dict(index=index, problem='a dispatched unit that was never queued or armed', unit=hex(unit)))
                    else:
                        del pending[unit]
        if found:
            problems.setdefault(trace_id, []).extend(dict(p, label='dispatch', mode=mode) for p in found)
        if pending:
            leftovers[(trace_id, mode)] = dict(Counter(pending.values()))
    return problems, leftovers


# The dispatched functions whose sections name no unit: the NET_RX vector
# (handle_softirqs passes NULL); set by run_chunk from the dispatch map.
SOFTIRQ_FUNCS = set()


def load_decisions(config):
    """The mirror's decision table (`leanux-model --decisions`), validated."""
    result = subprocess.run([MODEL, '--decisions'], capture_output=True, timeout=60)
    if result.returncode:
        raise InvalidOutput('leanux-model --decisions failed')
    return parse_decisions(loads(result.stdout.decode()), config)


def parse_decisions(decisions, config):
    if type(decisions) is not list or not decisions:
        raise InvalidOutput('empty decision table')
    table = {}
    for entry in decisions:
        if set(entry) != {'label', 'file', 'line', 'when_true', 'when_false', 'repeatable', 'comparison'} \
                or type(entry['repeatable']) is not bool:
            raise InvalidOutput(f'decision fields: {entry}')
        label = entry['label']
        if type(label) is not str or label in table or entry['file'] not in config['files']:
            raise InvalidOutput(f'decision {label}: duplicate label or unanchored file')
        if type(entry['line']) is not int or non_statement(f"{entry['file']}:{entry['line']}"):
            raise InvalidOutput(f'decision {label}: condition line must be a source statement')
        comparison = entry['comparison']
        if comparison is not None and (set(comparison) != {'rel', 'const_rhs', 'site', 'assigned'}
                                       or comparison['rel'] not in RELATIONS
                                       or type(comparison['const_rhs']) is not bool
                                       or type(comparison['assigned']) is not bool):
            raise InvalidOutput(f'decision {label}: comparison spec')
        if comparison is not None and comparison['site'] is not None:
            site_file, _, site_line = comparison['site'].rpartition(':')
            if site_file != entry['file'] or not site_line.isdigit():
                raise InvalidOutput(f'decision {label}: comparison site file')
            # a comparison in the condition is within two lines of it; one
            # assigned to a local the condition tests precedes it closely
            near = (0 < entry['line'] - int(site_line) <= 6) if comparison['assigned'] \
                else abs(int(site_line) - entry['line']) <= 2
            if not near:
                raise InvalidOutput(f'decision {label}: comparison site must be within two lines of the condition'
                                    ' (or, assigned, precede it within six)')
        spans = {}
        for outcome, key in ((True, 'when_true'), (False, 'when_false')):
            lines = set()
            for span in entry[key]:
                if set(span) != {'file', 'lo', 'hi'} or span['file'] not in config['files']:
                    raise InvalidOutput(f'decision {label}: span fields or file')
                if type(span['lo']) is not int or type(span['hi']) is not int or not 1 <= span['lo'] <= span['hi']:
                    raise InvalidOutput(f'decision {label}: span bounds')
                # Spans stay near their condition: within the enclosing C function.
                if not entry['line'] - SPAN_WINDOW[0] <= span['lo'] and span['hi'] <= entry['line'] + SPAN_WINDOW[1]:
                    raise InvalidOutput(f'decision {label}: span {span} too far from line {entry["line"]}')
                lines.update(f"{span['file']}:{n}" for n in range(span['lo'], span['hi'] + 1))
            spans[outcome] = {line for line in lines if not non_statement(line)}
        if spans[True] & spans[False]:
            raise InvalidOutput(f'decision {label}: outcome spans overlap')
        table[label] = dict(site=f"{entry['file']}:{entry['line']}", spans=spans,
                            function=label.split('.', 1)[0], comparison=comparison, repeatable=entry['repeatable'])
    return table


def witness_table(decisions, instrumented, functions, branch_free_functions=()):
    """Witnesses are the instrumented lines of each outcome span. An outcome
    without witnesses is unobservable; the report counts these (no declared
    reason is required, user decision 2026-09-30). Each decision's C function
    (the label prefix) must own instrumentation, so reaching it is checkable,
    unless the configuration lists it as branch-free."""
    table, problems = {}, []
    for label, entry in decisions.items():
        table[label] = {o: entry['spans'][o] & instrumented for o in (True, False)}
        if entry['function'] not in functions and entry['function'] not in branch_free_functions:
            problems.append(f'{label}: C function {entry["function"]} owns no instrumentation point')
    if problems:
        raise InvalidOutput('decision table does not match the instrumented kernel:\n  ' + '\n  '.join(problems))
    return table


def op_lines(row, locations, files):
    return set(line_positions(row, locations, files))


def raw_lines(row, locations, files):
    """Every anchored line in the operation's coverage, from any function and
    any attribution."""
    lines = set()
    for pc in row['pcs']:
        for frame in locations[pc]:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files:
                lines.add(source)
    return lines


def unlisted_c_lines(row, locations, files, functions):
    """Anchored `.c` lines run by attributable PCs of unlisted functions."""
    lines = set()
    for pc in row['pcs']:
        frames = locations[pc]
        if not attributable(frames) or listed(frames, functions):
            continue
        for frame in frames:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files and source.split(':')[0].endswith('.c'):
                lines.add(source)
    return lines


def frame_chain(frames):
    """A point's DWARF frames as `file:line` strings, innermost first."""
    return tuple(frame['source'].split('/.deps/linux/')[-1].split(' ')[0] for frame in frames)


def decision_functions_run(row, locations, config, decisions):
    """Decision functions (label prefixes) with a frame, in an anchored file,
    of a PC that witnesses decisions (attributable, in a listed function),
    and how many of the row's PCs are declared shared exits.

    A declared shared exit (`kcov.json` `shared_exits`) is one point, named
    by its exact frame chain, that the compiler shares between a function's
    early returns and an inlined helper's exit; the line table attributes it
    to the helper. When the operation did not cover the declared
    `unless_covered` point (the block that enters the helper on its own
    path), the early returns reached it and the helper did not run: then,
    and only then, that helper's frame at that exact point is not counted as
    the helper running."""
    functions = {entry['function'] for entry in decisions.values()}
    listed_functions = set(config['functions'])
    covered = {frame_chain(locations[pc]) for pc in row['pcs']}
    shared = {tuple(e['frames']): e['function'] for e in config['shared_exits']
              if tuple(e['unless_covered']) not in covered}
    ran, shared_hits = set(), 0
    for pc in row['pcs']:
        frames = locations[pc]
        if not attributable(frames) or not listed(frames, listed_functions):
            continue
        exempt = shared.get(frame_chain(frames))
        shared_hits += exempt is not None
        for frame in frames:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0].split(':')[0]
            if frame['function'] in functions and source in config['files'] and frame['function'] != exempt:
                ran.add(frame['function'])
    return ran, shared_hits


def listed(frames, functions):
    """Whether a PC belongs to one of the configured functions: its outermost
    DWARF frame, which names the symbol. Header helpers are inlined into
    unmodeled code too (refcounts on the netlink core's skbs), so only these
    PCs witness decisions, as only these PCs define the instrumentation map."""
    return frames[-1]['function'].split('.')[0] in functions


def line_positions(row, locations, files, functions=None):
    """Each anchored line's first position in the operation's coverage, from
    PCs in `functions` when given. The guest records each PC once, at its
    first execution, in execution order."""
    positions = {}
    for position, pc in enumerate(row['pcs']):
        if not attributable(locations[pc]):
            continue
        if functions is not None and not listed(locations[pc], functions):
            continue
        for frame in locations[pc]:
            source = frame['source'].split('/.deps/linux/')[-1].split(' ')[0]
            if source.split(':')[0] in files:
                positions.setdefault(source, position)
    return positions


def parse_step(label):
    name, sep, outcome = label.rpartition('=')
    if not sep or outcome not in ('0', '1'):
        return None
    return name, outcome == '1'


def control_flow(trace, model_obs, coverage, locations, config, decisions, witnesses, instrumented, functions):
    """A2: the mirror's decision outcomes agree with Linux KCOV coverage.

    For each operation: each decision is reported at most once; a reported
    outcome must cover one of its
    witnesses; the opposite outcome's witnesses must be uncovered; and a
    decision the mirror did not report must have no covered witness at all.
    """
    steps = {}
    for branch in model_obs['branches']:
        steps.setdefault(branch['index'], []).append(branch['label'])
    span_lines = set().union(*(e['spans'][o] for e in decisions.values() for o in (True, False)))
    problems, gaps = [], Counter()
    order_stats = Counter()
    for index, op in enumerate(trace['ops']):
        # E-B (docs/2026-10-05-e-dos.md §4.1): a `wg_flood` runs the receive
        # worker as a discarded section whose per-packet coverage is
        # scheduling-driven and not modeled (the mirror reports no decisions for
        # it). The one checked control-flow effect is that the flood crossed the
        # threshold: receive.c:115 (last_under_load = now) is covered.
        if op['op'] == 'wg_flood':
            covered = raw_lines(coverage[index], locations, config['files'])
            if 'drivers/net/wireguard/receive.c:115' not in covered:
                problems.append(dict(index=index,
                                     problem='flood did not reach under_load (receive.c:115 not covered)'))
            continue
        # Raw coverage of a span line (any function, any attribution) must be
        # mapped, and no unlisted function may run span lines of an anchored
        # C file: either means a modeled path runs outside the listed
        # functions. (Header helpers are inlined everywhere, so header span
        # lines in unlisted functions are a stated gap.)
        unmapped = sorted((raw_lines(coverage[index], locations, config['files']) & span_lines) - instrumented)
        foreign = sorted(unlisted_c_lines(coverage[index], locations, config['files'], set(config['functions']))
                         & span_lines)
        if foreign:
            problems.append(dict(index=index, problem='span lines covered by an unlisted function', lines=foreign))
        positions = line_positions(coverage[index], locations, config['files'], set(config['functions']))
        lines = set(positions)
        if not lines:
            problems.append(dict(index=index, problem='no coverage in anchored files'))
        if unmapped:
            problems.append(dict(index=index, problem='covered span lines missing from the instrumentation map',
                                 lines=unmapped))
        reported, sequence = set(), []
        for label in steps.get(index, []):
            step = parse_step(label)
            if step is None or step[0] not in decisions:
                problems.append(dict(index=index, label=label, problem='unknown decision'))
            elif any(name == step[0] for name, _ in reported):
                if not decisions[step[0]]['repeatable']:
                    problems.append(dict(index=index, label=label, problem='decision reported more than once'))
                reported.add(step)  # a repeatable decision: later evaluations add outcomes, not order
            else:
                reported.add(step)
                sequence.append(step)
        if not reported:
            problems.append(dict(index=index, problem='no model decision'))
        for name, outcome in sorted(reported):
            own, other = witnesses[name][outcome], witnesses[name][not outcome]
            if own and not (lines & own):
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='outcome not witnessed',
                                     witnesses=sorted(own)))
            both = (name, not outcome) in reported and decisions[name]['repeatable']
            if lines & other and not both:
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='opposite outcome covered',
                                     covered=sorted(lines & other)))
        # Order: within each C function, witnessed decisions appear in the
        # mirror's order at their first witness in Linux's execution. (Across
        # functions an arm's first witness can follow a nested call's
        # decisions, so positions are only comparable within a function.)
        previous = {}
        for name, outcome in sequence:
            covered = witnesses[name][outcome] & lines
            if not covered:
                order_stats['unwitnessed'] += 1
                continue
            here = min(positions[line] for line in covered)
            function = decisions[name]['function']
            if function in previous:
                order_stats['compared'] += 1
                order_stats['ties'] += here == previous[function][1]
            if function in previous and here < previous[function][1]:
                problems.append(dict(index=index, label=f'{name}={int(outcome)}', problem='decision order differs from Linux',
                                     after=previous[function][0], linux_position=here,
                                     previous_position=previous[function][1]))
            previous[function] = (f'{name}={int(outcome)}', here)
        names = {name for name, _ in reported}
        # Function reached: a decision function Linux ran (any frame of a
        # counted point, in an anchored file) must have a reported decision.
        # Unobservable outcomes cannot show an omitted decision; this shows an
        # omitted function.
        ran, shared_hits = decision_functions_run(coverage[index], locations, config, decisions)
        if shared_hits:
            gaps['shared exits reached by an early return (kcov.json)'] += shared_hits
        silent = sorted(ran - {decisions[name]['function'] for name in names})
        if silent:
            problems.append(dict(index=index, problem='Linux ran a decision function the mirror reported nothing in',
                                 functions=silent))
        for name, sides in witnesses.items():
            if name not in names and lines & (sides[True] | sides[False]):
                problems.append(dict(index=index, label=name, problem='Linux evaluated an unreported decision',
                                     covered=sorted(lines & (sides[True] | sides[False]))))
        for gap in config['known_gaps']:
            if gap['op'] == op['op'] and gap['line'] in lines:
                gaps[gap['name']] += 1
    gaps.update({f'order: {k}': v for k, v in order_stats.items()})
    return problems, gaps


KCOV_CMP_CONST = 1
RELATIONS = ('lt', 'le', 'gt', 'ge', 'eq', 'ne', 'flag')
# The constants a compiler may use for `x REL c`: `x < c` becomes `x <= c-1`,
# `x <= c` becomes `x < c+1`, and so on; equality and mask tests are exact.
CONSTANT_SHIFTS = {'lt': (0, -1), 'le': (0, 1), 'gt': (0, 1), 'ge': (0, -1), 'eq': (0,), 'ne': (0,), 'flag': (0,)}


def encode(value, bits):
    """`value` as a `bits`-wide C value, or None if it does not fit."""
    if 0 <= value < 1 << bits:
        return value
    if -(1 << (bits - 1)) <= value < 0:
        return value & ((1 << bits) - 1)
    return None


def operands_match(lhs, rhs, record, comparison):
    """Whether a `KCOV_TRACE_CMP` record (type, arg1, arg2) is the C comparison
    `lhs REL rhs` the mirror declares. Operands must fit the recorded width
    (type bits 1-2: log2 bytes). A constant record (KCOV puts the constant in
    arg1) needs a declared constant right-hand side: the variable must equal
    `lhs` exactly and the constant may be shifted only as the relation allows.
    A non-constant record may list the operands in either order, because the
    compiler canonicalizes operand order (`nr < max_fds` is recorded as
    `(max_fds, nr)`)."""
    kind, x, y = record
    bits = 8 << (kind >> 1)
    a, b = encode(lhs, bits), encode(rhs, bits)
    if a is None or b is None:
        return False
    if kind & KCOV_CMP_CONST:
        if not comparison['const_rhs']:
            return False
        return y == a and any(x == (rhs + shift) & ((1 << bits) - 1) for shift in CONSTANT_SHIFTS[comparison['rel']])
    return sorted((x, y)) == sorted((a, b))


def operand_agreement(trace, model_obs, comparisons, locations, decisions, functions=None, exclusions=(),
                      excluded=None):
    """A3: declared value comparisons report operands, and each matches a
    comparison Linux made at the decision's condition line (the innermost
    source frame of the comparison) in the same operation, in one of the
    configured `functions` when given.

    A declared operand exclusion (`kcov.json` `operand_exclusions`) is one
    call site whose operand is a guest-wide value the mirror does not model:
    the mirror reports the outcome with `operands_excluded` naming the
    operand instead of the pair. It must name a declared (label, operand),
    and Linux must have recorded the comparison at the condition line with
    the declared call line as the outermost frame, once for each such report
    in the operation. `excluded` (a Counter) receives the count."""
    problems, checked = [], 0
    used = Counter()
    for branch in model_obs['branches']:
        name = branch['label'].rpartition('=')[0]
        if name not in decisions:
            continue  # control_flow reports unknown labels
        comparison = decisions[name]['comparison']
        if 'operands_excluded' in branch:
            entry = next((e for e in exclusions
                          if e['label'] == name and e['operand'] == branch['operands_excluded']), None)
            if comparison is None or 'operands' in branch or entry is None:
                problems.append(dict(index=branch['index'], label=branch['label'],
                                     problem='undeclared operand exclusion', operand=branch['operands_excluded']))
                continue
            site = comparison['site'] or decisions[name]['site']
            at_call = sum(1 for r in comparisons[branch['index']]['records']
                          if frame_chain(locations[r[3]])[0] == site and frame_chain(locations[r[3]])[-1] == entry['call']
                          and attributable(locations[r[3]])
                          and (functions is None or listed(locations[r[3]], functions)))
            used[(branch['index'], name)] += 1
            if used[(branch['index'], name)] > at_call:
                problems.append(dict(index=branch['index'], label=branch['label'],
                                     problem='operand exclusion without a comparison at its declared call site',
                                     site=site, call=entry['call'], linux_records_at_call=at_call))
            elif excluded is not None:
                excluded[f"operands excluded: {name} at {entry['call']} ({entry['operand']})"] += 1
            continue
        if comparison is None:
            if 'operands' in branch:
                problems.append(dict(index=branch['index'], label=branch['label'],
                                     problem='operands on a decision not declared a comparison'))
            continue
        if 'operands' not in branch:
            problems.append(dict(index=branch['index'], label=branch['label'],
                                 problem='declared comparison reported without operands'))
            continue
        site = comparison['site'] or decisions[name]['site']
        records = [(r[0], int(r[1], 16), int(r[2], 16)) for r in comparisons[branch['index']]['records']
                   if locations[r[3]][0]['source'].split('/.deps/linux/')[-1].split(' ')[0] == site
                   and attributable(locations[r[3]])
                   and (functions is None or listed(locations[r[3]], functions))]
        lhs, rhs = branch['operands']
        if not records:
            problems.append(dict(index=branch['index'], label=branch['label'], problem='no comparison recorded at condition',
                                 site=site, operands=[lhs, rhs]))
        elif not any(operands_match(lhs, rhs, r, comparison) for r in records):
            problems.append(dict(index=branch['index'], label=branch['label'], problem='operands differ from Linux',
                                 site=site, operands=[lhs, rhs], linux=[[k, hex(x), hex(y)] for k, x, y in records[:6]]))
        else:
            checked += 1
    return problems, checked


# The guest's time budget. A timeout only bounds a hung guest, so the budget
# is generous; a budget that a contended host can exceed makes a correct run
# fail (2026-10-06: 6 of 148 recorded WireGuard-chunk runs timed out at
# 1.00-1.01x the old budget, which did not count wg_inject's wait or the
# queue waits, and 10 more completed at 0.90-0.98x). Two parts:
# - the guest's fixed waits (harness/guest.c), which do not slow down: each
#   of a trace's two children (coverage, comparisons) sleeps OBSERVE_WAIT_US
#   (0.4 s) before wg_observe and after wg_inject, and QUEUE_WAIT_US (0.1 s)
#   after wg_set, wg_up and wg_xmit; D3: a wg_advance waits for the tick
#   before it, then for its absorbing tick (each at most a 4 ms tick), then
#   ADVANCE_WAIT_US (0.1 s), counted as ADVANCE_WAIT_SECONDS; pipes (P design
#   section 6): each pause_ms, exactly;
# - its computation (boot, fixtures, TCG execution), which does: measured on
#   the loaded host (load average 50-100 on 32 CPUs, 3 guests) at most
#   2.0 s per WireGuard trace (both children, boot included) and 0.025 s per
#   operation of other traces, plus, for pipes, an allowance for a read or
#   write's bytes (TCG copies and hashes 64 KiB in well under a millisecond;
#   this is for safety: 1 s per MiB per child), scaled by CONTENTION_FACTOR.
GUEST_CHILDREN = 2
OBSERVE_WAIT_SECONDS = 0.4
QUEUE_WAIT_SECONDS = 0.1
ADVANCE_WAIT_SECONDS = 0.15
PAUSE_SECONDS_PER_MS = 0.001
GUEST_BOOT_SECONDS = 30
WIREGUARD_TRACE_SECONDS = 2.0
OPERATION_SECONDS = 0.03
IO_SECONDS_PER_BYTE = 1 / 2**20
CONTENTION_FACTOR = 3


def guest_timeout(traces):
    ops = [op for trace in traces for op in trace['ops']]
    names = [op['op'] for op in ops]
    # E-B: a wg_flood waits QUEUE_WAIT_US after its submission (harness/guest.c)
    waits = GUEST_CHILDREN * (OBSERVE_WAIT_SECONDS * sum(op in ('wg_observe', 'wg_inject') for op in names)
                              + QUEUE_WAIT_SECONDS * sum(op in ('wg_set', 'wg_up', 'wg_xmit', 'wg_flood') for op in names)
                              + ADVANCE_WAIT_SECONDS * sum(op == 'wg_advance' for op in names)
                              + PAUSE_SECONDS_PER_MS * sum(op.get('pause_ms', 0) for op in ops))
    io_bytes = sum(op['count'] for op in ops if op['op'] in ('read', 'write'))
    compute = (GUEST_BOOT_SECONDS + WIREGUARD_TRACE_SECONDS * sum(uses_wireguard(t) for t in traces)
               + OPERATION_SECONDS * len(ops) + GUEST_CHILDREN * IO_SECONDS_PER_BYTE * io_bytes)
    return round(waits + CONTENTION_FACTOR * compute)


# Outcomes of the guest's infrastructure, not of Linux's or the mirror's
# behavior: a chunk that fails with one of them (every trace alike) is run
# once more, and the report records it (`chunk_retries`). output_limit is
# deterministic and is split instead; a mismatch of any kind is never rerun.
RETRIED_OUTCOMES = ('timeout', 'resource_busy')


# Env.napiIrqExit: a NAPI poll whose records leave its placement open (inside
# wg_queue_enqueue_per_peer_rx, holding its peer reference, or after it) is a
# choice the mirror reports and the check enumerates: each choice vector is one
# complete execution, and the comparison child's operands must agree with one
# of them. Up to this many open placements per trace are enumerated; beyond,
# the mismatch stands.
NAPI_PLACEMENTS_MAX = 3


def napi_placements(trace, hidden_traces, actual_cmp, out, trace_comparisons, locations, kcov):
    """The first other placement vector under which the comparison child's
    operands agree: (choice, observation, problems, checked, excluded), or
    None."""
    count = actual_cmp['napi_irq_ambiguous']
    if count > NAPI_PLACEMENTS_MAX:
        return None
    with_records = next(t for t in hidden_traces if t['id'] == trace['id'])
    for bits in range(1, 2 ** count):
        choice = [bool(bits >> i & 1) for i in range(count)]
        where = out / f'model-cmp-napi-{trace["id"]}-{bits}'
        where.mkdir()
        try:
            [alternative] = run_model([dict(with_records, napi_irq_before_put=choice)], where)
        except (InvalidOutput, OSError, subprocess.SubprocessError):
            continue
        if alternative.get('napi_irq_ambiguous') != count:
            continue
        if [o['ret'] for o in alternative['observations']] != [o['ret'] for o in actual_cmp['observations']]:
            continue
        excluded = Counter()
        problems, checked = operand_agreement(trace, alternative, trace_comparisons, locations, kcov[1],
                                              set(kcov[0]['functions']), kcov[0]['operand_exclusions'], excluded)
        if not problems:
            return choice, alternative, problems, checked, excluded
    return None


def run_chunk(traces, out, kcov, guest_variant=None, alloc_flags=0, arm=()):
    """`alloc_flags`: the allocation load flags of an armed chunk; nonzero
    only for the control kernel's controls, which the oracle rejects. `arm`:
    allocation sites to arm without steering them (a control's armed run of
    an FS trace, which the guest cannot steer). Both are for
    scripts/alloc-evaluator-controls.py only."""
    out.mkdir(parents=True)
    results, gaps = {}, Counter()
    outcomes = Counter()
    try:
        sites_by_key = load_hidden_sites()
        # the mirror's section sites name functions of the dispatch set
        if not {e['file'] for e in sites_by_key.values() if e['kind'] == 'section'} <= set(DISPATCH_SYMBOLS):
            raise InvalidOutput('a section site outside the dispatch set')
        steer_wire, alloc, armed_labels = {}, None, []
        if any('steer' in t for t in traces) or arm:
            by_label = {entry['label']: entry for entry in sites_by_key.values()}
            calls = call_sites(KERNEL / 'vmlinux', LINUX_ARTIFACTS / 'cache')
            steered_alloc = {label for t in traces for label, _ in t.get('steer', []) if label in ALLOC_SITES} | set(arm)
            # A chunk with a steered allocation site is armed with those
            # sites' ranges (every trace in it then records their
            # candidates); others stay disarmed (section 6.6).
            alloc_sites = alloc_call_sites(KERNEL / 'vmlinux', LINUX_ARTIFACTS / 'cache') if steered_alloc else None
            steer_wire = {t['id']: resolve_steering(t, by_label, calls, alloc_sites) for t in traces if 'steer' in t}
            if steered_alloc:
                alloc = {'flags': alloc_flags, 'ranges': alloc_ranges(steered_alloc, alloc_sites)}
                # the sites whose records every trace of the chunk carries
                armed_labels = alloc_armed_labels(alloc['ranges'], alloc_sites)
        # one arm-record switch for the kernel (the wire's `A` line) and the
        # mirror (the input's `arm_records`)
        linux = run_linux(traces, out / 'linux', timeout=guest_timeout(traces), steer_wire=steer_wire,
                          arm_records=ARM_RECORDS, guest_variant=guest_variant, alloc=alloc)
        coverage = [loads(line) for line in (out / 'linux/coverage.jsonl').read_text().splitlines()]
        validate_coverage(traces, coverage)
        mapped = symbolize(coverage, KERNEL / 'vmlinux')
        (out / 'linux/coverage-map.json').write_text(json.dumps(mapped, indent=1) + '\n')
        comparisons = [loads(line) for line in (out / 'linux/comparisons.jsonl').read_text().splitlines()]
        compared = symbolize([{'pcs': sorted({r[3] for row in comparisons for r in row['records']})}],
                             KERNEL / 'vmlinux')
        (out / 'linux/comparison-map.json').write_text(json.dumps(compared, indent=1) + '\n')
        hidden_path = out / 'linux/hidden.jsonl'
        rows = [loads(line) for line in hidden_path.read_text().splitlines()] if hidden_path.exists() else []
        per = hidden_records(traces, rows)
        ips = sorted({r[1] for ops in per.values() for op in ops for r in op}
                     | {a for ops in per.values() for op in ops for r in op if r[0] & 0x7fff == ALLOC_KIND
                        for a in alloc_chain(r[4])})
        called = symbolize([{'pcs': ips}], KERNEL / 'vmlinux') if ips else {'locations': {}}
        dispatch = {}
        if any(uses_wireguard(t) for t in traces):
            dispatch = dict(zip(dispatch_addresses(KERNEL), DISPATCH_SYMBOLS))
        records, site_problems, skipped, meta = resolve_choices(per, sites_by_key, called['locations'], dispatch)
        steer_path = out / 'linux/steering.jsonl'
        status_rows = [loads(line) for line in steer_path.read_text().splitlines()] if steer_path.exists() else []
        for trace_id, found in steering_problems(traces, meta, status_rows).items():
            site_problems.setdefault(trace_id, []).extend(found)
        sections_path = out / 'linux/sections.jsonl'
        section_rows = [loads(line) for line in sections_path.read_text().splitlines()] if sections_path.exists() else []
        for trace_id, found in section_problems(per, section_rows).items():
            site_problems.setdefault(trace_id, []).extend(found)
        for trace_id, found in jiffies_problems(traces, per).items():
            site_problems.setdefault(trace_id, []).extend(found)
        SOFTIRQ_FUNCS.clear()
        SOFTIRQ_FUNCS.update(a for a, name in dispatch.items() if name == 'net_rx_action')
        dispatch_found, left = dispatch_problems(per)
        for trace_id, found in dispatch_found.items():
            site_problems.setdefault(trace_id, []).extend(found)
        for counts in left.values():
            for unit_kind, n in counts.items():
                outcomes[f'dispatch units left {unit_kind == "timer" and "armed" or "queued"}'] += n
        outcomes.update({f'choice records skipped ({k})': n for k, n in skipped.items()})
        # the transitional unarmed answer (docs/2026-10-05-a-alloc.md 6.6) is
        # declared: the report counts the traces each way
        outcomes['alloc runs (armed)' if armed_labels else 'alloc runs (unarmed)'] += len(traces)
    except LinuxRunError as exc:
        return {t['id']: dict(id=t['id'], outcome=exc.kind, side='linux', detail=str(exc)) for t in traces}, gaps, outcomes
    except SteeringError as exc:
        return {t['id']: dict(id=t['id'], outcome='invalid_input', side='linux', detail=str(exc)) for t in traces}, gaps, outcomes
    except (InvalidOutput, ValueError, OSError, subprocess.SubprocessError) as exc:
        return {t['id']: dict(id=t['id'], outcome='invalid_coverage', side='linux', detail=str(exc)) for t in traces}, gaps, outcomes
    # The mirror runs once with each guest child's hidden-input records: the
    # coverage child's run is compared for behavior and control flow, the
    # comparison child's for operands (docs/2026-10-03-hidden-inputs-design.md).
    def with_hidden(mode):
        armed = dict(alloc_armed=armed_labels) if armed_labels else {}
        return [dict(t, hidden=records[(t['id'], mode)], arm_records=ARM_RECORDS, **armed)
                if (t['id'], mode) in records else t for t in traces]
    try:
        (out / 'model').mkdir()
        model = run_model(with_hidden('pc'), out / 'model')
        if records:
            (out / 'model-cmp').mkdir()
            model_cmp = run_model(with_hidden('cmp'), out / 'model-cmp')
        else:
            model_cmp = model
    except (InvalidOutput, OSError, subprocess.SubprocessError) as exc:
        kind = getattr(exc, 'kind', 'invalid_output')
        return {t['id']: dict(id=t['id'], outcome=kind, side='model', detail=str(exc)) for t in traces}, gaps, outcomes
    rows, cmp_rows = iter(coverage), iter(comparisons)
    for trace, expected, actual, actual_cmp in zip(traces, linux, model, model_cmp):
        trace_coverage = [next(rows) for _ in trace['ops']]
        trace_comparisons = [next(cmp_rows) for _ in trace['ops']]
        result = compare(trace, expected, actual)
        if result['outcome'] == 'agreement':
            problems, trace_gaps = control_flow(trace, actual, trace_coverage, mapped['locations'], *kcov)
            # P: declared operand exclusions are counted with the gaps, from
            # the placement that agrees (D3 merge [AGENT])
            excluded = Counter()
            operand_problems, checked = operand_agreement(trace, actual_cmp, trace_comparisons,
                                                          compared['locations'], kcov[1], set(kcov[0]['functions']),
                                                          kcov[0]['operand_exclusions'], excluded)
            if operand_problems and actual_cmp.get('napi_irq_ambiguous'):
                placed = napi_placements(trace, with_hidden('cmp'), actual_cmp, out, trace_comparisons,
                                         compared['locations'], kcov)
                if placed is not None:
                    choice, actual_cmp, operand_problems, checked, excluded = placed
                    # popped into the report's napi_irq_placements
                    outcomes[f'napi placement ({trace["id"]})'] = sum(1 << i for i, b in enumerate(choice) if b)
            trace_gaps.update(excluded)
            problems += operand_problems + site_problems.get(trace['id'], [])
            # a steered trace states what its steering is for: the mirror's
            # agreeing run (A2 ties it to Linux's coverage) must show it
            # (D3: `fired:<symbol>` names a timer section the mirror's
            # environment ran)
            reported = {b['label'] for b in actual['branches']} \
                | {f"fired:{f['symbol']}" for f in actual.get('fired', [])}
            problems += [dict(index=None, label=label, problem='expected outcome not reached')
                         for label in trace.get('expect', []) if label not in reported]
            # Both children's returns are equal (harness/linux.py); so must be
            # the mirror's under each child's records.
            if [o['ret'] for o in actual_cmp['observations']] != [o['ret'] for o in actual['observations']]:
                problems.append(dict(index=None, label='returns', problem='the comparison run returns differently'))
            outcomes['operand pairs matched'] += checked
            gaps.update(trace_gaps)
            outcomes.update(b['label'] for b in actual['branches'])
            if problems:
                result = dict(id=trace['id'], outcome='control_flow_mismatch', problems=problems)
        results[trace['id']] = result
    return results, gaps, outcomes


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--suite', default=','.join(SUITES))
    parser.add_argument('--generated-count', type=int, default=1000)
    parser.add_argument('--wireguard-count', type=int, default=200)
    parser.add_argument('--pipes-count', type=int, default=200)
    parser.add_argument('--seed', type=int, default=20260920)
    parser.add_argument('--trace')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--no-build', action='store_true', help='reuse the existing .lake build')
    parser.add_argument('--guest-variant', choices=sorted(GUEST_VARIANTS),
                        help='a guest build variant for a negative control (never the oracle)')
    parser.add_argument('--alloc-share', type=float, default=ALLOC_SHARE,
                        help='share of alloc_fail traces among the generated WireGuard traces (0: none, as before A1)')
    args = parser.parse_args(argv)
    suites = args.suite.split(',')
    if not suites or any(s not in SUITES + CONTROL_SUITES for s in suites):
        parser.error(f'--suite must be a comma-separated subset of {SUITES + CONTROL_SUITES}')
    if args.guest_variant and set(suites) - set(CONTROL_SUITES):
        parser.error('--guest-variant runs control suites only')
    artifacts = Path(os.environ.get('LEANUX_ARTIFACTS', ROOT / '.artifacts')).resolve()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out = (args.out or artifacts / 'check' / stamp).resolve()
    if not out.is_relative_to(artifacts) or out == artifacts:
        parser.error(f'--out must be a new directory inside {artifacts}')
    try:
        config = load_kcov_config()
    except (ValueError, OSError) as exc:
        parser.exit(2, f'invalid input: {exc}\n')
    traces, filtered = [], Counter()
    out.mkdir(parents=True, exist_ok=False)
    started = datetime.now(timezone.utc).isoformat()
    results, gaps, build, aborted, identity = {}, Counter(), None, None, None
    outcomes, decisions, kcov, splits, retries = Counter(), {}, None, 0, {}
    try:
        identity = verify_kernel()   # the oracle, or the build LEANUX_KERNEL_IDENTITY names; else no run
        build = build_model(out, rebuild=not args.no_build)
        traces = load_traces(suites, {'generated': args.generated_count, 'wireguard-generated': args.wireguard_count,
                                      'pipes-generated': args.pipes_count},
                             args.seed, args.trace, filtered, args.alloc_share)
        decisions.update(load_decisions(config))
        instrumented, functions, chains = instrumented_lines(KERNEL / 'vmlinux', config['functions'], config['files'])
        # each declared shared exit names exactly one instrumentation point
        for exit_ in config['shared_exits']:
            for chain in (exit_['frames'], exit_['unless_covered']):
                if chains[tuple(chain)] != 1:
                    raise InvalidOutput(f"shared exit {exit_['frames']}: {chain} names {chains[tuple(chain)]}"
                                        ' instrumentation points of the listed functions, not one')
        kcov = (config, decisions, witness_table(decisions, instrumented, functions, config['branch_free_functions']),
                instrumented, functions)
        observable = sum(bool(w[True] or w[False]) for w in kcov[2].values())
        print(f'{len(decisions)} decisions, {observable} with KCOV witnesses', file=sys.stderr)
        pending = list(chunk_traces(traces))
        while pending:
            start, chunk, name = pending.pop(0)
            print(f'traces {start}-{start + len(chunk) - 1} ...', file=sys.stderr, flush=True)
            chunk_results, chunk_gaps, chunk_outcomes = run_chunk(chunk, out / name, kcov, args.guest_variant)
            first = {r.get('outcome') for r in chunk_results.values()}
            if chunk_results and len(first) == 1 and first <= set(RETRIED_OUTCOMES):
                detail = next(iter(chunk_results.values())).get('detail')
                print(f'{name}: {first.pop()} ({detail}); running it once more', file=sys.stderr, flush=True)
                retries[name] = dict(retries=1, first_outcome=next(iter(chunk_results.values()))['outcome'],
                                     detail=detail, rerun=name + '-retry')
                chunk_results, chunk_gaps, chunk_outcomes = run_chunk(chunk, out / (name + '-retry'), kcov,
                                                                      args.guest_variant)
                retries[name]['rerun_outcomes'] = dict(Counter(r.get('outcome') for r in chunk_results.values()))
            # One guest's console output is bounded; a chunk that exceeds it
            # is rerun as two halves (recorded in the report). A single trace
            # that still exceeds it fails.
            if len(chunk) > 1 and chunk_results and all(r.get('outcome') == 'output_limit'
                                                         for r in chunk_results.values()):
                half = len(chunk) // 2
                pending[:0] = [(start, chunk[:half], name + 'a'), (start + half, chunk[half:], name + 'b')]
                splits += 1
                continue
            results.update(chunk_results)
            gaps.update(chunk_gaps)
            outcomes.update(chunk_outcomes)
    except BaseException as exc:  # recorded as an aborted, failing run, then re-raised
        aborted = f'{type(exc).__name__}: {exc}'
        raise
    finally:
        matched = outcomes.pop('operand pairs matched', 0)
        skipped = {k[len('choice records skipped ('):-1]: outcomes.pop(k) for k in list(outcomes)
                   if k.startswith('choice records skipped (')}
        placements = {k[len('napi placement ('):-1]: outcomes.pop(k) for k in list(outcomes)
                      if k.startswith('napi placement (')}
        alloc_runs = {k[len('alloc runs ('):-1]: outcomes.pop(k) for k in list(outcomes) if k.startswith('alloc runs (')}
        status = write_report(out, traces, results, gaps, build, aborted, started, suites, args,
                              decision_summary(decisions, outcomes, kcov[2] if kcov else {}), matched, filtered, splits,
                              skipped, retries, placements, alloc_runs, kernel_identity=identity)
    return 0 if status == 'pass' else 1


def decision_summary(decisions, outcomes, witnesses):
    """How often each decision outcome occurred in agreeing traces, and
    which outcomes KCOV can witness: the map of what the corpus exercises."""
    rows = {}
    for label, entry in decisions.items():
        rows[label] = dict(site=entry['site'], true=outcomes[f'{label}=1'], false=outcomes[f'{label}=0'],
                           witnessed_true=bool(witnesses.get(label, {}).get(True)),
                           witnessed_false=bool(witnesses.get(label, {}).get(False)))
    return dict(decisions=len(rows),
                unobservable_outcomes=sum((not r['witnessed_true']) + (not r['witnessed_false']) for r in rows.values()),
                unobservable_decisions=sorted(l for l, r in rows.items() if not r['witnessed_true'] and not r['witnessed_false']),
                never_evaluated=sorted(l for l, r in rows.items() if not r['true'] + r['false']),
                one_outcome_only=sorted(l for l, r in rows.items() if bool(r['true']) != bool(r['false'])),
                table=rows)


def write_report(out, traces, results, gaps, build, aborted, started, suites, args, decision_coverage=None,
                 operand_pairs_matched=0, domain_filtered=None, chunk_splits=0, choice_records_skipped=None,
                 chunk_retries=None, napi_irq_placements=None, alloc_runs=None, kernel_identity=None):
    ordered = [results.get(trace['id'], dict(id=trace['id'], outcome='not_run')) for trace in traces]
    counts = Counter(r['outcome'] for r in ordered)
    vmlinux = KERNEL / 'vmlinux'
    kernel = dict(vmlinux_sha256=sha256(vmlinux.read_bytes())) if vmlinux.is_file() else dict(missing=str(vmlinux))
    # the identity check's record (harness.linux.verify_kernel): a run that
    # never passed it (aborted before any boot) has none, and fails
    kernel['identity'] = kernel_identity
    passed = (aborted is None and bool(traces) and 'missing' not in kernel and kernel_identity is not None
              and counts == Counter(agreement=len(traces)))
    report = dict(
        version=1, status='pass' if passed else 'fail', aborted=aborted, build=build,
        started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(),
        git=git_state(), model_sources=model_identity(),
        kernel=kernel,
        kcov_config_sha256=sha256(ANCHORS.read_bytes()),
        selection=dict(suites=suites, generated_count=args.generated_count, wireguard_count=args.wireguard_count,
                       pipes_count=getattr(args, 'pipes_count', None), seed=args.seed, trace=args.trace,
                       guest_variant=getattr(args, 'guest_variant', None), alloc_share=getattr(args, 'alloc_share', None)),
        traces=len(traces), operations=sum(len(t['ops']) for t in traces),
        counts=dict(counts), known_gap_hits=dict(gaps), operand_pairs_matched=operand_pairs_matched,
        # cut and ambient choice records (coverage child), by site: consumed
        # without their values, so their growth is visible here
        choice_records_skipped=dict(sorted((choice_records_skipped or {}).items())),
        # traces whose allocation outcomes were consumed from records (armed),
        # and those that ran on the transitional unarmed answer (all ok)
        alloc_runs=dict(sorted((alloc_runs or {}).items())),
        # A2 [USER 2026-10-06]: traces under a declared domain extension. A
        # "failslab" trace forces task-context allocation failures: each
        # failure is in the allocator's output set (the OOM-victim path), but
        # the trace as a whole is not a possible Linux execution
        domain_extensions={ext: sorted(t['id'] for t in traces if t.get('domain_extension') == ext)
                           for ext in sorted({t['domain_extension'] for t in traces if 'domain_extension' in t})},
        domain_filtered=dict(domain_filtered or {}), chunk_splits=chunk_splits,
        # chunks rerun once after an infrastructure outcome (RETRIED_OUTCOMES),
        # by chunk: the first outcome and the rerun's outcomes
        chunk_retries=dict(chunk_retries or {}),
        # traces whose comparison child agreed only under another placement
        # of an open NAPI poll (Env.napiIrqExit): the choice, bit i for the
        # trace's i-th open poll (1: inside wg_queue_enqueue_per_peer_rx)
        napi_irq_placements=dict(sorted((napi_irq_placements or {}).items())),
        decision_coverage=decision_coverage,
        failures=[r for r in ordered if r['outcome'] != 'agreement'])
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'traces', 'operations', 'counts', 'operand_pairs_matched')}, indent=2))
    print(f'report: {out / "report.json"}', file=sys.stderr)
    return report['status']


if __name__ == '__main__':
    raise SystemExit(main())
