"""Seeded, bounded trace generation and dependency-preserving reduction."""
from copy import deepcopy
import hashlib
import json
import random

from harness import noise

U64 = 2**64 - 1
PRODUCERS = {'eventfd2', 'dup', 'dup3'}


def identity(trace):
    """Trace identity excludes its human-readable label."""
    return hashlib.sha256(json.dumps({'version': trace['version'], 'ops': trace['ops']},
                                   sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def generate(seed=20260920, count=1000, max_ops=64, profile='v2'):
    """Seeded traces. Profile `v1` reproduces the 2026-09-21 evidence; `v2`
    (Phase 4) widens the domain: blocking eventfds, arbitrary getter
    arguments, allocation bursts that reach EMFILE, and fewer invalid
    creations so fewer operations fall through to EBADF."""
    if profile == 'v2':
        return generate_v2(seed, count, max_ops)
    if profile == 'pipes':
        return generate_pipes(seed, count, min(max_ops, 48))
    if profile != 'v1':
        raise ValueError(f'unknown generator profile {profile}')
    if not 4 <= max_ops <= 64 or not 1 <= count <= 100000:
        raise ValueError('bounded generator parameters')
    rng = random.Random(seed)
    seen, result = set(), []
    while len(result) < count:
        operations = []
        producers = []

        def fd():
            if producers and rng.random() < .78:
                return {'ref': rng.choice(producers)}
            return {'literal': rng.choice([-2**31, -19, -1, 8, 9, 10, 15, 30, 31, 32, 2**31 - 1])}

        length = rng.randint(4, max_ops)
        for index in range(length):
            kind = 'eventfd2' if not index else rng.choices(
                ['eventfd2', 'dup', 'dup3', 'close', 'read', 'write', 'fcntl'], [3, 3, 2, 2, 5, 5, 2])[0]
            if kind == 'eventfd2':
                init = rng.choice([0, 1, 2, 7, 2**32 - 1, rng.randrange(2**32)])
                flags = 2048 | rng.choice([0, 1, 524288, 524289, 2, 2**31])
                operation = dict(op=kind, init=init, flags=flags)
            elif kind in ('dup', 'close'):
                operation = dict(op=kind, fd=fd())
            elif kind == 'dup3':
                operation = dict(op=kind, fd=fd(), newfd=fd(), flags=rng.choice([0, 524288, 1, 2**32 - 1]))
            elif kind in ('read', 'write'):
                operation = dict(op=kind, fd=fd(), count=rng.choices([0, 7, 8, 9, 16], [1, 1, 8, 1, 1])[0])
                if kind == 'write':
                    operation['value'] = str(rng.choice([0, 1, 2, 17, U64, U64 - 1, U64 - 2, rng.randrange(U64)]))
            else:
                command = rng.choice(['F_GETFD', 'F_SETFD', 'F_GETFL'])
                operation = dict(op=kind, fd=fd(), cmd=command,
                                 arg=rng.choice([0, 1, 2, 3, 2**32 - 1]) if command == 'F_SETFD' else 0)
            operations.append(operation)
            if kind in PRODUCERS:
                producers.append(index)
        trace = dict(version=1, id=f'generated-{seed}-{len(result):05}', ops=operations)
        digest = identity(trace)
        if digest not in seen:
            seen.add(digest)
            result.append(trace)
    return result


def remove_operations(trace, removed):
    """Remove transitive consumers of removed producer references and renumber.

    Numeric literals remain numeric, and surviving producer references continue
    to refer to their original producer. Replay decides whether descriptor reuse
    and the original semantic failure were preserved.
    """
    removed = set(removed)
    kept = []
    mapping = {}
    for index, op in enumerate(trace['ops']):
        references = [value['ref'] for value in (op.get('fd'), op.get('newfd'))
                      if type(value) is dict and 'ref' in value]
        if index in removed or any(ref in removed for ref in references):
            removed.add(index)
            continue
        mapping[index] = len(kept)
        converted = deepcopy(op)
        for key in ('fd', 'newfd'):
            if key in converted and 'ref' in converted[key]:
                converted[key]['ref'] = mapping[converted[key]['ref']]
        kept.append(converted)
    return dict(version=1, id=trace['id'], ops=kept)


def minimize(trace, retains_failure, budget=120):
    """Bounded ddmin plus scalar reduction. Predicate must independently replay.

    The caller compares a fixed failure signature; parser, process and coverage
    failures must return False. Every attempted reduction is retained in history.
    """
    current, history = deepcopy(trace), []

    def consider(candidate):
        nonlocal current
        if not candidate['ops'] or candidate == current or len(history) >= budget:
            return False
        accepted = bool(retains_failure(candidate))
        history.append(dict(trace=deepcopy(candidate), retained=accepted))
        if accepted:
            current = candidate
        return accepted

    width = max(1, len(current['ops']) // 2)
    while width and len(history) < budget:
        changed = False
        for start in range(0, len(current['ops']), width):
            if consider(remove_operations(current, range(start, min(start + width, len(current['ops']))))):
                changed = True
                break
        if not changed:
            width //= 2
    for index in range(len(current['ops'])):
        for key, values in [('init', [0, 1, 2]), ('value', ['0', '1', '2']), ('flags', [0, 2048, 2049])]:
            if key not in current['ops'][index]:
                continue
            original = current['ops'][index][key]
            for value in values:
                if int(value) >= int(original):
                    continue
                if key == 'flags' and current['ops'][index]['op'] == 'eventfd2' and not value & 2048:
                    continue
                candidate = deepcopy(current)
                candidate['ops'][index][key] = value
                if consider(candidate):
                    break
    return current, history


def failure_signature(result):
    if result.get('outcome') != 'semantic_mismatch':
        return None
    changed = tuple(key for key in ('ret', 'errno', 'bytes') if result['linux'][key] != result['model'][key])
    return result['outcome'], result['operation']['op'], changed


def generate_v2(seed, count, max_ops):
    if not 4 <= max_ops <= 64 or not 1 <= count <= 100000:
        raise ValueError('bounded generator parameters')
    rng = random.Random(seed)
    seen, result = set(), []
    while len(result) < count:
        operations, producers = [], []
        # A fifth of the traces raise RLIMIT_NOFILE so the table can grow past 64.
        rlimit = rng.choices([32, 64, 96, 128, 1024], [16, 1, 1, 1, 1])[0]
        literals = [-2**31, -1, 8, 9, 10, 15, 30, 31, 32, 63, 64, 2**31 - 1]
        if rlimit > 32:
            literals += [rlimit - 1, rlimit, 65, 100, 127, 700]

        def fd():
            if producers and rng.random() < .9:
                return {'ref': rng.choice(producers)}
            return {'literal': rng.choice(literals)}

        def append(operation):
            operations.append(operation)
            if operation['op'] in PRODUCERS:
                producers.append(len(operations) - 1)

        def creation():
            init = rng.choice([0, 0, 1, 2, 7, 2**32 - 1, rng.randrange(2**32)])
            mode = rng.choice([2048, 0])                    # nonblocking or blocking
            extra = rng.choices([0, 1, 524288, 524289, 2, 2**31], [6, 3, 2, 2, 1, 1])[0]
            return dict(op='eventfd2', init=init, flags=mode | extra)

        length = rng.randint(4, max_ops)
        append(creation())
        while len(operations) < length:
            if rng.random() < .04 and len(operations) + 26 <= max_ops:
                # Allocation burst: 24 slots are free (8..31), so this reaches EMFILE.
                for _ in range(rng.randint(20, 26)):
                    append(creation() if rng.random() < .5 or not producers else dict(op='dup', fd={'ref': rng.choice(producers)}))
                continue
            kind = rng.choices(['eventfd2', 'dup', 'dup3', 'close', 'read', 'write', 'fcntl'], [3, 3, 3, 3, 5, 5, 3])[0]
            if kind == 'eventfd2':
                append(creation())
            elif kind in ('dup', 'close'):
                append(dict(op=kind, fd=fd()))
            elif kind == 'dup3':
                newfd = fd() if rlimit == 32 or rng.random() < .5 else {'literal': rng.choice([64, 65, 100, rlimit - 1, rlimit])}
                append(dict(op=kind, fd=fd(), newfd=newfd, flags=rng.choices([0, 524288, 1, 2**32 - 1], [5, 4, 1, 1])[0]))
            elif kind in ('read', 'write'):
                operation = dict(op=kind, fd=fd(), count=rng.choices([0, 7, 8, 9, 16], [1, 1, 10, 1, 1])[0])
                if kind == 'write':
                    operation['value'] = str(rng.choice([0, 1, 2, 17, U64, U64 - 1, U64 - 2, rng.randrange(U64)]))
                append(operation)
            else:
                command = rng.choice(['F_GETFD', 'F_SETFD', 'F_GETFL', 'F_SETFL'])
                if command == 'F_SETFL':
                    arg = rng.choice([0, 2048, 1024, 16384, 262144, 8192, 2048 | 1024, 2**32 - 1])
                else:
                    arg = rng.choice([0, 1, 2, 3, 2**32 - 1])
                append(dict(op=kind, fd=fd(), cmd=command, arg=arg))
        trace = dict(version=1, id=f'generated-v2-{seed}-{len(result):05}', ops=operations[:max_ops])
        if rlimit != 32:
            trace['rlimit_nofile'] = rlimit
        digest = identity(trace)
        if digest not in seen:
            seen.add(digest)
            result.append(trace)
    return result


# Profile `pipes` (docs/2026-10-05-p-pipes.md section 7).
O_NONBLOCK, O_DIRECT, O_NOATIME, O_CLOEXEC, O_NOTIFICATION_PIPE = 0o4000, 0o40000, 0o1000000, 0o2000000, 0o200
PIPE_FLAGS = [O_NONBLOCK, O_NONBLOCK | O_CLOEXEC, O_NONBLOCK | O_DIRECT, O_DIRECT, 0, O_CLOEXEC,
              O_NOTIFICATION_PIPE, 1, 2**31]
# nonblocking 6 : 1, so most traces stay outside the blocking waits (the
# domain filter excludes those)
PIPE_FLAG_WEIGHTS = [12, 6, 6, 1, 1, 1, 1, 1, 1]
PIPE_COUNTS = [0, 1, 7, 8, 9, 16, 100, 4095, 4096, 4097, 8192, 16384, 65536, 65537, 69632]
# F_SETPIPE_SZ arguments: accepted sizes are capped at 4 MiB, and 2^31 (and
# 2^31 - 1, which rounds up to it) is excluded: round_pipe_size rejects only
# size > 1U << 31 (fs/pipe.c:1249), so 2^31 would kcalloc 2^19 buffers in
# pipe_resize_ring (:1271) and fail with -ENOMEM on the guest, an allocation
# outcome that fails the chunk (audit M1). 2^31 + 1 and 2^32 - 1 give -EINVAL
# without allocating.
PIPE_SIZES = [0, 1, 4095, 4096, 4097, 8192, 65536, 65537, 1048576, 1048577, 4194304, 2**31 + 1, 2**32 - 1]
PIPE_SETFL = [O_NONBLOCK, O_NONBLOCK | O_DIRECT, O_NONBLOCK | O_NOATIME, O_DIRECT, 0,
              O_NONBLOCK | O_DIRECT | O_NOATIME, 2**32 - 1]
PAUSE_SHARE = .1


def generate_pipes(seed, count, max_ops=48):
    """Seeded pipe traces: producers `eventfd2` and `pipe2`, descriptors drawn
    over pipe ends, eventfds and literals; reads and writes near the page and
    ring boundaries; fcntl including F_SETPIPE_SZ/F_GETPIPE_SZ. Bursts: 17
    page writes (fill to -EAGAIN), 16 one-byte packet writes, and write/read
    pairs on a one-slot ring (index wrap). A tenth of the reads and writes
    pause 5 ms first (the stamps' "differs" outcome). Blocking pipes are
    rare; the domain filter drops the traces that would wait."""
    if not 4 <= max_ops <= 64 or not 1 <= count <= 100000:
        raise ValueError('bounded generator parameters')
    rng = random.Random(f'pipes-{seed}')
    seen, result = set(), []
    while len(result) < count:
        operations, events, pipes = [], [], []
        rlimit = rng.choices([32, 9, 10, 64], [20, 1, 1, 2])[0]
        literals = [-1, 8, 9, 10, 11, 15, 31, 2**31 - 1]

        def end(index=None, which=None):
            index = rng.choice(pipes) if index is None else index
            return {'pipe': index, 'end': rng.choice([0, 1]) if which is None else which}

        def fd():
            draw = rng.random()
            if pipes and draw < .75:
                return end()
            if events and draw < .9:
                return {'ref': rng.choice(events)}
            return {'literal': rng.choice(literals)}

        def append(operation):
            if len(operations) < max_ops:
                operations.append(operation)
                if operation['op'] == 'pipe2':
                    pipes.append(len(operations) - 1)
                elif operation['op'] in PRODUCERS:
                    events.append(len(operations) - 1)

        def paused(operation):
            if rng.random() < PAUSE_SHARE:
                operation['pause_ms'] = 5
            return operation

        def write(target, count):
            return paused(dict(op='write', fd=target, count=count,
                               value=str(rng.choice([0, 1, 17, U64, rng.randrange(U64)]))))

        def creation():
            return dict(op='pipe2', flags=rng.choices(PIPE_FLAGS, PIPE_FLAG_WEIGHTS)[0])

        length = rng.randint(4, max_ops)
        append(creation())
        while len(operations) < length:
            burst = rng.random()
            if pipes and burst < .012:
                # fill the default ring: 17 page writes, the last one -EAGAIN
                target = end(which=1)
                for _ in range(17):
                    append(write(target, 4096))
                continue
            if pipes and burst < .02:
                # sixteen one-byte packets (on an O_DIRECT write end they fill the ring)
                target = end(which=1)
                if rng.random() < .5:
                    append(dict(op='fcntl', fd=target, cmd='F_SETFL', arg=O_NONBLOCK | O_DIRECT))
                for _ in range(16):
                    append(write(target, 1))
                continue
            if pipes and burst < .03:
                # a one-slot ring and write/read pairs: head and tail pass ring_size
                index = rng.choice(pipes)
                append(dict(op='fcntl', fd=end(index, 1), cmd='F_SETPIPE_SZ', arg=4096))
                for _ in range(rng.randint(2, 6)):
                    append(write(end(index, 1), rng.choice([1, 7, 100])))
                    append(paused(dict(op='read', fd=end(index, 0), count=rng.choice([1, 100, 4096]))))
                continue
            kind = rng.choices(['pipe2', 'eventfd2', 'dup', 'dup3', 'close', 'read', 'write', 'fcntl'],
                               [3, 1, 2, 2, 3, 8, 8, 5])[0]
            if kind == 'pipe2':
                append(creation())
            elif kind == 'eventfd2':
                append(dict(op='eventfd2', init=rng.choice([0, 1, 7]), flags=O_NONBLOCK))
            elif kind in ('dup', 'close'):
                append(dict(op=kind, fd=fd()))
            elif kind == 'dup3':
                newfd = fd() if rng.random() < .6 else {'literal': rng.choice([20, 30, rlimit - 1])}
                append(dict(op=kind, fd=fd(), newfd=newfd, flags=rng.choices([0, O_CLOEXEC, 1], [6, 3, 1])[0]))
            elif kind == 'read':
                append(paused(dict(op='read', fd=fd(), count=rng.choice(PIPE_COUNTS))))
            elif kind == 'write':
                append(write(fd(), rng.choice(PIPE_COUNTS)))
            else:
                command = rng.choices(['F_GETFD', 'F_SETFD', 'F_GETFL', 'F_SETFL', 'F_SETPIPE_SZ', 'F_GETPIPE_SZ'],
                                      [1, 1, 2, 3, 5, 3])[0]
                arg = {'F_SETFD': lambda: rng.choice([0, 1]), 'F_SETFL': lambda: rng.choice(PIPE_SETFL),
                       'F_SETPIPE_SZ': lambda: rng.choice(PIPE_SIZES)}.get(command, lambda: 0)()
                append(dict(op='fcntl', fd=fd(), cmd=command, arg=arg))
        trace = dict(version=1, id=f'pipes-{seed}-{len(result):05}', ops=operations)
        if rlimit != 32:
            trace['rlimit_nofile'] = rlimit
        digest = identity(trace)
        if digest not in seen:
            seen.add(digest)
            result.append(trace)
    return result


# The guest's waits (harness/guest.c): 0.4 s in wg_inject and wg_observe,
# 0.1 s in the operations that can queue the handshake send worker, and 0.1 s
# after the tick that absorbs a wg_advance (D3). It fails a trace that runs
# longer than 4.5 s after wg_up, net of its advances (REKEY_BOUND_NS), so the
# generator keeps the planned waits well inside it (computation took up to
# 0.5 s per trace on a contended host, 2026-10-06).
WAIT_BUDGET_SECONDS = 2.8
# A wg_advance costs more real time than its 0.1 s wait: the fresh-tick start
# and the absorbing tick (up to 4 ms each, polled at 1 ms), and the work its
# callbacks queue (a retransmit's initiation is a Curve25519 computation under
# TCG). Measured on the contended host (int-dl full check, 2026-10-07): the 20
# advances of a give-up chain ran 1.4-1.6 s beyond their modeled waits, about
# 0.17 s per advance in all; counted at 0.2 s [AGENT, int-dl follow-up 1].
ADVANCE_COST_SECONDS = 0.2


def wait_after_up(operations):
    waits, up = 0.0, False
    for op in operations:
        up = up or op['op'] == 'wg_up'
        if up:
            waits += {'wg_inject': 0.4, 'wg_observe': 0.4, 'wg_set': 0.1, 'wg_up': 0.1, 'wg_xmit': 0.1,
                      'wg_advance': ADVANCE_COST_SECONDS}.get(op['op'], 0)
    return waits


def generate_wireguard(seed, count, max_ops=12, steered=0.0, data=0.0, timers=0.0):
    """Seeded WireGuard traces over small pools of keys and prefixes, so that
    peers, trie nodes and identities collide often. A third are configuration
    traces (stage A), and the rest bring wg0 up and transmit (stage B1), inject
    messages (stage B2), or inject handshake initiations (stage C), a sixth
    each. Every trace ends with a dump.

    `steered` is the share of steered handshakes (stage D1, steered_handshake),
    drawn from a separate generator: with the default 0 the other classes'
    streams are exactly as before. `data` is the share of steered data-plane
    traces (stage D2, steered_data), drawn first and from a third generator:
    the other traces keep their content and order (only their identifiers
    shift), and with the default 0 the output is exactly as before.
    `timers` is the share of steered timer traces (stage D3, steered_timers),
    drawn before the data-plane share from a fourth generator, with the same
    property."""
    if not 2 <= max_ops <= 64 or not 1 <= count <= 100000 or not 0 <= steered <= 1 or not 0 <= data <= 1 \
            or not 0 <= timers <= 1:
        raise ValueError('bounded generator parameters')
    rng = random.Random(seed)
    steered_rng = random.Random(f'steered-{seed}')
    data_rng = random.Random(f'data-{seed}')
    timers_rng = random.Random(f'timers-{seed}')
    keys = ['11' * 32, '22' * 32, '33' * 32, '00' * 32,
            '7b4e909bbe7ffe44c465a220037d608ee35897d31ef972f07f74892cb0f73f13']   # public key of 11..11
    private = ['11' * 32, '10' + '11' * 30 + '51', '22' * 32, '00' * 32]
    v4 = ['0a000000', '0a010000', '0a010203', '0a800000', 'c0a80001', '00000000', 'ffffffff']
    v6 = ['20010db8000000000000000000000000', '20010db8000000008000000000000001', '20010db9000000000000000000000000',
          'fe800000000000000000000000000000', '00000000000000000000000000000000']
    seen, result = set(), []

    def allowed_ip():
        if rng.random() < .6:
            return dict(family=4, addr=rng.choice(v4), cidr=rng.choices([0, 8, 15, 16, 24, 32, 33], [1, 3, 2, 3, 2, 2, 1])[0])
        return dict(family=6, addr=rng.choice(v6), cidr=rng.choices([0, 10, 32, 48, 64, 65, 128, 129], [1, 1, 3, 2, 2, 1, 2, 1])[0])

    def peer():
        entry = dict(public_key=rng.choice(keys))
        for flag, p in (('remove', .1), ('update_only', .1), ('replace_allowed_ips', .15)):
            if rng.random() < p:
                entry[flag] = True
        if rng.random() < .2:
            entry['preshared_key'] = rng.choice(['aa' * 32, 'bb' * 32])
        if rng.random() < .3:
            entry['endpoint'] = rng.choice([dict(family=4, addr='0a000001', port=rng.choice([1, 51820])),
                                            dict(family=6, addr=v6[1], port=rng.choice([1, 51820]))])
        if rng.random() < .3:
            entry['keepalive'] = rng.choice([0, 25])
        if rng.random() < .8:
            entry['allowed_ips'] = [allowed_ip() for _ in range(rng.choices([0, 1, 2, 3, 5], [1, 3, 3, 2, 1])[0])]
        return entry

    def config():
        result = {}
        if rng.random() < .3:
            result['private_key'] = rng.choice(private)
        if rng.random() < .15:
            result['listen_port'] = rng.choice([0, 51820])
        if rng.random() < .1:
            result['fwmark'] = rng.choice([0, 1, 2**32 - 1])
        if rng.random() < .1:
            result['replace_peers'] = True
        if rng.random() < .85:
            result['peers'] = [peer() for _ in range(rng.choices([0, 1, 2, 3], [1, 4, 3, 2])[0])]
        return result

    endpoints = [dict(family=4, addr='7f000001', port=51999), dict(family=6, addr='0' * 31 + '1', port=51999),
                 dict(family=4, addr='7f000001', port=1234)]
    destinations = [(4, a) for a in ('0a000001', '0a010201', '0a0102ff', '0a800001', 'c0a80001', '0b000001', 'e0000001')] + \
                   [(6, a) for a in ('20010db8000000000000000000000001', '20010db8000000008000000000000002',
                                     'fe800000000000000000000000000001', 'fd000000000000000000000000000001')]

    def transmit_trace():
        """Stage B1: configure, bring wg0 up, then transmit and observe."""
        first = config()
        first['listen_port'] = 51820
        for peer in first.get('peers', []):
            peer.pop('remove', None)
            if rng.random() < .8:
                peer['endpoint'] = rng.choice(endpoints)
        ops = [{'op': 'wg_set', 'config': first}, {'op': 'wg_up'}]
        for _ in range(rng.randint(1, max_ops - 4)):
            kind = rng.choices(['xmit', 'observe', 'set', 'get'], [5, 3, 1, 1])[0]
            if kind == 'xmit':
                family, dst = rng.choice(destinations)
                ops.append({'op': 'wg_xmit', 'packet': {'family': family, 'dst': dst}})
            elif kind == 'observe':
                ops.append({'op': 'wg_observe'})
            elif kind == 'set':
                change = config()
                change.pop('listen_port', None)
                ops.append({'op': 'wg_set', 'config': change})
            else:
                ops.append({'op': 'wg_get'})
        return ops + [{'op': 'wg_observe'}]

    def message():
        """A WireGuard message near the parser's boundaries: type, reserved
        bytes and length vary; the body is one repeated byte."""
        kind = rng.choices([0, 1, 2, 3, 4, 5, 255], [1, 4, 3, 3, 4, 1, 1])[0]
        exact = {1: 148, 2: 92, 3: 64, 4: rng.choice([32, 33, 48, 1400])}.get(kind, 148)
        length = min(1400, rng.choices([exact, exact - 1, exact + 1, rng.randint(0, 40)], [6, 1, 1, 1])[0])
        reserved = bytes(3) if rng.random() < .9 else bytes([0, 0, 1])
        body = bytes([kind]) + reserved + bytes([rng.randrange(256)]) * max(0, length - 4)
        return body[:length] if length else bytes([kind])

    def receive_trace():
        """Stage B2: configure, bring wg0 up, then inject messages."""
        first = config()
        first['listen_port'] = 51820
        for peer in first.get('peers', []):
            for field in ('remove', 'keepalive'):   # no handshake work: index lookups stay determined
                peer.pop(field, None)
        ops = [{'op': 'wg_set', 'config': first}, {'op': 'wg_up'}]
        for _ in range(rng.randint(1, max_ops - 4)):
            kind = rng.choices(['inject', 'set', 'get'], [8, 1, 1])[0]
            if kind == 'inject':
                ops.append({'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': message().hex()})
            elif kind == 'set':
                change = config()
                change.pop('listen_port', None)
                for peer in change.get('peers', []):
                    peer.pop('keepalive', None)
                ops.append({'op': 'wg_set', 'config': change})
            else:
                ops.append({'op': 'wg_get'})
        return ops

    initiators = [b'\x22' * 32, b'\x44' * 32]
    handshake_privates = [b'\x11' * 32, b'\x55' * 32, b'\x22' * 32, None]

    def handshake_trace():
        """Stage C: configure, bring wg0 up, then inject Noise initiations from
        two initiators (and a low-order static key) whose keys, timestamps and
        targets collide with the configuration."""
        device = rng.choices(handshake_privates, [6, 2, 1, 1])[0]
        stamp = 1

        def hs_peer():
            public = rng.choices([noise.public_key(k) for k in initiators] + [bytes(32)], [6, 2, 1])[0]
            entry = dict(public_key=public.hex(), allowed_ips=[allowed_ip() for _ in range(rng.randint(0, 2))])
            if rng.random() < .2:
                entry['preshared_key'] = rng.choice(['aa' * 32, 'bb' * 32])
            if rng.random() < .3:
                entry['endpoint'] = rng.choice(endpoints[:2])
            if rng.random() < .2:
                entry['keepalive'] = 25
            if rng.random() < .1:
                entry['remove'] = True
            return entry

        def initiation():
            nonlocal stamp
            stamp = max(1, stamp + rng.choices([1, 0, -1], [8, 1, 1])[0])
            target = device if rng.random() < .9 else rng.choice([k for k in handshake_privates if k])
            responder = noise.public_key(target) if target else bytes(32)
            initiator = rng.choices(initiators, [7, 2])[0]
            extra = {}
            if rng.random() < .08:
                extra['static_public'] = bytes(32)
            if rng.random() < .05:
                extra['ephemeral_public'] = bytes(32)
            if rng.random() < .1:
                extra['tamper'] = rng.choice(['static', 'timestamp'])
            if target is None:
                extra['mac1_key'] = bytes(32)
            return noise.initiation(responder, initiator, bytes([rng.randrange(1, 256)]) * 32,
                                    bytes(11) + bytes([stamp]), rng.randrange(2 ** 32), **extra)

        first = dict(listen_port=51820, peers=[hs_peer() for _ in range(rng.randint(1, 3))])
        for peer in first['peers']:
            peer.pop('remove', None)
        if device is not None:
            first['private_key'] = device.hex()
        ops = [{'op': 'wg_set', 'config': first}, {'op': 'wg_up'}]
        if any('keepalive' in p for p in first['peers']):
            ops.append({'op': 'wg_observe'})   # the keepalive's handshake work runs first
        for _ in range(rng.randint(1, max_ops - 4)):
            kind = rng.choices(['inject', 'observe', 'set', 'get'], [8, 3, 1, 1])[0]
            if kind == 'inject':
                ops.append({'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820,
                            'message': initiation().hex()})
            elif kind == 'observe':
                ops.append({'op': 'wg_observe'})
            elif kind == 'set':
                change = dict(peers=[hs_peer() for _ in range(rng.randint(0, 2))])
                for peer in change['peers']:
                    peer.pop('keepalive', None)
                if rng.random() < .3:
                    device = rng.choice(handshake_privates[:3])
                    change['private_key'] = device.hex()
                ops.append({'op': 'wg_set', 'config': change})
            else:
                ops.append({'op': 'wg_get'})
        return ops + [{'op': 'wg_observe'}]

    while len(result) < count:
        if timers and timers_rng.random() < timers:
            trace = steered_timers(timers_rng, f'generated-wg-{seed}-{len(result):05}')
            if wait_after_up(trace['ops']) > WAIT_BUDGET_SECONDS:
                raise AssertionError('a steered timer trace exceeds the wait budget')
            digest = identity(trace)
            if digest not in seen:
                seen.add(digest)
                result.append(trace)
            continue
        if data and data_rng.random() < data:
            trace = steered_data(data_rng, f'generated-wg-{seed}-{len(result):05}')
            if wait_after_up(trace['ops']) > WAIT_BUDGET_SECONDS:
                raise AssertionError('a steered data trace exceeds the wait budget')
            digest = identity(trace)
            if digest not in seen:
                seen.add(digest)
                result.append(trace)
            continue
        if steered and steered_rng.random() < steered:
            trace = steered_handshake(steered_rng, f'generated-wg-{seed}-{len(result):05}')
            if wait_after_up(trace['ops']) > WAIT_BUDGET_SECONDS:
                raise AssertionError('a steered handshake exceeds the wait budget')
            digest = identity(trace)
            if digest not in seen:
                seen.add(digest)
                result.append(trace)
            continue
        draw = rng.random()
        if draw < 1 / 6:
            operations = receive_trace()
        elif draw < 1 / 3:
            operations = handshake_trace()
        elif draw < 2 / 3:
            operations = transmit_trace()
        else:
            operations = []
            for _ in range(rng.randint(1, max_ops - 1)):
                operations.append({'op': 'wg_get'} if rng.random() < .2 else {'op': 'wg_set', 'config': config()})
        operations.append({'op': 'wg_get'})
        if wait_after_up(operations) > WAIT_BUDGET_SECONDS:
            continue   # the guest fails a trace longer than 4.5 s after wg_up
        trace = dict(version=1, id=f'generated-wg-{seed}-{len(result):05}', ops=operations)
        digest = identity(trace)
        if digest not in seen:
            seen.add(digest)
            result.append(trace)
    return result


# Stage D1: wg0 initiates with steered hidden inputs, and a response computed
# offline completes (or, tampered, fails) the handshake
# (docs/2026-10-03-steering-design.md, sections 6.1-6.3).
D1_DEVICES = [b'\x11' * 32, bytes.fromhex('10' + '11' * 30 + '51'), b'\x55' * 32]
D1_PEERS = [b'\x22' * 32, b'\x44' * 32, b'\x66' * 32]
D1_LISTENERS = [dict(family=4, addr='7f000001', port=51999), dict(family=6, addr='0' * 31 + '1', port=51999)]
D1_SESSION = ['wg_receive_handshake_packet.response=1', 'wg_noise_handshake_begin_session.initiator=1',
              'add_new_keypair.initiator=1', 'wg_packet_send_staged_packets.no_keypair=0']
TAI64N_SEC_MAX = 2**63 // 1_000_000_000 - 30 * 365 * 24 * 3600 - 1   # harness/steer.py's bound, inclusive


def steered_handshake(rng, trace_id):
    """One steered D1 trace. The schedule is predicted from the trace's shape
    rather than by running the mirror (design 6.3 step 2): each shape has a
    fixed encounter order. create_initiation draws the ephemeral (before the
    clamp), reads the clock, then draws the index; create_response draws its
    ephemeral, then the index. The variants: a completed handshake (half),
    a tampered encrypted_nothing, a bad MAC1, a receiver index naming nothing
    (another bucket or the same one), a second response after the session,
    and respond-then-initiate (a pending next keypair, then wg0 initiates
    after a key change resets the rate limit)."""
    device = rng.choice(D1_DEVICES)
    peer_private = rng.choice(D1_PEERS)
    peer_public = noise.public_key(peer_private)
    psk = rng.choice([b'\xaa' * 32, b'\xbb' * 32, rng.randbytes(32)]) if rng.random() < .25 else None
    variant = rng.choices(['session', 'nothing', 'mac1', 'other_bucket', 'same_bucket', 'second', 'respond_first'],
                          [6, 1, 1, 1, 1, 1, 2])[0]

    def clock():
        sec = rng.choice([0, 1, rng.randrange(2**31), rng.randrange(2**31, TAI64N_SEC_MAX), TAI64N_SEC_MAX])
        return sec, rng.choice([0, (1 << 24) - 1, 999_999_999, rng.randrange(1_000_000_000)])

    def initiation(device):
        ephemeral, (sec, nsec), index = rng.randbytes(32), clock(), rng.randrange(2**32)
        steer = [['init_ephemeral', ephemeral.hex()], ['tai64n_now', noise.timespec64(sec, nsec).hex()],
                 ['index_draw', index.to_bytes(4, 'little').hex()]]
        return noise.steered_initiation(peer_public, device, ephemeral, sec, nsec, index), index, steer

    def respond(message, device, **kw):
        return noise.response(message, peer_private, rng.randbytes(32), psk, rng.randrange(2**32),
                              initiator_public=noise.public_key(device), **kw).message

    def inject(message):
        return {'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': message.hex()}

    peer = dict(public_key=peer_public.hex(), allowed_ips=[dict(family=4, addr='0a000000', cidr=8)],
                endpoint=rng.choice(D1_LISTENERS))
    if psk is not None:
        peer['preshared_key'] = psk.hex()
    peers = [peer]
    if rng.random() < .3:   # a bystander: no endpoint and no keepalive, so no handshake work
        bystander = rng.choice([k for k in D1_PEERS if k != peer_private])
        peers.append(dict(public_key=noise.public_key(bystander).hex(),
                          allowed_ips=[dict(family=4, addr='0a010000', cidr=16)]))
    observe, get = {'op': 'wg_observe'}, {'op': 'wg_get'}
    if variant == 'respond_first':
        theirs = noise.initiation(noise.public_key(device), peer_private, rng.randbytes(32),
                                  noise.tai64n(*clock()), rng.randrange(2**32))
        # a key change: D1_DEVICES[1] is D1_DEVICES[0] clamped, the same key to wg_set_device
        second = rng.choice([k for k in D1_DEVICES if noise.clamp(k) != noise.clamp(device)])
        ours, _, steer = initiation(second)
        draws = [['resp_ephemeral', rng.randbytes(32).hex() if rng.random() < .5 else 'draw'],
                 ['index_draw', rng.randbytes(4).hex() if rng.random() < .5 else 'draw']]
        ops = [{'op': 'wg_set', 'config': dict(private_key=device.hex(), listen_port=51820, peers=peers)},
               {'op': 'wg_up'}, inject(theirs), observe,
               {'op': 'wg_set', 'config': dict(private_key=second.hex(),
                                               peers=[dict(public_key=peer_public.hex(), keepalive=25)])},
               observe, inject(respond(ours, second)), observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=draws + steer,
                    expect=['wg_receive_handshake_packet.initiation=1'] + D1_SESSION)
    peer['keepalive'] = 25
    ours, index, steer = initiation(device)
    after, expect = [], D1_SESSION
    if variant == 'nothing':
        response, expect = respond(ours, device, tamper='nothing'), ['wg_receive_handshake_packet.response=1']
    elif variant == 'mac1':
        response, expect = respond(ours, device, tamper='mac1'), None
    elif variant == 'other_bucket':
        response = respond(ours, device, receiver_index=index ^ rng.randrange(1, 1 << 13))
        expect = ['wg_receive_handshake_packet.response=1', 'wg_index_hashtable_lookup.entry=0']
    elif variant == 'same_bucket':
        response = respond(ours, device, receiver_index=index ^ (rng.randrange(1, 1 << 19) << 13))
        expect = ['wg_receive_handshake_packet.response=1', 'wg_index_hashtable_lookup.index_matches=0']
    else:
        response = respond(ours, device)
        if variant == 'second':
            after = [inject(respond(ours, device)), observe]
            expect = D1_SESSION + ['wg_index_hashtable_lookup.type_matches=0']
    ops = [{'op': 'wg_set', 'config': dict(private_key=device.hex(), listen_port=51820, peers=peers)},
           {'op': 'wg_up'}, observe, inject(response), observe, *after, get]
    trace = dict(version=1, id=trace_id, ops=ops, steer=steer)
    if expect:
        trace['expect'] = expect
    return trace


# Stage D2: the data plane (docs/2026-10-04-d2-data-plane.md, section 6).
# After a steered session (wg0 initiates, or responds), payload packets in
# both directions: wg_xmit with payloads, and message_data built offline
# under the session's keys carrying inner IPv4/IPv6 UDP packets.
D2_ALLOWED4 = [('0a000000', 8), ('0a010000', 16)]
D2_ALLOWED6 = [('20010db8000000000000000000000000', 32), ('20010db8000000000000000000000000', 48)]
D2_OUTSIDE4 = ['c0a80002', '0b000001', 'ac100001']                 # in no allowed range
D2_OUTSIDE6 = ['20010db9000000000000000000000002', '20020000000000000000000000000001']
D2_SIZES4 = [1, 15, 16, 17, 20, 1376, 1377, 1391, 1392]            # inner lengths 1404, 1405, 1419, 1420
D2_SIZES6 = [1, 15, 16, 17, 20, 1356, 1357, 1371, 1372]
D2_INJECT_MAX = 1400 - 32                                           # wg_inject's message bound, less header and tag
D2_WINDOW = noise.COUNTER_WINDOW_SIZE
D2_REJECT = noise.REJECT_AFTER_MESSAGES


def _in_prefix(rng, addr, cidr, length):
    """A random address inside addr/cidr (`length` bytes)."""
    base = int(addr, 16)
    host_bits = 8 * length - cidr
    return (base | rng.randrange(2 ** host_bits)).to_bytes(length, 'big')


def steered_data(rng, trace_id):
    """One steered D2 trace. The session comes first, as in
    steered_handshake: wg0 initiates (steered ephemeral, clock and index),
    or the peer initiates and wg0 responds (steered resp_ephemeral and
    index_draw: the keys the peer sends with depend on both). Then one of:
    - `xmit`: 1-4 payload transmissions after the session (sizes at the
      padding and MTU-clamp boundaries, or random);
    - `staged`: 1-4 transmissions before the session, flushed by it;
    - `receive`: up to three injected data messages under a counter pattern
      (in order, duplicate, reordered within the window, older than the
      window, a jump over COUNTER_BITS_TOTAL, the window boundary pair, the
      REJECT_AFTER_MESSAGES pair), each carrying a delivered inner packet, a
      keepalive or a dishonest inner packet, sometimes with a tampered tag
      or a wrong key index;
    - `mixed`: data messages and transmissions interleaved (the timer state);
    - `respond`: respond-then-data, optionally with a packet staged before
      the confirmation.
    Inner sources are drawn from the peer's allowed ranges minus wg0's local
    addresses; transmit destinations are non-local addresses in them, so no
    fe80::/10 destination occurs."""
    device = rng.choice(D1_DEVICES)
    peer_private = rng.choice(D1_PEERS)
    peer_public = noise.public_key(peer_private)
    psk = rng.choice([b'\xaa' * 32, rng.randbytes(32)]) if rng.random() < .2 else None
    variant = rng.choices(['xmit', 'staged', 'receive', 'mixed', 'respond'], [3, 2, 5, 2, 3])[0]
    allowed4, allowed6 = rng.choice(D2_ALLOWED4), rng.choice(D2_ALLOWED6)

    def source(family):
        if family == 4:
            while True:
                src = _in_prefix(rng, *allowed4, 4)
                if src != noise.WG0_ADDR4:
                    return src
        return _in_prefix(rng, *allowed6, 16)

    def destination(family):
        if family == 4:
            while True:
                dst = _in_prefix(rng, *allowed4, 4)
                if dst != noise.WG0_ADDR4:
                    return dst
        while True:
            dst = _in_prefix(rng, *allowed6, 16)
            if dst != noise.WG0_ADDR6:
                return dst

    def xmit():
        family = rng.choice([4, 6])
        sizes = D2_SIZES4 if family == 4 else D2_SIZES6
        size = rng.choice(sizes) if rng.random() < .6 else rng.randint(1, sizes[-1])
        dst = destination(family)
        if rng.random() < .05:   # no peer for the destination: wg_xmit's error path, with a payload
            dst = bytes.fromhex(rng.choice(D2_OUTSIDE4)) if family == 4 else bytes.fromhex(rng.choice(D2_OUTSIDE6))
        return {'op': 'wg_xmit', 'packet': dict(family=family, dst=dst.hex(), payload=rng.randbytes(size).hex())}

    def inner():
        """A plaintext: a delivered inner packet, a keepalive, or a dishonest one."""
        kind = rng.choices(['deliver4', 'deliver6', 'keepalive', 'type', 'size', 'source'], [5, 3, 1, 1, 1, 1])[0]
        text = rng.randbytes(rng.choice([0, 1, 7, 16, rng.randint(0, 200)]))
        sport = rng.choice([12345, 1, 65535, rng.randrange(1, 65536)])
        if kind == 'keepalive':
            return b''
        if kind == 'deliver4':
            return noise.to_wg0(4, source(4), text, sport=sport, checksum=rng.choice(['correct', 'wrong', 'zero']))
        if kind == 'deliver6':   # a zero UDP checksum is dropped on IPv6: outside the delivery predicate
            return noise.to_wg0(6, source(6), text, sport=sport, checksum=rng.choice(['correct', 'wrong']))
        if kind == 'source':
            family = rng.choice([4, 6])
            src = bytes.fromhex(rng.choice(D2_OUTSIDE4 if family == 4 else D2_OUTSIDE6))
            return noise.to_wg0(family, src, text, sport=sport)
        if kind == 'type':
            choice = rng.randrange(3)
            if choice == 0:   # another version in a full header
                return noise.to_wg0(4, source(4), text, sport=sport, version=rng.choice([0, 5, 7, 15]))
            if choice == 1:   # shorter than an IPv4 header, even padded
                return bytes([0x45]) + rng.randbytes(rng.randint(0, 14))
            return bytes([0x60]) + rng.randbytes(rng.randint(19, 30))   # version 6, padded below 40
        family = rng.choice([4, 6])
        packet = noise.to_wg0(family, source(family), text, sport=sport)
        padded = len(packet) + noise.padding(len(packet))
        if family == 4:
            return noise.to_wg0(4, source(4), text, sport=sport,
                                tot_len=rng.choice([0, 19, padded + 1, rng.randint(padded + 1, 65535)]))
        return noise.to_wg0(6, source(6), text, sport=sport, payload_len=rng.randint(padded - 39, 65535))

    def counters(n):
        pattern = rng.choice(['in_order', 'duplicate', 'reorder', 'old', 'jump', 'boundary', 'reject'])
        top = rng.choice([D2_WINDOW + 1, 10000, rng.randrange(D2_WINDOW + 1, 2**48), rng.randrange(2**63, D2_REJECT)])
        first = rng.choice([0, 0, 1, rng.randrange(1000)])
        values = {'in_order': [first, first + 1, first + 2],
                  'duplicate': [first, first, first + 1],
                  'reorder': [first + 2, first, first + 1],
                  'old': [top, top - D2_WINDOW - 1 - rng.randrange(min(100, top - D2_WINDOW)), top + 1],
                  'jump': [first, first + noise.COUNTER_BITS_TOTAL + rng.randrange(1, 100), first + 1],
                  'boundary': [top, top - D2_WINDOW, top - D2_WINDOW - 1],
                  'reject': [D2_REJECT, D2_REJECT - 1, first]}[pattern]
        return values[:n]

    def data_ops(session, n):
        ops = []
        for counter in counters(n):
            plaintext = inner()
            index = session.local_index
            if rng.random() < .05:
                index ^= rng.randrange(1, 2**32)
            message = noise.data_message(session.receiving, index, counter, plaintext, tamper=rng.random() < .1)
            ops.append({'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': message.hex()})
        return ops

    peer = dict(public_key=peer_public.hex(),
                allowed_ips=[dict(family=4, addr=allowed4[0], cidr=allowed4[1]),
                             dict(family=6, addr=allowed6[0], cidr=allowed6[1])],
                endpoint=rng.choice(D1_LISTENERS))
    if psk is not None:
        peer['preshared_key'] = psk.hex()
    observe, get = {'op': 'wg_observe'}, {'op': 'wg_get'}

    def setup():
        return [{'op': 'wg_set', 'config': dict(private_key=device.hex(), listen_port=51820, peers=[peer])},
                {'op': 'wg_up'}]

    if variant == 'respond':
        raw, index = rng.randbytes(32), rng.randrange(2**32)
        theirs = noise.initiation(noise.public_key(device), peer_private, rng.randbytes(32),
                                  noise.tai64n(rng.randrange(2**31), rng.randrange(10**9)), rng.randrange(2**32))
        session = noise.responder_session(noise.wg0_response(theirs, device, raw, psk, index))
        inject = {'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': theirs.hex()}
        staged = [xmit() for _ in range(rng.choice([0, 0, 1, 2]))]
        ops = setup() + [inject] + staged + data_ops(session, rng.randint(1, 3)) + [observe, get]
        steer = [['resp_ephemeral', raw.hex()], ['index_draw', index.to_bytes(4, 'little').hex()]]
        return dict(version=1, id=trace_id, ops=ops, steer=steer,
                    expect=['wg_receive_handshake_packet.initiation=1', 'add_new_keypair.initiator=0'])

    ephemeral, index = rng.randbytes(32), rng.randrange(2**32)
    sec = rng.choice([1, rng.randrange(2**31), TAI64N_SEC_MAX])
    nsec = rng.randrange(10**9)
    steer = [['init_ephemeral', ephemeral.hex()], ['tai64n_now', noise.timespec64(sec, nsec).hex()],
             ['index_draw', index.to_bytes(4, 'little').hex()]]
    ours = noise.steered_initiation(peer_public, device, ephemeral, sec, nsec, index)
    response = noise.response(ours, peer_private, rng.randbytes(32), psk, rng.randrange(2**32),
                              initiator_public=noise.public_key(device))
    session = noise.initiator_session(response)
    respond = {'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': response.message.hex()}
    if variant == 'staged':
        # no persistent keepalive: the first transmission stages and initiates
        first = xmit()
        first['packet']['dst'] = destination(first['packet']['family']).hex()   # routed to the peer
        ops = setup() + [first] + [xmit() for _ in range(rng.randint(0, 3))] + [observe, respond, observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=steer,
                    expect=D1_SESSION + ['wg_packet_send_staged_packets.no_keypair=1'])
    peer['keepalive'] = 25
    if variant == 'xmit':
        after = [xmit() for _ in range(rng.randint(1, 4))]
    elif variant == 'receive':
        after = data_ops(session, rng.randint(1, 3))
    else:
        after = data_ops(session, 2) + [xmit(), xmit()]
        rng.shuffle(after)
    ops = setup() + [observe, respond] + after + [observe, get]
    return dict(version=1, id=trace_id, ops=ops, steer=steer, expect=D1_SESSION)


# Stage D3: WireGuard's timers under the virtual time advance
# (docs/2026-10-05-d3-timers.md, sections 2.2, 6 and 7). In ticks (HZ 250).
HZ = 250
ADVANCE_WAIT_TICKS = 25            # ADVANCE_WAIT_US (0.1 s) after the absorbing tick
TRACE_BOUND_TICKS = 1125           # the guest's real-time bound, REKEY_BOUND_NS (4.5 s)
REKEY_TIMEOUT_TICKS = 5 * HZ
JITTER_MAX_TICKS = HZ // 3         # get_random_u32_below(REKEY_TIMEOUT_JITTER_MAX_JIFFIES): [0, 83)
KEEPALIVE_TIMEOUT_TICKS = 10 * HZ
NEW_HANDSHAKE_TICKS = KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS
ZERO_KEY_TICKS = 180 * 3 * HZ      # REJECT_AFTER_TIME * 3
# LVL_START(n + 1) (kernel/time/timer.c:154-171): a delta below the n-th
# entry is on level n, whose buckets are 8^n ticks wide.
WHEEL_LEVEL_LIMITS = (63, 504, 4032, 32256, 258048, 2064384)
D3_DRAWS = [['init_ephemeral', 'draw'], ['tai64n_now', 'draw'], ['index_draw', 'draw']]


def wheel_granularity(delay):
    """How late (in ticks) the wheel may run a timer armed `delay` ahead:
    calc_index rounds the expiry up to its level's bucket (section 2.2)."""
    for level, limit in enumerate(WHEEL_LEVEL_LIMITS):
        if delay < limit:
            return 8 ** level
    raise ValueError('delay beyond the wheel')


def fire_advance(delay_max):
    """An advance that surely runs a timer armed at most `delay_max` ticks
    ahead within the advance's own wait: the delay, the wheel's rounding
    and the wait, rounded up to 50 ticks (section 7). The margin is a
    heuristic: the trace's `fired:` label is the check."""
    need = delay_max + wheel_granularity(delay_max) + ADVANCE_WAIT_TICKS
    return -(-need // 50) * 50


def quiet_limit(delay_min):
    """The largest total advance after a timer's arm that surely does not run
    it before the trace ends: the real time before and after the advances
    (each at most the bound) and the wait stay below its expiry."""
    return delay_min - ADVANCE_WAIT_TICKS - 2 * TRACE_BOUND_TICKS


def expiry_advance(seconds):
    """An advance past a coarse-boot-time threshold (`wg_birthdate_has_expired`,
    section 6) by one second."""
    return (seconds + 1) * HZ


def steered_timers(rng, trace_id):
    """One steered D3 trace: a session (or none), then advances that fire
    one target timer each, with margin away from the wheel's rounding zone,
    while every other pending timer stays below its quiet limit.

    Sessions: wg0 initiates as in steered_handshake (persistent keepalive
    25 s from wg_up, which sends the initiation), or for `retransmit` and
    `after_new_handshake` a wg_xmit initiates with keepalive 0. Every later
    initiation (a retransmit, a new handshake, a key that needs refreshing)
    gets three `draw` entries: steering covers each encounter of its sites
    (stream K's note, section 13.5). Variants:
    - `retransmit`: no response; 1-3 advances, each firing the retransmit
      timer, whose retry sends another initiation;
    (no `gives_up` chain: its 20 advances do not fit the wait budget; the
    handwritten `d3_retransmit_gives_up` covers the give-up);
    - `keepalive`: 1 or 2 received data messages, an advance (the
      keepalive), and with 2 a second advance that fires nothing (the
      callback's re-arm is deleted by the tx worker);
    - `new_handshake`: data sent, then an advance: a fresh initiation; and
      sometimes data sent again, which re-arms the fired timer;
    - `persistent`: an interval of 5-30 s, one advance: a keepalive;
    - `zero_key`: the keepalive interval set to 0 (its pending timer fires
      as a no-op), one 540 s advance: the clear worker; then a data message
      under the cleared keys and/or a wg_xmit that initiates;
    - `after_new_handshake`: the session from a staged packet (data sent),
      one 540 s advance: the new handshake and the zero-key timer in bucket
      order, the send worker then the clear worker;
    - `expiry`: the interval set to 0, then one of the key-expiry arms of
      section 6 (send after REJECT_AFTER_TIME, send-side keep_key_fresh at
      120 s, receive-side keep_key_fresh at 165 s, receive after
      REJECT_AFTER_TIME);
    - `respond_initiate`: the peer initiates and wg0 responds; an advance
      past REKEY_TIMEOUT lets a wg_xmit initiate, and the response
      completes wg0's session as initiator over the pending next keypair."""
    device = rng.choice(D1_DEVICES)
    peer_private = rng.choice(D1_PEERS)
    peer_public = noise.public_key(peer_private)
    psk = rng.choice([b'\xaa' * 32, rng.randbytes(32)]) if rng.random() < .2 else None
    # No give-up chain (20 advances, about 3.2-3.9 s after wg_up): it does not
    # fit the wait budget at ADVANCE_COST_SECONDS; the handwritten
    # d3_retransmit_gives_up covers it [AGENT, int-dl follow-up 1]
    variant = rng.choices(['retransmit', 'keepalive', 'new_handshake', 'persistent', 'zero_key',
                           'after_new_handshake', 'expiry', 'respond_initiate'],
                          [3, 3, 3, 3, 2, 2, 5, 2])[0]
    allowed4 = rng.choice(D2_ALLOWED4)
    peer = dict(public_key=peer_public.hex(), allowed_ips=[dict(family=4, addr=allowed4[0], cidr=allowed4[1])],
                endpoint=rng.choice(D1_LISTENERS))
    if psk is not None:
        peer['preshared_key'] = psk.hex()
    observe, get = {'op': 'wg_observe'}, {'op': 'wg_get'}
    W, R = ADVANCE_WAIT_TICKS, TRACE_BOUND_TICKS

    def advance(ticks):
        return {'op': 'wg_advance', 'ticks': ticks}

    def destination():
        while True:
            dst = _in_prefix(rng, *allowed4, 4)
            if dst != noise.WG0_ADDR4:
                return dst

    def xmit():
        return {'op': 'wg_xmit', 'packet': dict(family=4, dst=destination().hex(),
                                                payload=rng.randbytes(rng.choice([1, 16, rng.randint(1, 200)])).hex())}

    def inject(message):
        return {'op': 'wg_inject', 'family': rng.choice([4, 6]), 'port': 51820, 'message': message.hex()}

    def data(session, counter):
        src = destination()
        inner = noise.to_wg0(4, src, rng.randbytes(rng.choice([0, 7, 16, rng.randint(1, 100)])),
                             sport=rng.choice([12345, rng.randrange(1, 65536)]))
        return inject(noise.data_message(session.receiving, session.local_index, counter, inner))

    def setup(keepalive):
        p = dict(peer, keepalive=keepalive) if keepalive else peer
        return [{'op': 'wg_set', 'config': dict(private_key=device.hex(), listen_port=51820, peers=[p])},
                {'op': 'wg_up'}]

    def keepalive_off():
        return {'op': 'wg_set', 'config': dict(peers=[dict(public_key=peer_public.hex(), keepalive=0)])}

    def slack(limit):
        return rng.randrange(0, max(1, min(200, limit) + 1))

    # wg0's initiation with steered values, and the peer's response
    ephemeral, index = rng.randbytes(32), rng.randrange(2**32)
    sec, nsec = rng.choice([1, rng.randrange(2**31)]), rng.randrange(10**9)
    steer = [['init_ephemeral', ephemeral.hex()], ['tai64n_now', noise.timespec64(sec, nsec).hex()],
             ['index_draw', index.to_bytes(4, 'little').hex()]]
    ours = noise.steered_initiation(peer_public, device, ephemeral, sec, nsec, index)
    response = noise.response(ours, peer_private, rng.randbytes(32), psk, rng.randrange(2**32),
                              initiator_public=noise.public_key(device))
    session = noise.initiator_session(response)
    respond = inject(response.message)
    fired = lambda name: f'fired:wg_expired_{name}'   # noqa: E731
    retransmit_fire = fire_advance(REKEY_TIMEOUT_TICKS + JITTER_MAX_TICKS)

    if variant == 'retransmit':
        # no session: the initiation's send arms the retransmit timer, the
        # only pending timer; each advance fires it (the rate limit of 5 s
        # has passed too) and its retry re-arms it
        count = rng.choice([1, 1, 2, 3])
        ops = setup(0) + [xmit()]
        for k in range(count):
            ops.append(advance(retransmit_fire + slack(150)))
            if rng.random() < .3:
                ops.append(observe)
        ops += [observe, get]
        expect = [fired('retransmit_handshake'), 'wg_packet_send_staged_packets.no_keypair=1',
                  'wg_expired_retransmit_handshake.give_up=0']
        return dict(version=1, id=trace_id, ops=ops, steer=steer + D3_DRAWS * count, expect=expect)

    session_ops = setup(25) + [observe, respond]
    persistent_quiet = quiet_limit(25 * HZ)
    if variant == 'keepalive':
        n = rng.choice([1, 2])
        ops = session_ops + [data(session, c) for c in range(n)]
        ops.append(advance(fire_advance(KEEPALIVE_TIMEOUT_TICKS) + slack(persistent_quiet - 2600)))
        if n == 2 and rng.random() < .6:
            # the re-arm made in the callback is deleted when the keepalive is sent
            ops.append(advance(fire_advance(KEEPALIVE_TIMEOUT_TICKS)))
        ops += [observe, get]
        expect = D1_SESSION + [fired('send_keepalive'), 'wg_timers_data_received.not_pending=1',
                               f'wg_expired_send_keepalive.need_another={int(n == 2)}']
        if n == 2:
            expect.append('wg_timers_data_received.not_pending=0')
        return dict(version=1, id=trace_id, ops=ops, steer=steer, expect=expect)
    if variant == 'new_handshake':
        target = fire_advance(NEW_HANDSHAKE_TICKS + JITTER_MAX_TICKS)
        assert target <= persistent_quiet
        ops = session_ops + [xmit() for _ in range(rng.choice([1, 2]))]
        ops.append(advance(target + slack(persistent_quiet - target)))
        if rng.random() < .5:
            ops.append(xmit())   # the fired timer is not pending: data_sent re-arms it
        ops += [observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=steer + D3_DRAWS,
                    expect=D1_SESSION + [fired('new_handshake'), 'wg_timers_data_sent.not_pending=1'])
    if variant == 'persistent':
        interval = rng.choice([5, 6, 10, 16, 17, 25, 30])
        ops = setup(interval) + [observe, respond]
        if rng.random() < .5:
            ops.append(observe)
        ops += [advance(fire_advance(interval * HZ) + slack(200)), observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=steer,
                    expect=D1_SESSION + [fired('send_persistent_keepalive'),
                                         'wg_expired_send_persistent_keepalive.interval=1'])
    if variant == 'zero_key':
        # the interval set to 0 leaves the pending persistent timer, which
        # fires first in the pass and sends nothing
        ops = session_ops + [keepalive_off(), advance(fire_advance(ZERO_KEY_TICKS) + slack(200))]
        tail = rng.choice(['data', 'xmit', 'both'])
        if tail in ('data', 'both'):
            ops.append(data(session, 0))       # its keypair's index entry is gone: dropped
        draws = []
        if tail in ('xmit', 'both'):
            ops.append(xmit())                 # no keypair: an initiation
            draws = D3_DRAWS
        ops += [observe, get]
        expect = D1_SESSION + [fired('zero_key_material'), fired('send_persistent_keepalive'),
                               'wg_expired_send_persistent_keepalive.interval=0',
                               'wg_expired_zero_key_material.alive=1']
        if tail != 'xmit':
            expect.append('wg_packet_consume_data.no_keypair=1')
        return dict(version=1, id=trace_id, ops=ops, steer=steer + draws, expect=expect)
    if variant == 'after_new_handshake':
        # keepalive 0: the wg_xmit stages a packet and initiates; the
        # response flushes it (data sent: the new-handshake timer)
        ops = setup(0) + [xmit(), observe, respond, advance(fire_advance(ZERO_KEY_TICKS) + slack(200)), observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=steer + D3_DRAWS,
                    expect=D1_SESSION + [fired('new_handshake'), fired('zero_key_material'),
                                         'wg_expired_zero_key_material.alive=1'])
    if variant == 'expiry':
        arm = rng.choice(['send_expired', 'send_fresh', 'rx_fresh', 'rx_expired'])
        ops = session_ops + [keepalive_off()]
        expect = D1_SESSION + [fired('send_persistent_keepalive'), 'wg_expired_send_persistent_keepalive.interval=0']
        rekey_after, reject_after, rx_fresh_after = 120, 180, 180 - 10 - 5
        if arm == 'send_expired':
            ops += [advance(expiry_advance(reject_after) + slack(750)), xmit()]
            expect.append('wg_packet_send_staged_packets.birthdate_expired=1')
            draws = D3_DRAWS
        elif arm == 'send_fresh':
            # below the receive-side threshold by more than the trace bound
            ops += [advance(expiry_advance(rekey_after) + slack(1000)), xmit()]
            expect += ['keep_key_fresh.birthdate_expired=1', 'keep_key_fresh.send=1']
            draws = D3_DRAWS
        elif arm == 'rx_fresh':
            ops += [advance(expiry_advance(rx_fresh_after) + slack(1000)), data(session, 0)]
            expect += ['keep_key_fresh.rx_birthdate_expired=1', 'keep_key_fresh.rx_send=1']
            if rng.random() < .6:
                ops.append(data(session, 1))   # returns before the clock read
                expect.append('keep_key_fresh.sent_lastminute=1')
            draws = D3_DRAWS
        else:
            ops += [advance(expiry_advance(reject_after) + slack(750)), data(session, 0)]
            expect.append('decrypt_packet.key_expired=1')
            draws = []
        ops += [observe, get]
        return dict(version=1, id=trace_id, ops=ops, steer=steer + draws, expect=expect)
    # respond_initiate: the response sets last_sent_handshake; an advance past
    # REKEY_TIMEOUT lets the staged packet's initiation through
    raw, wg0_index = rng.randbytes(32), rng.randrange(2**32)
    theirs = noise.initiation(noise.public_key(device), peer_private, rng.randbytes(32),
                              noise.tai64n(rng.randrange(2**31), rng.randrange(10**9)), rng.randrange(2**32))
    noise.wg0_response(theirs, device, raw, psk, wg0_index)   # the handshake is consumable
    second = noise.response(ours, peer_private, rng.randbytes(32), psk, rng.randrange(2**32),
                            initiator_public=noise.public_key(device))
    ops = setup(0) + [inject(theirs), advance(REKEY_TIMEOUT_TICKS + 2 * W + slack(400)), xmit(), observe,
                      inject(second.message), observe, get]
    draws = [['resp_ephemeral', raw.hex()], ['index_draw', wg0_index.to_bytes(4, 'little').hex()]]
    return dict(version=1, id=trace_id, ops=ops, steer=draws + steer,
                expect=['wg_receive_handshake_packet.initiation=1'] + D1_SESSION)
