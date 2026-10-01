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


def generate_wireguard(seed, count, max_ops=12):
    """Seeded WireGuard traces over small pools of keys and prefixes, so that
    peers, trie nodes and identities collide often. A third are configuration
    traces (stage A), and the rest bring wg0 up and transmit (stage B1), inject
    messages (stage B2), or inject handshake initiations (stage C), a sixth
    each. Every trace ends with a dump."""
    if not 2 <= max_ops <= 64 or not 1 <= count <= 100000:
        raise ValueError('bounded generator parameters')
    rng = random.Random(seed)
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
        trace = dict(version=1, id=f'generated-wg-{seed}-{len(result):05}', ops=operations)
        digest = identity(trace)
        if digest not in seen:
            seen.add(digest)
            result.append(trace)
    return result
