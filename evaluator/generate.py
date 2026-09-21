"""Seeded, bounded trace generation and dependency-preserving reduction."""
from copy import deepcopy
import hashlib
import json
import random

U64 = 2**64 - 1
PRODUCERS = {'eventfd2', 'dup', 'dup3'}


def identity(trace):
    """Trace identity excludes its human-readable label."""
    return hashlib.sha256(json.dumps({'version': trace['version'], 'ops': trace['ops']},
                                   sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def generate(seed=20260920, count=1000, max_ops=64):
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
