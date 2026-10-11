"""Strict observation validation and literal per-operation comparison (trace v1)."""
import json
import re

from harness.trace import KCOV_CAPACITY


class InvalidOutput(ValueError):
    pass


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InvalidOutput(f'duplicate JSON field: {key}')
        result[key] = value
    return result


def loads(text):
    try:
        return json.loads(text, object_pairs_hook=unique_object,
                          parse_constant=lambda x: (_ for _ in ()).throw(InvalidOutput(x)))
    except (ValueError, RecursionError) as exc:
        raise InvalidOutput(str(exc)) from exc


def integer(value, low, high):
    return type(value) is int and low <= value <= high


def keys(value, expected):
    return type(value) is dict and set(value) == set(expected)


# The pipes observation contract (docs/2026-10-05-p-pipes.md section 6).
# A read's "bytes" is the hex of its first READ_HEAD bytes (all of them when
# ret <= READ_HEAD; eventfd reads are unchanged). Each operation kind's fields
# beyond index/ret/errno/bytes:
#   pipe2: "fds": [r, w] after success, null on failure
#   read:  "digest": 64 hex digits, BLAKE2s-256 of all ret bytes when ret > 0,
#          else null
#   write: "sigpipe": 0 or 1, whether SIGPIPE is pending after the call
# `digest` and `sigpipe` are emitted by the guest (harness/guest.c) and the
# runner (Leanux/Runner.lean readDigest, writeSigpipe) for every read and
# write, eventfd's included (stream P1 switched them on together).
READ_HEAD = 64
MAX_IO = 69632
DIGEST = re.compile(r'[0-9a-f]{64}')
EXTRA_FIELDS = {'pipe2': ('fds',), 'read': ('digest',), 'write': ('sigpipe',)}


def validate_observation(trace, result):
    """Check protocol shape, not whether the claimed semantics are correct."""
    # D3: the mirror adds `fired` (the timer sections its environment ran,
    # for `fired:<symbol>` expectations) when one ran; it reports how many
    # NAPI poll placements its records left open (Env.napiIrqExit), which the
    # check enumerates
    base = ('version', 'id', 'observations', 'branches')
    if not any(keys(result, base + extra) for extra in
               ((), ('fired',), ('napi_irq_ambiguous',), ('fired', 'napi_irq_ambiguous'))):
        raise InvalidOutput('observation fields')
    if 'napi_irq_ambiguous' in result and not integer(result['napi_irq_ambiguous'], 1, 64):
        raise InvalidOutput('napi_irq_ambiguous')
    if type(result['version']) is not int or result['version'] != 1 or result['id'] != trace['id']:
        raise InvalidOutput('version or trace identity')
    observations = result['observations']
    if type(observations) is not list or len(observations) != len(trace['ops']):
        raise InvalidOutput('missing or extra observations')
    for index, (op, obs) in enumerate(zip(trace['ops'], observations)):
        fields = ('index', 'ret', 'errno', 'bytes') + EXTRA_FIELDS.get(op['op'], ())
        if op['op'] == 'wg_get' and type(obs) is dict and obs.get('ret') == 0:
            fields += ('device',)   # the canonical device state (harness/wg.py)
        if op['op'] == 'wg_observe':
            fields += ('datagrams', 'replies', 'stats')   # what wg0 emitted, replies to the sender, counters
        if not keys(obs, fields):
            raise InvalidOutput(f'observation {index}: fields')
        if 'device' in fields and type(obs['device']) is not dict:
            raise InvalidOutput(f'observation {index}: device state')
        # stats null: no wg0 (L)
        if 'datagrams' in fields and (type(obs['datagrams']) is not list or type(obs['replies']) is not list
                                      or (obs['stats'] is not None and type(obs['stats']) is not dict)):
            raise InvalidOutput(f'observation {index}: observed emissions')
        if 'fds' in fields and not (
                (obs.get('ret') == 0 and type(obs['fds']) is list and len(obs['fds']) == 2
                 and all(integer(fd, 0, 2**31 - 1) for fd in obs['fds']) and obs['fds'][0] != obs['fds'][1])
                or (obs.get('ret') != 0 and obs['fds'] is None)):
            raise InvalidOutput(f'observation {index}: pipe descriptors')
        if 'digest' in fields and not (
                (type(obs.get('ret')) is int and obs['ret'] > 0 and type(obs['digest']) is str
                 and DIGEST.fullmatch(obs['digest']))
                or (not (type(obs.get('ret')) is int and obs['ret'] > 0) and obs['digest'] is None)):
            raise InvalidOutput(f'observation {index}: digest')
        if 'sigpipe' in fields and (type(obs['sigpipe']) is not int or obs['sigpipe'] not in (0, 1)):
            raise InvalidOutput(f'observation {index}: sigpipe')
        if type(obs['index']) is not int or obs['index'] != index:
            raise InvalidOutput(f'observation {index}: order/index')
        ret, error, data = obs['ret'], obs['errno'], obs['bytes']
        if not integer(ret, -4095, 2**63 - 1):
            raise InvalidOutput(f'observation {index}: return range')
        if (ret < 0 and (not integer(error, 1, 4095) or error != -ret)) or (ret >= 0 and error is not None):
            raise InvalidOutput(f'observation {index}: contradictory errno')
        if type(data) is not str or not re.fullmatch(r'(?:[0-9a-f]{2}){0,%d}' % READ_HEAD, data):
            raise InvalidOutput(f'observation {index}: byte encoding')
        expected = min(ret, READ_HEAD) if op['op'] == 'read' and ret >= 0 else 0
        if len(data) != 2 * expected:
            raise InvalidOutput(f'observation {index}: byte count')
    branches = result['branches']
    if type(branches) is not list or len(branches) > 4096:
        raise InvalidOutput('branch report size')
    for branch in branches:
        if not (keys(branch, ('index', 'label')) or keys(branch, ('index', 'label', 'operands'))
                or keys(branch, ('index', 'label', 'operands_excluded'))) \
                or not integer(branch['index'], 0, len(trace['ops']) - 1):
            raise InvalidOutput('branch fields/index')
        # a declared operand exclusion (correspondence/kcov.json) names the operand
        if 'operands_excluded' in branch and not (type(branch['operands_excluded']) is str
                                                  and 1 <= len(branch['operands_excluded']) <= 80):
            raise InvalidOutput('branch operands_excluded')
        if 'operands' in branch and not (type(branch['operands']) is list and len(branch['operands']) == 2
                                         and all(integer(x, -2**63, 2**64 - 1) for x in branch['operands'])):
            raise InvalidOutput('branch operands')
        if type(branch['label']) is not str or not 1 <= len(branch['label']) <= 120:
            raise InvalidOutput('branch label')
    fired = result.get('fired')
    if fired is not None and (type(fired) is not list or not 1 <= len(fired) <= 4096 or any(
            not keys(f, ('index', 'symbol')) or not integer(f['index'], 0, len(trace['ops']) - 1)
            or type(f['symbol']) is not str or not re.fullmatch(r'[a-z0-9_]{1,80}', f['symbol']) for f in fired)):
        raise InvalidOutput('fired timer sections')
    return result


def parse_batch(traces, output, max_bytes=16 * 1024 * 1024):
    if not traces:
        raise InvalidOutput('empty required test batch')
    if len(output) > max_bytes:
        raise InvalidOutput('oversized output')
    if isinstance(output, bytes):
        try:
            output = output.decode('utf-8', errors='strict')
        except UnicodeError as exc:
            raise InvalidOutput('invalid UTF-8') from exc
    lines = output.splitlines()
    if len(lines) != len(traces) or any(not line for line in lines):
        raise InvalidOutput('missing, extra, or empty output lines')
    return [validate_observation(t, loads(line)) for t, line in zip(traces, lines)]


# These outcomes cannot be ordinary results in the declared single-threaded,
# valid-buffer fixture. In particular resource failure must not count as agreement.
# ENOMEM (12) is compared, not absorbed, where an allocation outcome the
# mirror consumes from the records can produce it (docs/2026-10-05-a-alloc.md
# 6.3; A2): eventfd2 (the context, file, dentry and fd table), dup, dup3 and
# fcntl (F_DUPFD*: the fd table), wg_set (peer and allowed-ips nodes). A
# Linux ENOMEM the mirror did not take is a semantic mismatch, and its
# record is unconsumed or absent: fail-noisy on both sides.
SEMANTIC_ERRNOS = {'eventfd2': {12, 22, 24}, 'dup': {9, 12, 24}, 'dup3': {9, 12, 22},
                   'close': {9}, 'fcntl': {1, 9, 12, 22},
                   # L (docs/2026-10-05-l-lifecycle.md): ENODEV without wg0;
                   # EADDRINUSE binding a fixture port (wg_up, a running wg_set)
                   'wg_set': {12, 22, 95, 19, 98}, 'wg_get': {22, 19},
                   # ENOKEY, EDESTADDRREQ, EPROTONOSUPPORT, ENETUNREACH (no route before wg_up); EAGAIN when nothing arrived
                   'wg_up': {19, 98}, 'wg_xmit': {126, 89, 93, 101}, 'wg_observe': {11}, 'read': {9, 11, 22}, 'write': {9, 11, 22},
                   # D3: the advance ioctl fails only outside the oracle's setup (-EOPNOTSUPP, -EINVAL, -EPERM)
                   'wg_advance': set(),
                   # E-B: the io_uring submission (wg_flood) fails only outside the oracle's setup
                   'wg_flood': set(),
                   # EEXIST (a second wg0), ENODEV (no wg0)
                   'wg_create': {17}, 'wg_down': {19}, 'wg_delete': {19},
                   # W9 (docs/2026-10-06-w8-w9-netns-routing.md 4.3): RTM_DELADDR of
                   # wg0's fixture address (EADDRNOTAVAIL when absent) and
                   # RTM_DELROUTE of the default route via wg0 (ESRCH when absent)
                   'wg_deladdr': {99}, 'wg_delroute': {3}}
# Opcodes 20-21 (W2) and 22 (W8) are reserved (harness/trace.py
# RESERVED_OPCODES); their operations, and so their entries here, come with
# the streams that land them. W9 took 23 and 24.
# Pipes (P design section 6): EINVAL, EMFILE, ENOPKG (O_NOTIFICATION_PIPE
# without CONFIG_WATCH_QUEUE); EPIPE on write; EBUSY from F_SETPIPE_SZ.
# A's pipe sites (section 19.6; D3+A integration): pipe2's ENFILE (a failed
# alloc_pipe_info in get_pipe_inode) and write's ENOMEM (pipe_write's first
# page, `ret ? : -ENOMEM`) are compared; Linux gives them only under a
# declared failslab trace (harness/linux.py), otherwise environment failures.
SEMANTIC_ERRNOS['pipe2'] = {22, 23, 24, 65}
SEMANTIC_ERRNOS['write'] = SEMANTIC_ERRNOS['write'] | {12, 32}
SEMANTIC_ERRNOS['fcntl'] = SEMANTIC_ERRNOS['fcntl'] | {16}


def compare(trace, linux, model):
    for side, obs in (('linux', linux), ('model', model)):
        try:
            validate_observation(trace, obs)
        except InvalidOutput as exc:
            return dict(id=trace['id'], outcome='invalid_output', side=side, detail=str(exc))
    for index, obs in enumerate(linux['observations']):
        if obs['errno'] is not None and obs['errno'] not in SEMANTIC_ERRNOS[trace['ops'][index]['op']]:
            return dict(id=trace['id'], outcome='environment_failure', index=index, observation=obs)
    for index, (actual, expected) in enumerate(zip(model['observations'], linux['observations'])):
        # Canonical JSON keeps types apart (True vs 1, list vs tuple) in the
        # nested device state; key order is irrelevant.
        if json.dumps(actual, sort_keys=True) != json.dumps(expected, sort_keys=True):
            return dict(id=trace['id'], outcome='semantic_mismatch', index=index,
                        operation=trace['ops'][index], linux=expected, model=actual)
    return dict(id=trace['id'], outcome='agreement', operations=len(trace['ops']))


def validate_coverage(traces, coverage):
    """One numbered KCOV record per operation, in the runner's wire order."""
    expected = [(trace['id'], index) for trace in traces for index in range(len(trace['ops']))]
    if type(coverage) is not list or len(coverage) != len(expected):
        raise InvalidOutput('missing or extra coverage operations')
    for (ident, index), entry in zip(expected, coverage):
        if not keys(entry, ('id', 'index', 'count', 'pcs')) or entry['id'] != ident or type(entry['index']) is not int or entry['index'] != index:
            raise InvalidOutput('coverage identity/operation order')
        pcs = entry['pcs']
        # a network row is the task and remote streams, each below CAPACITY - 1
        if type(pcs) is not list or not pcs or not integer(entry['count'], len(pcs), 2 * (KCOV_CAPACITY - 1) - 1):
            raise InvalidOutput('missing or truncated per-operation coverage')
        if any(type(pc) is not str or not re.fullmatch(r'0x[0-9a-f]{16}', pc) for pc in pcs) or len(set(pcs)) != len(pcs):
            raise InvalidOutput('invalid coverage PC set')
