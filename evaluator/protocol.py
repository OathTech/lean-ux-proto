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
# W7: a batch's completions present when io_uring_enter returned (each
# item's length, or the sender's errno; null for an item without one)
# epoll R (docs/2026-10-12-epoll-design.md 6): an epoll_wait's events go
# through the read channel: `bytes` is the first 64 of the ret * 12 bytes of
# the packed epoll_event array, `digest` the BLAKE2s-256 of all of them
# seccomp W (docs/2026-10-12-seccomp-design.md 6.1): a probe carries `sigsys`
# (the SIGSYS handler's {nr, data, arch} after a TRAP, else null) and
# `child` (a child probe's record: an optional strict_ret, then exactly one
# of ret, exited or signal; null for a self probe)
EXTRA_FIELDS = {'pipe2': ('fds',), 'read': ('digest',), 'write': ('sigpipe',), 'wg_batch': ('cqes',),
                'epoll_wait': ('digest',), 'seccomp_probe': ('sigsys', 'child'),
                # lane C's shape oracle (docs/2026-10-15-design-c-fib-trie.md, 9.4): after an
                # operation that changes the IPv4 tables, the trie as /proc/net/fib_trie
                # prints it, read by the guest outside the window and serialised by the mirror
                'wg_up': ('fib_trie',), 'wg_down': ('fib_trie',), 'wg_delete': ('fib_trie',),
                'wg_deladdr': ('fib_trie',), 'wg_delroute': ('fib_trie',), 'wg_set_mtu': ('fib_trie',),
                'wg_netns_close': ('fib_trie',)}
EPOLL_EVENT_SIZE = 12   # sizeof(struct epoll_event) on x86-64 (packed)


def injected_messages(trace):
    """The ceiling on the mirror's open NAPI placements in a trace: one (c')
    placement arises per `wg_queue_enqueue_per_peer_rx`, that is per data
    message the fixture delivered to wg0, so the count can never exceed the
    messages the trace injects (`wg_inject`, a `wg_flood`'s count and its
    leading `messages`, a `wg_batch`'s inject items). A 1024-item receive
    batch legitimately opens about a thousand (the receive-side ring-full
    trace of the W7 tier); a count above this ceiling is an invalid output
    (claim-point robustness, 2026-10-13). At least 1, the field's floor."""
    total = 0
    for op in trace.get('ops', ()):
        name = op.get('op')
        if name == 'wg_inject':
            total += 1
        elif name == 'wg_flood':
            total += integer_or(op.get('count'), 0) + len(op.get('messages') or ())
        elif name == 'wg_batch':
            total += sum(1 for item in (op.get('items') or ()) if type(item) is dict and item.get('kind') == 'inject')
    return max(1, total)


def integer_or(value, default):
    return value if type(value) is int and value >= 0 else default


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
    if 'napi_irq_ambiguous' in result and not integer(result['napi_irq_ambiguous'], 1, injected_messages(trace)):
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
        if op['op'] == 'wg_get_recv' and type(obs) is dict and obs.get('ret') == 0:
            fields += ('messages',)   # W2: one receive's messages, as put (harness/wg.py decode_messages)
        if op['op'] == 'wg_observe':
            fields += ('datagrams', 'replies', 'stats')   # what wg0 emitted, replies to the sender, counters
        if not keys(obs, fields):
            raise InvalidOutput(f'observation {index}: fields')
        if 'device' in fields and type(obs['device']) is not dict:
            raise InvalidOutput(f'observation {index}: device state')
        # stats null: no wg0 (L); datagrams null: the listeners closed by
        # wg_netns_close (W8), where the recvfrom is -EBADF
        if 'datagrams' in fields and ((obs['datagrams'] is not None and type(obs['datagrams']) is not list)
                                      or (obs['datagrams'] is None and obs.get('ret') != -9)
                                      or type(obs['replies']) is not list
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
        if 'cqes' in fields and (type(obs['cqes']) is not list
                                 or not all(x is None or integer(x, -4095, 2**31 - 1) for x in obs['cqes'])):
            raise InvalidOutput(f'observation {index}: cqes')
        if 'sigsys' in fields and not (obs['sigsys'] is None or (
                keys(obs['sigsys'], ('nr', 'data', 'arch')) and integer(obs['sigsys']['nr'], -2**31, 2**31 - 1)
                and integer(obs['sigsys']['data'], -2**31, 2**31 - 1) and integer(obs['sigsys']['arch'], 0, 2**32 - 1))):
            raise InvalidOutput(f'observation {index}: sigsys')
        if 'child' in fields:
            child = obs['child']
            if child is not None and not (type(child) is dict and (
                    (set(child) - {'strict_ret'}) in ({'ret'}, {'exited'}, {'signal'})
                    and ('strict_ret' not in child or integer(child['strict_ret'], -4095, 2**31 - 1))
                    and ('ret' not in child or integer(child['ret'], -2**63, 2**63 - 1))
                    and ('exited' not in child or integer(child['exited'], 0, 255))
                    and ('signal' not in child or integer(child['signal'], 1, 64)))):
                raise InvalidOutput(f'observation {index}: child')
            if (op['op'] == 'seccomp_probe') and ((op['where'] == 'child') != (child is not None)):
                raise InvalidOutput(f'observation {index}: child record of a {op["where"]} probe')
        if type(obs['index']) is not int or obs['index'] != index:
            raise InvalidOutput(f'observation {index}: order/index')
        ret, error, data = obs['ret'], obs['errno'], obs['bytes']
        if not integer(ret, -4095, 2**63 - 1):
            raise InvalidOutput(f'observation {index}: return range')
        if (ret < 0 and (not integer(error, 1, 4095) or error != -ret)) or (ret >= 0 and error is not None):
            raise InvalidOutput(f'observation {index}: contradictory errno')
        if type(data) is not str or not re.fullmatch(r'(?:[0-9a-f]{2}){0,%d}' % READ_HEAD, data):
            raise InvalidOutput(f'observation {index}: byte encoding')
        expected = min(ret, READ_HEAD) if op['op'] == 'read' and ret >= 0 else \
            min(ret * EPOLL_EVENT_SIZE, READ_HEAD) if op['op'] == 'epoll_wait' and ret >= 0 else 0
        if len(data) != 2 * expected:
            raise InvalidOutput(f'observation {index}: byte count')
    branches = result['branches']
    # W4 (docs/2026-10-06-w4-w7-transmit-bulk.md, 2.2): a multi-packet ring
    # item (the 129-packet flush of w4_gso_trim) reports about 2800 branches
    # in one operation; the bound follows the bulk tiers (W7), as the guest's
    # output limit bounds the whole
    if type(branches) is not list or len(branches) > MAX_BRANCHES:
        raise InvalidOutput('branch report size')
    for branch in branches:
        # W7 stream H (docs/2026-10-06-w4-w7-transmit-bulk.md, 13.2 (ii)): a
        # branch inside a NET_RX section carries the section's ordinal
        fields = ('index', 'label') + (('section',) if 'section' in branch else ())
        if not (keys(branch, fields) or keys(branch, fields + ('operands',))
                or keys(branch, fields + ('operands_excluded',))) \
                or not integer(branch['index'], 0, len(trace['ops']) - 1) \
                or ('section' in branch and not integer(branch['section'], 1, MAX_BRANCHES)):
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
# The mirror's branches per trace (W4: raised from 4096 for multi-packet items;
# the W7 full-ring tier: a 1024-item wg_batch reports 126,531 labels on the
# wrap trace, docs/2026-10-13-w7-full-ring-tier.md, so 2^18 with headroom
# for the 1025-item trace)
MAX_BRANCHES = 262144

SEMANTIC_ERRNOS = {'eventfd2': {12, 22, 24}, 'dup': {9, 12, 24}, 'dup3': {9, 12, 22},
                   'close': {9}, 'fcntl': {1, 9, 12, 22},
                   # L (docs/2026-10-05-l-lifecycle.md): ENODEV without wg0;
                   # EADDRINUSE binding a fixture port (wg_up, a running wg_set)
                   # W1: EBADR (both or neither selector), EPFNOSUPPORT (protocol version),
                   # EOPNOTSUPP on wg_get (a non-WireGuard device); W8: EPERM for a port or fwmark
                   # after the creating namespace exited
                   'wg_set': {12, 22, 95, 19, 98, 53, 96, 1}, 'wg_get': {22, 19, 53, 95},
                   # ENOKEY, EDESTADDRREQ, EPROTONOSUPPORT, ENETUNREACH (no route before wg_up); EAGAIN when nothing arrived
                   # W8: wg_up's ENONET after the creating namespace exited; wg_observe's
                   # EBADF once the listeners are closed; wg_netns_close fails only
                   # outside the oracle's setup (the holders are the fixture's);
                   # W4: wg_xmit's EMSGSIZE and EINVAL from the sender's IP layer
                   'wg_up': {19, 98, 64}, 'wg_xmit': {126, 89, 93, 101, 90, 22}, 'wg_observe': {11, 9}, 'read': {9, 11, 22}, 'write': {9, 11, 22},
                   'wg_netns_close': set(),
                   # D3: the advance ioctl fails only outside the oracle's setup (-EOPNOTSUPP, -EINVAL, -EPERM)
                   'wg_advance': set(),
                   # E-B: the io_uring submission (wg_flood) fails only outside the oracle's setup
                   'wg_flood': set(),
                   # W7: the batch's submission likewise; per-item results are its cqes
                   'wg_batch': set(),
                   # W4: dev_validate_mtu's -EINVAL (net/core/dev.c:9061-9075: negative, or
                   # above max_mtu; the audit of 2026-10-13 corrected this from -ERANGE)
                   'wg_set_mtu': {19, 22},
                   # EEXIST (a second wg0), ENODEV (no wg0)
                   'wg_create': {17}, 'wg_down': {19}, 'wg_delete': {19},
                   # W9 (docs/2026-10-06-w8-w9-netns-routing.md 4.3): RTM_DELADDR of
                   # wg0's fixture address (EADDRNOTAVAIL when absent) and
                   # RTM_DELROUTE of the default route via wg0 (ESRCH when absent)
                   'wg_deladdr': {99}, 'wg_delroute': {3},
                   # W2 (docs/2026-10-06-w1-w2-netlink.md 4.2): the stepped dump's
                   # request is acknowledged on a later receive, never failed; a
                   # receive with nothing queued is EAGAIN (the mirror's unsupported)
                   'wg_get_start': set(), 'wg_get_recv': {11}}
# Pipes (P design section 6): EINVAL, EMFILE, ENOPKG (O_NOTIFICATION_PIPE
# without CONFIG_WATCH_QUEUE); EPIPE on write; EBUSY from F_SETPIPE_SZ.
# A's pipe sites (section 19.6; D3+A integration): pipe2's ENFILE (a failed
# alloc_pipe_info in get_pipe_inode) and write's ENOMEM (pipe_write's first
# page, `ret ? : -ENOMEM`) are compared; Linux gives them only under a
# declared failslab trace (harness/linux.py), otherwise environment failures.
SEMANTIC_ERRNOS['pipe2'] = {22, 23, 24, 65}
# epoll R (docs/2026-10-12-epoll-design.md, 2.1, 2.2, 2.6): epoll_create1's
# EINVAL (flags), EMFILE, ENOMEM (ep_alloc, the file, the fd table);
# epoll_ctl's EBADF, EPERM (a target without poll), EINVAL, EEXIST, ENOENT,
# ELOOP, ENOSPC (max_user_watches), ENOMEM (the item, the pwq, the head);
# epoll_wait's EINVAL (maxevents, not an epoll file) and EBADF
SEMANTIC_ERRNOS['epoll_create1'] = {12, 22, 24}
SEMANTIC_ERRNOS['epoll_ctl'] = {1, 2, 9, 12, 17, 22, 28, 40}
SEMANTIC_ERRNOS['epoll_wait'] = {9, 22}
# seccomp W (docs/2026-10-12-seccomp-design.md 2.2, 2.4, 2.9, 2.10): an
# install's EINVAL (flags, length, checker, mode), EFAULT (the bad pointers),
# EACCES (no no-new-privs and no CAP_SYS_ADMIN), ENOMEM (the path budget
# MAX_INSNS_PER_PATH; a real allocation failure surfaces as a mirror mismatch);
# a self probe's ENOSYS (TRACE without a tracer, call 1000, call 335), or the
# errno a filter returns (ERRNO's data 1..4095); the prctl queries' EINVAL;
# capset's EPERM/EINVAL; the queries' EINVAL and EOPNOTSUPP
SEMANTIC_ERRNOS['seccomp_install'] = {22, 14, 13, 12}
SEMANTIC_ERRNOS['seccomp_probe'] = set(range(1, 4096))
SEMANTIC_ERRNOS['seccomp_prctl'] = {22}
SEMANTIC_ERRNOS['seccomp_capdrop'] = {1, 22, 14}
SEMANTIC_ERRNOS['seccomp_query'] = {22, 95, 14}
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
