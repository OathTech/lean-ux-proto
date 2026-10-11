"""Steering schedules (docs/2026-10-03-choice-stream-strategy.md, step 2):
resolve a trace's `steer` entries ([site label, value hex or "draw"]) into the
kernel's schedule entries: the hooked call's kind, the value's length, and the
return addresses of the calls whose consumer frame is the site.

The return addresses come from the kernel image: every call to a hooked
random or clock entry point, symbolized with its inline chain; the consumer
frame is the first frame outside the random and clock helpers, as the check
attributes records (evaluator/check.py). The result is cached per kernel.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

# The hooked entry points and their kinds (kernel/patches/choice-stream.patch).
HOOKS = {'get_random_bytes': 1, 'get_random_u8': 101, 'get_random_u16': 102, 'get_random_u32': 104,
         'get_random_u64': 108, '__get_random_u32_below': 110}
CLOCKS = ['ktime_get_mono_fast_ns', 'ktime_get_raw_fast_ns', 'ktime_get_boot_fast_ns', 'ktime_get_tai_fast_ns',
          'ktime_get_real_fast_ns', 'ktime_get_real_ts64', 'ktime_get', 'ktime_get_with_offset',
          'ktime_get_coarse_with_offset', 'ktime_get_raw', 'ktime_get_ts64', 'ktime_get_seconds',
          'ktime_get_real_seconds', 'ktime_get_raw_ts64', 'getboottime64', 'ktime_get_coarse_real_ts64',
          'ktime_get_coarse_ts64']
HOOKS.update({name: 200 + i for i, name in enumerate(CLOCKS)})
CHOICE_HELPERS = ('drivers/char/random.c', 'include/linux/random.h', 'kernel/time/timekeeping.c',
                  'include/linux/timekeeping.h', 'include/crypto/curve25519.h', 'include/linux/hrtimer.h',
                  'include/linux/sched.h')   # cond_resched's inline wrapper (resched records)
# Sites a trace may steer, and their domains (strategy section 3): every
# value in the domain is a possible output of the source.
# L (docs/2026-10-05-l-lifecycle.md section 3.3): udp_lib_get_port's
# get_random_u32 (net/ipv4/udp.c:257), any 4 bytes.
STEERABLE = {'init_ephemeral', 'resp_ephemeral', 'index_draw', 'tai64n_now', 'udp_port_draw'}
TIME_SETTOD_SEC_MAX = (1 << 63) // 1_000_000_000 - 30 * 365 * 24 * 3600   # KTIME_SEC_MAX - TIME_UPTIME_SEC_MAX


class SteeringError(ValueError):
    pass


def symbolize(vmlinux, addresses):
    """Each address's inline chain, innermost first: [(function, file:line)]."""
    query = ''.join(hex(a) + '\n' for a in addresses).encode()
    lines = subprocess.run(['addr2line', '-e', str(vmlinux), '-a', '-i', '-f'], input=query, capture_output=True,
                           check=True).stdout.decode().splitlines()
    chains, k = [], 0
    while k < len(lines):
        if lines[k].startswith('0x'):
            chains.append([])
            k += 1
        else:
            chains[-1].append((lines[k], lines[k + 1].split('/.deps/linux/')[-1].split(' ')[0]))
            k += 2
    if len(chains) != len(addresses):
        raise SteeringError('malformed addr2line output')
    return chains


def call_sites(vmlinux, cache_dir):
    """{(kind, consumer "file:line"): [return addresses]} for every call to a
    hooked entry point in the image."""
    digest = hashlib.sha256(Path(vmlinux).read_bytes()).hexdigest()
    cache = Path(cache_dir) / f'steer-sites-v2-{digest}.json'
    if cache.exists():
        return {(k, c): v for k, c, v in json.loads(cache.read_text())}
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', str(vmlinux)], capture_output=True, text=True,
                         check=True).stdout.splitlines()
    calls, tail_jumps = [], []
    for current, following in zip(out, out[1:]):
        m = re.search(r'\t(call|jmp)\s+[0-9a-f]+ <([A-Za-z0-9_.]+)>$', current)
        if not m or m.group(2) not in HOOKS:
            continue
        nxt = re.match(r'\s*([0-9a-f]+):', following)
        if m.group(1) == 'jmp':
            tail_jumps.append(int(current.strip().split(':')[0], 16))
        elif nxt:
            calls.append((HOOKS[m.group(2)], int(nxt.group(1), 16)))
    chains = symbolize(vmlinux, [ip - 1 for _, ip in calls] + tail_jumps)
    sites = {}
    for (kind, ip), chain in zip(calls, chains):
        consumer = next((src for _, src in chain if src.split(':')[0] not in CHOICE_HELPERS), None)
        if consumer:
            entry = sites.setdefault((kind, consumer), {'ips': [], 'functions': []})
            entry['ips'].append(ip)
            entry['functions'] = sorted(set(entry['functions']) | {chain[-1][0]})
    # A tail jump into a hook hides its consumer's frame from _RET_IP_: such
    # records are attributed to the caller's caller. resolve() refuses a site
    # in a function that tail-jumps to a hook.
    sites[('tail_jumps', '')] = sorted({chain[-1][0] for chain in chains[len(calls):]})
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps([[k, c, v] for (k, c), v in sorted(sites.items(), key=str)]))
    return sites


def resolve(trace, site_table, sites, alloc_sites=None):
    """The trace's schedule for the kernel: [(kind, length, draw, ips, hex)],
    allocation entries with a sixth element, the flags.
    `site_table`: the mirror's sites by label (leanux-model --hidden-sites).
    `alloc_sites`: alloc_call_sites(...), needed for allocation labels."""
    out = []
    if trace.get('domain_extension') and not any(
            label in ALLOC_SITES and value != 'draw'
            and ALLOC_SITES[label]['cls'] in EXTENSION_CLASSES[trace['domain_extension']]
            for label, value in trace['steer']):
        raise SteeringError(f'{trace["id"]}: declares the {trace["domain_extension"]} extension but forces no failure '
                            'in its classes')
    for label, value in trace['steer']:
        if label in ALLOC_SITES:
            reason = alloc_refusal(trace, label, value)
            if reason:
                raise SteeringError(f'{trace["id"]}: {reason}')
            mirror = site_table.get(label)
            consumer = ALLOC_SITES[label]['consumer']
            if mirror is None or mirror['kind'] != 'alloc' or f"{mirror['file']}:{mirror['line']}" != consumer:
                raise SteeringError(f'{trace["id"]}: the mirror declares {label} elsewhere than {consumer}')
            if alloc_sites is None:
                raise SteeringError(f'{trace["id"]}: allocation sites not resolved')
            out.append(alloc_entry(label, value, alloc_sites))
            continue
        entry = site_table.get(label)
        if entry is None or label not in STEERABLE:
            raise SteeringError(f'{trace["id"]}: {label!r} is not a steerable site')
        consumer = f"{entry['file']}:{entry['line']}"
        kinds = [(k, v) for (k, c), v in sites.items() if k != 'tail_jumps' and c == consumer
                 and (k < 200) == (entry['kind'] == 'random')]
        if len(kinds) != 1 or not 1 <= len(kinds[0][1]['ips']) <= 4:
            raise SteeringError(f'{trace["id"]}: site {label} resolves to {kinds}')
        kind, found = kinds[0]
        ips = found['ips']
        if set(found['functions']) & set(sites.get(('tail_jumps', ''), [])):
            raise SteeringError(f'{trace["id"]}: site {label} is in a function that tail-jumps to a hook')
        if value != 'draw':
            data = bytes.fromhex(value)
            if len(data) != entry['len']:
                raise SteeringError(f'{trace["id"]}: {label} takes {entry["len"]} bytes')
            if label == 'tai64n_now':
                sec = int.from_bytes(data[:8], 'little', signed=True)
                nsec = int.from_bytes(data[8:], 'little', signed=True)
                if not (0 <= sec < TIME_SETTOD_SEC_MAX and 0 <= nsec < 1_000_000_000):
                    raise SteeringError(f'{trace["id"]}: tai64n_now outside the wall clock\'s range')
        out.append((kind, entry['len'], value == 'draw', ips, '' if value == 'draw' else value))
    return out


# ---- Allocation outcomes (docs/2026-10-05-a-alloc.md, sections 4-5) ----
# The allocator entry points a consumer calls directly (inline kmalloc,
# kzalloc, kmem_cache_zalloc, kcalloc, alloc_page wrappers end in these),
# and the out-of-line helpers whose allocations a helper site steers.
ALLOC_ENTRIES = ('__kmalloc_cache_noprof', '__kmalloc_noprof', '__kmalloc_node_noprof', 'kmem_cache_alloc_noprof',
                 'kmem_cache_alloc_lru_noprof', 'kmem_cache_alloc_node_noprof', '__kmalloc_cache_node_noprof',
                 '__alloc_pages_noprof')
# helper -> the functions whose whole ranges arm its allocations (the
# helper and the out-of-line allocating helpers below it)
ALLOC_HELPER_RANGES = {'__alloc_skb': ('__alloc_skb', 'kmalloc_reserve'),
                       'skb_cow_data': ('pskb_expand_head', 'kmalloc_reserve'),
                       'd_alloc_pseudo': ('__d_alloc',),
                       '__kvmalloc_node_noprof': ('__kvmalloc_node_noprof',)}
ALLOC_HELPER_FILES = ('include/linux/slab.h', 'include/linux/gfp.h', 'mm/slub.c', 'mm/page_alloc.c', 'mm/util.c',
                      'net/core/skbuff.c', 'include/linux/skbuff.h', 'fs/dcache.c', 'fs/inode.c')
ALLOC_HELPER_FUNCTIONS = ('skb_checksum_help',)
# Classes (section 3): 'atomic' (a): a GFP_ATOMIC failure is an ordinary
# output in any context, steerable [USER A1]. 'task' (b-task): steerable only
# under the declared failslab-style extension [USER 2026-10-06, A2], i.e. for
# a trace that declares "domain_extension": "failslab" (the NULL is in the
# allocator's output set via the OOM-victim path; the forced trace is not a
# possible Linux execution). 'kworker' (b-kworker, noise.c:100): record-only,
# never steered (Q2).
ENABLED_CLASSES = frozenset({'atomic'})
EXTENSION_CLASSES = {'failslab': frozenset({'task'})}


def enabled_classes(trace):
    """The classes a trace may force failures in: (a) always, (b-task)
    under the declared extension."""
    return ENABLED_CLASSES | EXTENSION_CLASSES.get(trace.get('domain_extension'), frozenset())
# The site table (sections 2, 5.5): label -> consumer frame, class, the
# helper it calls (None: a direct site), and the encounters per
# consultation: an int for an exact site, ('lax', n) for a lax site whose
# count A0 fixed at n (section 16.2.3), ('lax', None) for a lax site with no
# fixed count. `nofail`: the allocation carries __GFP_NOFAIL (none does; A0
# saw no such mask). `kvmalloc_limit`: a fail entry is refused for traces
# whose rlimit allows an array above PAGE_SIZE (the 8 KiB fd array, whose
# slab failure is followed by a successful vmalloc; section 6.2, M7).
ALLOC_SITES = {
    'sendBufSkb': dict(consumer='drivers/net/wireguard/socket.c:192', cls='atomic', helper='__alloc_skb', count=2),
    'replySkb': dict(consumer='drivers/net/wireguard/socket.c:217', cls='atomic', helper='__alloc_skb', count=2),
    # also in task context (wg_up's and wg_set's staged keepalive, A0): the
    # class follows GFP_ATOMIC, not the context
    'keepaliveSkb': dict(consumer='drivers/net/wireguard/send.c:226', cls='atomic', helper='__alloc_skb', count=2),
    'skbCowHead': dict(consumer='drivers/net/wireguard/send.c:183', cls='atomic', helper='skb_cow_data', count=('lax', 0)),
    'skbChecksumHelp': dict(consumer='drivers/net/wireguard/send.c:188', cls='atomic', helper='skb_cow_data',
                            count=('lax', 0)),
    'skbCowDataTx': dict(consumer='drivers/net/wireguard/send.c:192', cls='atomic', helper='skb_cow_data', count=('lax', 0)),
    'skbCowDataRx': dict(consumer='drivers/net/wireguard/receive.c:268', cls='atomic', helper='skb_cow_data',
                         count=('lax', 0)),
    'kmallocEventfdCtx': dict(consumer='fs/eventfd.c:393', cls='task', helper=None, count=1),
    'filpAlloc': dict(consumer='fs/file_table.c:232', cls='task', helper=None, count=1),
    'dAllocPseudo': dict(consumer='fs/file_table.c:374', cls='task', helper='d_alloc_pseudo', count=1),
    'kmallocFdtable': dict(consumer='fs/file.c:147', cls='task', helper=None, count=1),
    'kvmallocFdArray': dict(consumer='fs/file.c:151', cls='task', helper='__kvmalloc_node_noprof', count=1,
                            kvmalloc_limit=512),
    'kvmallocFdBitmaps': dict(consumer='fs/file.c:156', cls='task', helper='__kvmalloc_node_noprof', count=1),
    'kmemCacheZallocPeer': dict(consumer='drivers/net/wireguard/peer.c:33', cls='task', helper=None, count=1),
    'allocNode190': dict(consumer='drivers/net/wireguard/allowedips.c:190', cls='task', helper=None, count=1),
    'allocNode205': dict(consumer='drivers/net/wireguard/allowedips.c:205', cls='task', helper=None, count=1),
    'allocNode234': dict(consumer='drivers/net/wireguard/allowedips.c:234', cls='task', helper=None, count=1),
    'kzallocKeypair': dict(consumer='drivers/net/wireguard/noise.c:100', cls='kworker', helper=None, count=1),
    # pipes (A section 19.6; D3+A integration): direct calls, task context
    # (pipe.c:882 and :1271 are deferred: Leanux/Kernel/Defs.lean AllocSite)
    'kzallocPipeInfo': dict(consumer='fs/pipe.c:798', cls='task', helper=None, count=1),
    'kcallocPipeBufs': dict(consumer='fs/pipe.c:815', cls='task', helper=None, count=1),
    'allocPipePage': dict(consumer='fs/pipe.c:513', cls='task', helper=None, count=1),
}
ALLOC_KIND = 305
ALLOC_FAIL = '00' * 8      # a fail entry's value: word 0 with outcome 0
STEER_CHAIN = 1


def alloc_consumer(chain_frames):
    """The consumer frame of an allocation: the first frame, over the
    record's address and its unwound return addresses (each with its inline
    chain, innermost first), outside the choice and allocation helpers."""
    for frames in chain_frames:
        for function, source in frames:
            if source.split(':')[0] not in ALLOC_HELPER_FILES + CHOICE_HELPERS \
                    and function not in ALLOC_HELPER_FUNCTIONS:
                return source
    return None


def alloc_call_sites(vmlinux, cache_dir):
    """{(target, consumer "file:line"): {'ips': [...], 'functions': [...]}}
    for every call to an allocator entry (target 'direct') or an allocation
    helper (target: its name), and ('tail_jumps', '') for functions that
    tail-jump to one; with `functions`: {name: [start, end)} for the helper
    ranges."""
    digest = hashlib.sha256(Path(vmlinux).read_bytes()).hexdigest()
    cache = Path(cache_dir) / f'alloc-sites-v1-{digest}.json'
    if cache.exists():
        data = json.loads(cache.read_text())
        return {(k, c): v for k, c, v in data['sites']}, {k: tuple(v) for k, v in data['ranges'].items()}
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', str(vmlinux)], capture_output=True, text=True,
                         check=True).stdout.splitlines()
    targets = set(ALLOC_ENTRIES) | set(ALLOC_HELPER_RANGES)
    calls, tail_jumps = [], []
    for current, following in zip(out, out[1:]):
        m = re.search(r'\t(call|jmp)\s+[0-9a-f]+ <([A-Za-z0-9_.]+)>$', current)
        if not m or m.group(2) not in targets:
            continue
        nxt = re.match(r'\s*([0-9a-f]+):', following)
        if m.group(1) == 'jmp':
            tail_jumps.append(int(current.strip().split(':')[0], 16))
        elif nxt:
            calls.append(('direct' if m.group(2) in ALLOC_ENTRIES else m.group(2), int(nxt.group(1), 16)))
    chains = symbolize(vmlinux, [ip - 1 for _, ip in calls] + tail_jumps)
    sites = {}
    for (target, ip), chain in zip(calls, chains):
        consumer = alloc_consumer([chain])
        if consumer:
            entry = sites.setdefault((target, consumer), {'ips': [], 'functions': []})
            entry['ips'].append(ip)
            entry['functions'] = sorted(set(entry['functions']) | {chain[-1][0]})
    sites[('tail_jumps', '')] = sorted({chain[-1][0] for chain in chains[len(calls):]})
    wanted = {f for fs in ALLOC_HELPER_RANGES.values() for f in fs}
    ranges = {}
    for line in subprocess.run(['nm', '-S', '--defined-only', str(vmlinux)], capture_output=True, text=True,
                               check=True).stdout.splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[3] in wanted and parts[2] in 'tT':
            if parts[3] in ranges:
                raise SteeringError(f'helper {parts[3]} is not one symbol')
            start = int(parts[0], 16)
            ranges[parts[3]] = (start, start + int(parts[1], 16))
    if set(ranges) != wanted:
        raise SteeringError(f'helper ranges missing: {sorted(wanted - set(ranges))}')
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps({'sites': [[k, c, v] for (k, c), v in sorted(sites.items(), key=str)],
                                 'ranges': ranges}))
    return sites, ranges


def alloc_refusal(trace, label, value):
    """Why the host refuses this allocation entry (section 5.5), or None."""
    row = ALLOC_SITES[label]
    count = row['count']
    if type(count) is tuple:
        if count[1] is None:
            return f'{label} is lax and A0 fixed no count'
        if count[1] == 0:
            return f'{label}: A0 fixed its count at 0, so no encounter exists to steer'
    if value == 'draw':
        return None
    if value != ALLOC_FAIL:
        return f'{label}: an allocation entry is "draw" or fail ({ALLOC_FAIL})'
    # Intrinsic refusals (a fail is never a possible/clean outcome here),
    # checked before the class policy gate so the honest reason surfaces.
    if row.get('nofail'):
        return f'{label}: a __GFP_NOFAIL allocation is never failed'
    if 'kvmalloc_limit' in row and trace.get('rlimit_nofile', 32) > row['kvmalloc_limit']:
        return f'{label}: the array can exceed PAGE_SIZE (vmalloc fallback), never failed'
    if row['cls'] not in enabled_classes(trace):
        return f'{label}: class {row["cls"]} is not enabled for steering' + \
            (' (a task-context failure needs "domain_extension": "failslab")' if row['cls'] == 'task' else '')
    return None


def alloc_entry(label, value, alloc_sites):
    """The kernel entry for an allocation site: (305, 8, draw, ips, hex,
    flags). A direct site names the consumer's calls into the allocator
    entries (the record's own address); a helper site names its calls into
    the helper, found among the unwound return addresses (chain match)."""
    row = ALLOC_SITES[label]
    sites, _ = alloc_sites
    found = sites.get(('direct' if row['helper'] is None else row['helper'], row['consumer']))
    if found is None or not 1 <= len(found['ips']) <= 4:
        raise SteeringError(f'allocation site {label} resolves to {found}')
    if set(found['functions']) & set(sites.get(('tail_jumps', ''), [])):
        raise SteeringError(f'allocation site {label} is in a function that tail-jumps to an allocator')
    draw = value == 'draw'
    return (ALLOC_KIND, 8, draw, found['ips'], '' if draw else ALLOC_FAIL, 0 if row['helper'] is None else STEER_CHAIN)


def alloc_ranges(labels, alloc_sites):
    """The armed allocation set for these sites (KCOV_LEANUX_ALLOC_LOAD):
    a direct site's return addresses as [ip, ip + 1), a helper site's
    helper ranges; sorted and merged, at most 64."""
    sites, ranges = alloc_sites
    out = []
    for label in sorted(set(labels)):
        row = ALLOC_SITES[label]
        if row['helper'] is None:
            out += [(ip, ip + 1) for ip in alloc_entry(label, 'draw', alloc_sites)[3]]
        else:
            out += [ranges[f] for f in ALLOC_HELPER_RANGES[row['helper']]]
    merged = []
    for lo, hi in sorted(set(out)):
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    if len(merged) > 64:
        raise SteeringError('more than 64 allocation ranges')
    return merged


def site_ranges(label, alloc_sites):
    """The ranges whose allocations are this site's candidates."""
    sites, ranges = alloc_sites
    row = ALLOC_SITES[label]
    if row['helper'] is None:
        return [(ip, ip + 1) for ip in alloc_entry(label, 'draw', alloc_sites)[3]]
    return [ranges[f] for f in ALLOC_HELPER_RANGES[row['helper']]]


def alloc_armed_labels(armed, alloc_sites):
    """The exact sites whose records an armed run carries (the mirror
    consumes their outcomes, `World.allocArmed`): every site whose ranges all
    lie in the armed set `armed` (alloc_ranges' result). An exact site with
    only some of its ranges armed would record some encounters and not
    others; it is refused. Lax sites are not listed: their count is fixed
    (at 0, A0) and the mirror consumes none of their records."""
    def inside(r):
        return any(lo <= r[0] and r[1] <= hi for lo, hi in armed)

    def touches(r):
        return any(r[0] < hi and lo < r[1] for lo, hi in armed)
    out = []
    for label, row in sorted(ALLOC_SITES.items()):
        if type(row['count']) is not int:
            continue
        rs = site_ranges(label, alloc_sites)
        if all(inside(r) for r in rs):
            out.append(label)
        elif any(touches(r) for r in rs):
            raise SteeringError(f'allocation site {label} is only partly armed')
    return out
