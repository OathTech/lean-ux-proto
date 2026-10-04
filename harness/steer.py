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
                  'include/linux/timekeeping.h', 'include/crypto/curve25519.h', 'include/linux/hrtimer.h')
# Sites a trace may steer, and their domains (strategy section 3): every
# value in the domain is a possible output of the source.
STEERABLE = {'init_ephemeral', 'resp_ephemeral', 'index_draw', 'tai64n_now'}
TIME_SETTOD_SEC_MAX = (1 << 63) // 1_000_000_000 - 30 * 365 * 24 * 3600   # KTIME_SEC_MAX - TIME_UPTIME_SEC_MAX


class SteeringError(ValueError):
    pass


def call_sites(vmlinux, cache_dir):
    """{(kind, consumer "file:line"): [return addresses]} for every call to a
    hooked entry point in the image."""
    digest = hashlib.sha256(Path(vmlinux).read_bytes()).hexdigest()
    cache = Path(cache_dir) / f'steer-sites-{digest}.json'
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
            tail_jumps.append(current.strip())
        elif nxt:
            calls.append((HOOKS[m.group(2)], int(nxt.group(1), 16)))
    query = ''.join(hex(ip - 1) + '\n' for _, ip in calls).encode()
    lines = subprocess.run(['addr2line', '-e', str(vmlinux), '-a', '-i'], input=query, capture_output=True,
                           check=True).stdout.decode().splitlines()
    chains, k = [], -1
    for line in lines:
        if line.startswith('0x'):
            chains.append([])
        else:
            chains[-1].append(line.split('/.deps/linux/')[-1].split(' ')[0])
    if len(chains) != len(calls):
        raise SteeringError('malformed addr2line output')
    sites = {}
    for (kind, ip), chain in zip(calls, chains):
        consumer = next((src for src in chain if src.split(':')[0] not in CHOICE_HELPERS), None)
        if consumer:
            sites.setdefault((kind, consumer), []).append(ip)
    # A tail jump into a hook hides its consumer's frame from _RET_IP_: such
    # records are attributed to the caller's caller. They are listed with the
    # cache; resolve() refuses a site whose function tail-jumps to a hook.
    sites[('tail_jumps', '')] = tail_jumps
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(json.dumps([[k, c, v] for (k, c), v in sorted(sites.items(), key=str)]))
    return sites


def resolve(trace, site_table, sites):
    """The trace's schedule for the kernel: [(kind, length, draw, ips, hex)].
    `site_table`: the mirror's sites by label (leanux-model --hidden-sites)."""
    out = []
    for label, value in trace['steer']:
        entry = site_table.get(label)
        if entry is None or label not in STEERABLE:
            raise SteeringError(f'{trace["id"]}: {label!r} is not a steerable site')
        consumer = f"{entry['file']}:{entry['line']}"
        kinds = [(k, ips) for (k, c), ips in sites.items() if k != 'tail_jumps' and c == consumer
                 and (k < 200) == (entry['kind'] == 'random')]
        if len(kinds) != 1 or not 1 <= len(kinds[0][1]) <= 4:
            raise SteeringError(f'{trace["id"]}: site {label} resolves to {kinds}')
        kind, ips = kinds[0]
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
