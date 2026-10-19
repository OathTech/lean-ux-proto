#!/usr/bin/python3
"""For each conditional jump of the listed fib_trie.c functions: its source line and, per arm,
the first KCOV point reached (its line, checker convention) and whether every block on the
way has a single predecessor (an exclusive witness) or is a join."""
import re, subprocess, sys, json
from collections import defaultdict
vm = '/home/dev/projects/lean-ux-proto/.artifacts/kernel-net-choice-s4/vmlinux'
fns = sys.argv[1:]
symbols = set(subprocess.run(['nm', vm], capture_output=True, text=True).stdout.split())

def disasm(sym):
    out = subprocess.run(['objdump', '-d', '--no-show-raw-insn', f'--disassemble={sym}', vm], capture_output=True, text=True).stdout
    ins = []
    for line in out.splitlines():
        m = re.match(r'^ *([0-9a-f]+):\t(.*)$', line)
        if m:
            ins.append((int(m.group(1), 16), m.group(2).strip()))
    return ins

def a2l(addrs):
    q = ''.join(hex(a) + '\n' for a in addrs).encode()
    out = subprocess.run(['addr2line', '-e', vm, '-a', '-i', '-f'], input=q, capture_output=True).stdout.decode().splitlines()
    res, cur, i = {}, None, 0
    while i < len(out):
        if out[i].startswith('0x'):
            cur = int(out[i], 16); res[cur] = []; i += 1
        else:
            res[cur].append((out[i], out[i+1].split('/.deps/linux/')[-1].split(' ')[0])); i += 2
    return res

for fn in fns:
    names = [fn] + sorted(n for n in symbols if n.startswith(fn + '.'))
    ins = []
    for n in names: ins += disasm(n)
    addrs = [a for a, _ in ins]
    idx = {a: k for k, a in enumerate(addrs)}
    nxt = {addrs[k]: addrs[k+1] for k in range(len(addrs)-1)}
    def target(t):
        m = re.search(r'\b([0-9a-f]+) <', t)
        return int(m.group(1), 16) if m else None
    is_point = {}
    for a, t in ins:
        is_point[a] = t.startswith('call') and '<__sanitizer_cov_trace_pc>' in t
    # leaders
    leaders = {addrs[0]} if addrs else set()
    for a, t in ins:
        if t.startswith('j') or t.startswith('ret'):
            tg = target(t) if t.startswith('j') else None
            if tg is not None and tg in idx: leaders.add(tg)
            if a in nxt: leaders.add(nxt[a])
    block_of = {}
    cur = None
    for a, t in ins:
        if a in leaders: cur = a
        block_of[a] = cur
    preds = defaultdict(set)
    for a, t in ins:
        if t.startswith('jmp'):
            tg = target(t)
            if tg in idx: preds[block_of[tg]].add(block_of[a])
        elif t.startswith('j'):
            tg = target(t)
            if tg in idx: preds[block_of[tg]].add(block_of[a])
            if a in nxt: preds[block_of[nxt[a]]].add(block_of[a])
        elif t.startswith('ret'):
            pass
        else:
            if a in nxt and nxt[a] in leaders: preds[block_of[nxt[a]]].add(block_of[a])
    # lines of jumps (instruction address) and of points (return address - 1)
    jumps = [a for a, t in ins if t.startswith('j') and not t.startswith('jmp')]
    points = [a for a in addrs if is_point[a]]
    loc = a2l(jumps + [nxt[p] - 1 for p in points if p in nxt])
    def outer(frames): return frames[-1][1] if frames else '?'
    def line_of_point(p): return outer(loc.get(nxt[p] - 1, []))
    def follow(start):
        """first point from start along fallthrough/jmp; exclusivity along the way"""
        a, excl, steps, seen = start, True, 0, set()
        first = True
        while a is not None and a not in seen and steps < 400:
            seen.add(a); steps += 1
            if a in leaders and not first:
                if len(preds[a]) > 1: excl = False
            if first:
                if len(preds[block_of[a]]) > 1: excl = False
                first = False
            t = dict(ins)[a]
            if is_point[a]:
                return line_of_point(a), excl, a
            if t.startswith('jmp'):
                a = target(t)
                if a not in idx: return None, excl, None
                first = True
                continue
            if t.startswith('j') or t.startswith('ret'):
                return None, excl, None
            a = nxt.get(a)
        return None, excl, None
    print(f'== {fn} {names}')
    for j in jumps:
        t = dict(ins)[j]
        tg = target(t)
        l = outer(loc.get(j, []))
        chain = ' <- '.join(f'{f}@{s}' for f, s in loc.get(j, [])) if len(loc.get(j, [])) > 1 else ''
        ft = follow(nxt.get(j)); tk = follow(tg) if tg in idx else (None, True, None)
        def fmt(r): return f"{r[0]}{'' if r[1] else '(join)'}" if r[0] else 'none'
        print(f'  {l:34s} {t.split()[0]:4s} @{j:x}  fall→{fmt(ft):28s} taken→{fmt(tk)}   {chain}')
