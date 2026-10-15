#!/usr/bin/env python3
"""Lane C measurement (docs/2026-10-15-design-c-fib-trie.md): the shape of
the fixture's IPv4 FIB trie, from a transcription of fib_trie.c's insert
and resize (Linux 6.12.110: fib_insert_node :1110, resize :848,
should_inflate :804, should_halve :819, should_collapse :833, inflate :537,
halve :633, collapse :688, tnode_new :377, put_child :418). Keys in host
order; `slen` per leaf is max over its aliases (KEYLENGTH - plen).

    python3 scripts/probes/c-fib-shape.py            # the fixture's tables
    python3 scripts/probes/c-fib-shape.py --w4       # plus W4's host route

Prints the trie after each insert and the nodes' (pos, bits) so the
coverage's operand pairs (`pn->pos`, `tn->bits`) can be checked against it.
"""
import sys
KEYLENGTH = 32
INFL, HALVE, INFL_ROOT, HALVE_ROOT = 50, 25, 30, 15
MAX_WORK = 10

class KV:
    def __init__(self, key, pos, bits, slen):
        self.key, self.pos, self.bits, self.slen = key, pos, bits, slen
        self.parent = None
        self.children = [None] * (1 << bits) if bits else None
        self.empty = (1 << bits) if bits and bits != KEYLENGTH else 0
        self.full = 1 if bits == KEYLENGTH else 0
        self.aliases = []
    leaf = property(lambda s: s.bits == 0)
    def __repr__(self):
        return f'leaf {self.key:#010x}/{32 - self.slen if self.aliases else "?"}' if self.leaf else f'tnode key={self.key:#010x} pos={self.pos} bits={self.bits} slen={self.slen}'

ROOT = KV(0, KEYLENGTH, 0, KEYLENGTH); ROOT.children = [None]; ROOT.bits = 0  # IS_TRIE: pos >= KEYLENGTH
def is_trie(n): return n.pos >= KEYLENGTH
def child_length(tn): return (1 << tn.bits) & ~1
def get_index(key, kv):
    if KEYLENGTH == kv.pos: return 0
    return (key ^ kv.key) >> kv.pos
def tnode_full(tn, n): return n is not None and (n.pos + n.bits) == tn.pos and not n.leaf
def tnode_new(key, pos, bits):
    shift = pos + bits
    tn = KV(((key >> shift) << shift) if shift < KEYLENGTH else 0, pos, bits, pos)
    return tn
def put_child(tn, i, n):
    chi = tn.children[i]
    if n is None and chi is not None: tn.empty += 1
    if n is not None and chi is None: tn.empty -= 1
    wasfull, isfull = tnode_full(tn, chi), tnode_full(tn, n)
    if wasfull and not isfull: tn.full -= 1
    elif not wasfull and isfull: tn.full += 1
    if n is not None and tn.slen < n.slen: tn.slen = n.slen
    tn.children[i] = n
def put_child_root(tp, key, n):
    if is_trie(tp): tp.children[0] = n
    else: put_child(tp, get_index(key, tp), n)
def set_parent(n, tp):
    if n is not None: n.parent = tp
def update_children(tn):
    for i in range(child_length(tn) - 1, -1, -1):
        inode = tn.children[i]
        if inode is None: continue
        if inode.parent is tn: update_children(inode)
        else: inode.parent = tn
def replace(old, tn):
    tp = old.parent
    tn.parent = tp
    put_child_root(tp, tn.key, tn)
    update_children(tn)
    for i in range(child_length(tn) - 1, -1, -1):
        inode = tn.children[i]
        if tnode_full(tn, inode): tn = resize(inode)
    return tp
def inflate(old):
    tn = tnode_new(old.key, old.pos - 1, old.bits + 1)
    m = 1 << tn.pos
    for i in range(child_length(old) - 1, -1, -1):
        inode = old.children[i]
        if inode is None: continue
        if not tnode_full(old, inode):
            put_child(tn, get_index(inode.key, tn), inode); continue
        if inode.bits == 1:
            put_child(tn, 2 * i + 1, inode.children[1]); put_child(tn, 2 * i, inode.children[0]); continue
        node1 = tnode_new(inode.key | m, inode.pos, inode.bits - 1)
        node0 = tnode_new(inode.key, inode.pos, inode.bits - 1)
        k = child_length(inode); j = k // 2
        while j:
            k -= 1; j -= 1; put_child(node1, j, inode.children[k]); put_child(node0, j, inode.children[j])
            k -= 1; j -= 1; put_child(node1, j, inode.children[k]); put_child(node0, j, inode.children[j])
        node1.parent = tn; node0.parent = tn
        put_child(tn, 2 * i + 1, node1); put_child(tn, 2 * i, node0)
    return replace(old, tn)
def halve(old):
    tn = tnode_new(old.key, old.pos + 1, old.bits - 1)
    i = child_length(old)
    while i:
        i -= 1; node1 = old.children[i]
        i -= 1; node0 = old.children[i]
        if node1 is None or node0 is None:
            put_child(tn, i // 2, node1 if node1 is not None else node0); continue
        inode = tnode_new(node0.key, old.pos, 1)
        put_child(inode, 1, node1); put_child(inode, 0, node0); inode.parent = tn
        put_child(tn, i // 2, inode)
    return replace(old, tn)
def collapse(old):
    n = None
    for i in range(child_length(old) - 1, -1, -1):
        if old.children[i] is not None: n = old.children[i]; break
    tp = old.parent
    put_child_root(tp, old.key, n); set_parent(n, tp)
    return tp
def should_inflate(tp, tn):
    used = child_length(tn); threshold = used * (INFL_ROOT if is_trie(tp) else INFL)
    used = used - tn.empty + tn.full
    return used > 1 and tn.pos and (50 * used) >= threshold
def should_halve(tp, tn):
    used = child_length(tn); threshold = used * (HALVE_ROOT if is_trie(tp) else HALVE)
    used -= tn.empty
    return used > 1 and tn.bits > 1 and (100 * used) < threshold
def should_collapse(tn):
    used = child_length(tn) - tn.empty
    if tn.bits == KEYLENGTH and tn.full: used -= (1 << 32) - 1
    return used < 2
EVENTS = []
def resize(tn):
    tp = tn.parent; cindex = get_index(tn.key, tp); max_work = MAX_WORK
    while should_inflate(tp, tn) and max_work:
        EVENTS.append(f'inflate pos={tn.pos} bits={tn.bits}->{tn.bits + 1}')
        tp = inflate(tn); max_work -= 1; tn = tp.children[cindex] if not is_trie(tp) else tp.children[0]
    tp = tn.parent
    if max_work != MAX_WORK: return tp
    while should_halve(tp, tn) and max_work:
        EVENTS.append(f'halve pos={tn.pos} bits={tn.bits}->{tn.bits - 1}')
        tp = halve(tn); max_work -= 1; tn = tp.children[cindex] if not is_trie(tp) else tp.children[0]
    if should_collapse(tn):
        EVENTS.append(f'collapse pos={tn.pos}'); return collapse(tn)
    return tn.parent
def push_suffix(tn, slen):
    while tn.slen < slen: tn.slen = slen; tn = tn.parent
def fib_find_node(key):
    pn = n = ROOT; index = 0
    while True:
        pn = n; n = n.children[index] if n.children else None
        if n is None: break
        index = (key ^ n.key) >> n.pos if not is_trie(n) else 0
        if index >= (1 << n.bits): n = None; break
        if n.leaf: break
    return pn, n
def insert(key, plen, label):
    slen = KEYLENGTH - plen
    tp, l = fib_find_node(key)
    if l is not None:
        l.aliases.append((plen, label)); l.aliases.sort()
        if l.slen < slen: l.slen = slen; push_suffix(tp, slen)
        return
    leaf = KV(key, 0, 0, slen); leaf.aliases = [(plen, label)]
    n = tp.children[get_index(key, tp)] if not is_trie(tp) else tp.children[0]
    if n is not None:
        tn = tnode_new(key, (key ^ n.key).bit_length() - 1, 1)
        tn.parent = tp
        put_child(tn, get_index(key, tn) ^ 1, n)
        put_child_root(tp, key, tn); set_parent(n, tn)
        tp = tn
    push_suffix(tp, slen); leaf.parent = tp; put_child_root(tp, key, leaf)
    while not is_trie(tp): tp = resize(tp)
def dump(n=None, depth=0):
    n = ROOT.children[0] if n is None else n
    if n is None: print('  (empty)'); return
    print('  ' * depth + repr(n) + (f' aliases={n.aliases}' if n.leaf else ''))
    if not n.leaf:
        for c in n.children:
            if c is not None: dump(c, depth + 1)
def depth(n=None):
    n = ROOT.children[0] if n is None else n
    return 0 if n is None or n.leaf else 1 + max(depth(c) for c in n.children if c is not None)
SEQ = [  # boot: lo up (devinet.c:1601-1613 -> fib_add_ifaddr :1123-1159), then wg0's address and the default route (route_into_wg0, guest.c:1212-1294)
    (0x7f000001, 32, 'local 127.0.0.1 (lo host route, :1140)'),
    (0x7f000000, 8, 'local 127.0.0.0/8 (lo prefix route, :1150-1153: RTN_LOCAL on loopback)'),
    (0x7fffffff, 32, 'broadcast 127.255.255.255 (:1155-1157)'),
    (0x0afffe01, 32, 'local 10.255.254.1 (wg0 host route; /32 so no prefix or broadcast route)'),
    (0x00000000, 0, 'unicast default via wg0 (main; route_into_wg0)'),
]
if '--w4' in sys.argv:
    SEQ.append((0x0a000002, 32, 'unicast 10.0.0.2/32 via wg0 mtu (W4 routes mode)'))
for key, plen, label in SEQ:
    insert(key, plen, label)
    print(f'after insert {key:#010x}/{plen} ({label}); resize events: {EVENTS or "none"}')
    EVENTS.clear()
    dump()
print('depth (tnodes on the longest path):', depth())
