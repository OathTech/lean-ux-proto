#!/usr/bin/env python3
"""B3 probe: does kernel/time/timer.c's wheel, fed only the recorded clocks,
predict every WireGuard timer firing a check run recorded, its set at every
idle point and its order?  (docs/2026-10-15-design-b3-timer-wheel.md,
section 5.)

    python3 -I scripts/probes/b3-wheel-replay.py <check out dir> <kernel build dir>

The out dir is a run of `evaluator.check` (its chunk-*/linux/hidden.jsonl and
chunk-*/linux/inputs.jsonl); the kernel dir holds System.map and vmlinux (addr2line resolves
the record sites).  Stdlib only.  The probe replays each trace's coverage-child
records in sequence order:

- kind 311 (the caller's jiffies read) names the arming site, so the timer's
  kind; kind 303 {J_m, expires, timer} places the timer with the wheel's
  arithmetic at clk = J_m (the no-lag case: the base clock is not recorded
  yet; a kind-313 record is what B3 proposes), applying __mod_timer's three
  paths (same expires: nothing; same slot: position kept, old bucket expiry
  kept; else re-enqueued at the head);
- kind 300 (a dispatch section start, {func, unit}) of a wg_expired_*
  callback is a firing of the timer at `unit`; it is judged at that moment
  against the wheel: the earliest pending bucket (level descending, newest
  enqueue first) of the modeled timers, with the operation's kind-310
  end-of-wait read as the pass's clock bound;
- at the kind-310 read, every pending modeled timer with bucket expiry at or
  before the read must have fired: one that has not is reported by
  disposition, never absorbed;
- deletions are not recorded.  The mirror performs them from control flow;
  the probe performs them from the records that mark the same control flow
  exactly, each named at its C site (see DELETION MARKERS below), and
  attributes a clock-record marker to a peer only when one peer can be meant;
  otherwise the timer stays pending and can only produce an "unexplained"
  report, never hide one.

DELETION MARKERS (drivers/net/wireguard, Linux 6.12.110):
- timers.c:194 del_timer(retransmit) in wg_timers_handshake_complete, called
  at receive.c:179 (a response received) and :347 (first data confirms the
  keypair): the kind-205 wall-clock read at timers.c:197, consumer frames
  receive.c:179 / :347;
- timers.c:170 del_timer(send_keepalive) in any_authenticated_packet_sent,
  called at send.c:37 (an initiation sent: the kind-311 read at timers.c:185
  that follows, whose kind-303 names the peer), send.c:100 (a response sent:
  the kind-311 read at timers.c:206 with no kind-205 at receive.c:179 after it
  in the operation, i.e. the responder's session_derived, not the
  initiator's at receive.c:178) and send.c:248 (every run of the transmit
  worker: its section, whose unit is the peer's transmit_packet_work);
- timers.c:178 del_timer(new_handshake) in any_authenticated_packet_received,
  called at receive.c:201 (every valid handshake message: the response
  received, marker as :194; the initiation received, marker as send.c:100)
  and receive.c:353 (every data packet reaching consume_data_done: the
  kind-208 age test at receive.c:253 that precedes it; a packet the counter
  then rejects is a known over-approximation, noted in the output);
- timers.c:51 del_timer(send_keepalive) in the retransmit's give-up: the
  kind-311 read at timers.c:62 inside a wg_expired_retransmit_handshake
  section (absent if the zero-key timer was already pending: then the
  deletion is unmarked and shows up as unexplained);
- wg_timers_stop (device.c:124 at wg_stop; peer.c:106 at peer removal):
  the operations wg_down, wg_delete and wg_netns_close delete every timer;
  a peer removed by wg_set is not modeled (it would show up as unexplained).

Peers: a timer's address identifies its peer; the five timer_lists are
consecutive 40-byte fields (peer.h:53-55), so addr - 40*kind is a per-peer
anchor; a transmit worker's unit is attributed to the nearest anchor within
one struct wg_peer (1520 bytes on this build)."""
import json, sys, glob, os, subprocess
from collections import defaultdict, Counter

OUT, KDIR = sys.argv[1], sys.argv[2]
SYSMAP, VMLINUX = os.path.join(KDIR, 'System.map'), os.path.join(KDIR, 'vmlinux')

# --- kernel/time/timer.c arithmetic (:154-188, :567-620), HZ 250 ---
LVL_CLK_SHIFT, LVL_BITS, LVL_DEPTH = 3, 6, 9
LVL_SIZE = 1 << LVL_BITS; LVL_MASK = LVL_SIZE - 1
M64 = (1 << 64) - 1
def LVL_SHIFT(n): return n * LVL_CLK_SHIFT
def LVL_START(n): return (LVL_SIZE - 1) << ((n - 1) * LVL_CLK_SHIFT)
def LVL_OFFS(n): return n * LVL_SIZE
def s64(x): x &= M64; return x - (1 << 64) if x >> 63 else x
def time_after(a, b): return s64(b - a) < 0
def time_before(a, b): return time_after(b, a)
def time_after_eq(a, b): return s64(a - b) >= 0
def calc_index(expires, lvl):
    e = ((expires >> LVL_SHIFT(lvl)) + 1) & M64
    return LVL_OFFS(lvl) + (e & LVL_MASK), (e << LVL_SHIFT(lvl)) & M64
def calc_wheel_index(expires, clk):
    delta = (expires - clk) & M64
    for lvl in range(1, 8):
        if delta < LVL_START(lvl):
            return calc_index(expires, lvl - 1)
    if LVL_DEPTH > 8 and delta < LVL_START(8):
        return calc_index(expires, 7)
    if s64(delta) < 0:
        return clk & LVL_MASK, clk
    return calc_index(expires, LVL_DEPTH - 1)
def level_of(idx): return idx // LVL_SIZE

# --- symbols and sites ---
syms = {}
for line in open(SYSMAP):
    a, k, n = line.split()[:3]
    if n.startswith('wg_expired_') or n in ('net_rx_action', 'wg_packet_tx_worker', 'wg_packet_handshake_send_worker',
                                              'wg_packet_encrypt_worker', 'wg_packet_decrypt_worker',
                                              'wg_packet_handshake_receive_worker', 'wg_queued_expired_zero_key_material'):
        syms[int(a, 16)] = n
TIMER_FUNCS = {a for a, n in syms.items() if n.startswith('wg_expired_')}
TX_WORKER = {a for a, n in syms.items() if n == 'wg_packet_tx_worker'}
TIMER_KIND = {'timers.c:185': 0, 'timers.c:87': 1, 'timers.c:159': 1, 'timers.c:149': 2,
              'timers.c:62': 3, 'timers.c:206': 3, 'timers.c:216': 4}
KIND_NAME = ['retransmit', 'send_keepalive', 'new_handshake', 'zero_key', 'persistent_keepalive']
PEER_SIZE = 1520

def words(hexs):
    b = bytes.fromhex(hexs)
    return [int.from_bytes(b[i:i+8], 'little') for i in range(0, len(b), 8)]

rows = []
for p in sorted(glob.glob(os.path.join(OUT, 'chunk-*', 'linux', 'hidden.jsonl'))):
    rows += [json.loads(l) for l in open(p)]
per = defaultdict(lambda: defaultdict(list))
for r in rows:
    if r['mode'] != 'pc': continue
    per[r['id']][r['index']] += r['records']
ops_of = {}
for inputs in sorted(glob.glob(os.path.join(OUT, 'chunk-*', 'linux', 'inputs.jsonl'))):
    for l in open(inputs):
        t = json.loads(l)
        if isinstance(t, dict) and 'id' in t and 'ops' in t:
            ops_of[t['id']] = [o['op'] for o in t['ops']]
if not ops_of:
    sys.exit('no chunk-*/linux/inputs.jsonl under the out dir: the operation names are needed for wg_timers_stop')

# resolve the sites of kinds 205, 208, 311 once (addr2line on ip - 1)
ips = sorted({rec[1] for ops in per.values() for recs in ops.values() for rec in recs if (rec[0] & 0x7fff) in (205, 208, 311)})
site = {}
if ips:
    out = subprocess.run(['addr2line', '-e', VMLINUX] + [hex(int(ip, 16) - 1) for ip in ips],
                         capture_output=True, text=True, check=True).stdout.splitlines()
    for ip, loc in zip(ips, out):
        site[ip] = 'drivers/net/wireguard/' + loc.split('drivers/net/wireguard/')[-1].split(' ')[0] if 'drivers/net/wireguard/' in loc else loc
def short(ip):
    s = site.get(ip, '?')
    return s.rsplit('/', 1)[-1]

stats = Counter(); problems = []; dispositions = Counter(); notes = []
key = lambda t: (t['bexp'], -t['lvl'], -t['seq'])

for tid, ops in sorted(per.items()):
    pending = {}      # timer address -> entry
    seq = 0
    anchors = {}      # peer anchor -> True
    def peer_of_timer(addr, kind): return addr - 40 * kind
    def peer_of_unit(u):
        c = [a for a in anchors if abs(u - a) <= PEER_SIZE]
        return min(c, key=lambda a: abs(u - a)) if c else None
    def delete(pred, why, index, peer=None):
        """Delete the pending timers satisfying pred (a deletion the C performs)."""
        for a in [a for a, t in pending.items() if pred(a, t)]:
            dispositions[f'deleted: {why}'] += 1
            pending.pop(a)
    def delete_kind(kind, why, index, peer):
        if peer is None:
            cands = [a for a, t in pending.items() if t['kind'] == kind]
            if len(cands) == 1:
                delete(lambda a, t: a == cands[0], why, index)
            elif cands:
                stats['deletion markers left ambiguous (several peers; timers kept pending)'] += 1
                notes.append((tid, index, 'ambiguous', why, [hex(a) for a in cands]))
        else:
            delete(lambda a, t: t['kind'] == kind and t['peer'] == peer, why, index)
    for index in sorted(ops):
        recs = sorted(ops[index], key=lambda r: r[2])
        opname = ops_of.get(tid, [None] * (index + 1))[index] if tid in ops_of else None
        if opname in ('wg_down', 'wg_delete', 'wg_netns_close'):
            delete(lambda a, t: True, f'wg_timers_stop at {opname}', index)
        jends = [words(r[4])[0] for r in recs if (r[0] & 0x7fff) == 310]
        jend = jends[-1] if jends else None
        stats['end-of-wait reads (kind 310)'] += len(jends)
        has_resp_recv = any((r[0] & 0x7fff) == 205 and short(r[1]) == 'receive.c:179' for r in recs)
        order = []; nfired = 0; op_ok = True; last311 = None; open_timer_section = None
        for kind, ip, s, length, data in recs:
            kind &= 0x7fff
            if kind == 304:
                stats['advances (kind 304)'] += 1
            elif kind == 205:
                where = short(ip)
                if where in ('receive.c:179', 'receive.c:347'):
                    # wg_timers_handshake_complete: del_timer(retransmit) at timers.c:194; at :179 also
                    # any_authenticated_packet_received (receive.c:201): del_timer(new_handshake)
                    delete_kind(0, f'handshake complete (timers.c:194 via {where})', index, None)
                    if where == 'receive.c:179':
                        delete_kind(2, 'response received (receive.c:201, timers.c:178)', index, None)
            elif kind == 208:
                if short(ip) == 'receive.c:253':
                    # a data packet reaching consume_data_done: any_authenticated_packet_received (receive.c:353)
                    delete_kind(2, 'data received (receive.c:353, timers.c:178)', index, None)
            elif kind == 311:
                last311 = short(ip)
            elif kind == 303:
                jm, e, addr = words(data)[:3]
                stats['arms (kind 303)'] += 1
                tk = TIMER_KIND.get(last311)
                if tk is None:
                    problems.append((tid, index, 'an arm record without a preceding kind-311 site', last311)); continue
                peer = peer_of_timer(addr, tk); anchors[peer] = True
                if last311 == 'timers.c:185':
                    delete(lambda a, t: t['kind'] == 1 and t['peer'] == peer, 'initiation sent (send.c:37, timers.c:170)', index)
                elif last311 == 'timers.c:206' and not has_resp_recv:
                    delete(lambda a, t: t['kind'] == 1 and t['peer'] == peer, 'response sent (send.c:100, timers.c:170)', index)
                    delete(lambda a, t: t['kind'] == 2 and t['peer'] == peer, 'initiation received (receive.c:201, timers.c:178)', index)
                elif last311 == 'timers.c:62' and open_timer_section == 'wg_expired_retransmit_handshake':
                    delete(lambda a, t: t['kind'] == 1 and t['peer'] == peer, 'retransmit gave up (timers.c:51)', index)
                clk = jm
                overdue = [t['bexp'] for t in pending.values() if time_after_eq(jm, t['bexp'])]
                if overdue:
                    stats['arms with a modeled timer overdue (clk = min bucket, timer.c:1008-1014)'] += 1
                    clk = min(overdue)
                if addr in pending:
                    old = pending[addr]
                    if old['expires'] == e:
                        stats['re-arm, same expires (__mod_timer :1085-1088, nothing changes)'] += 1; continue
                    idx, bexp = calc_wheel_index(e, clk)
                    if idx == old['idx']:
                        stats['re-arm, same slot (:1123-1130: position and bucket expiry kept)'] += 1
                        old['expires'] = e; continue
                    stats['re-arm, new slot (:1144, :1181: re-enqueued at the head)'] += 1
                idx, bexp = calc_wheel_index(e, clk); seq += 1
                pending[addr] = dict(expires=e, idx=idx, bexp=bexp, seq=seq, lvl=level_of(idx), kind=tk, peer=peer, name=KIND_NAME[tk])
                stats[f'placements at level {level_of(idx)}'] += 1
            elif kind == 300 and length == 16:
                func, unit = words(data)[:2]
                if func in syms:
                    order.append('T' if func in TIMER_FUNCS else ('N' if syms[func] == 'net_rx_action' else 'W'))
                if func in TX_WORKER:
                    p = peer_of_unit(unit)
                    if p is not None:
                        delete(lambda a, t: t['kind'] == 1 and t['peer'] == p, 'transmit worker ran (send.c:248, timers.c:170)', index)
                    else:
                        delete_kind(1, 'transmit worker ran (send.c:248, timers.c:170)', index, None)
                if func in TIMER_FUNCS:
                    open_timer_section = syms[func]
                    nfired += 1; stats['firings (timer sections)'] += 1
                    if jend is None:
                        problems.append((tid, index, 'a timer section in an operation without a kind-310 read', syms[func])); op_ok = False; continue
                    ent = pending.get(unit)
                    if ent is not None and 'due_at' in ent:
                        dispositions['predicted due at a read, fired in a later operation (the deferral, E2)'] += 1
                        notes.append((tid, index, 'deferred', hex(unit), ent['due_at'])); pending.pop(unit); op_ok = False; continue
                    due = sorted([(a, t) for a, t in pending.items() if time_after_eq(jend, t['bexp'])], key=lambda at: key(at[1]))
                    if ent is None:
                        problems.append((tid, index, 'FIRED, but the probe has no pending timer at that address', hex(unit), syms[func])); op_ok = False
                    elif unit not in [a for a, _ in due]:
                        problems.append((tid, index, 'FIRED, but not due by the wheel at this read', dict(timer=hex(unit), name=syms[func], entry=ent, jend=jend))); op_ok = False
                    elif due[0][0] != unit:
                        problems.append((tid, index, 'ORDER differs from the wheel', dict(predicted=[(hex(a), t['name'], t['bexp'], t['lvl'], t['seq']) for a, t in due], observed=(hex(unit), syms[func]), jend=jend))); op_ok = False
                    else:
                        stats['firings the wheel predicts as the next to run'] += 1
                    pending.pop(unit, None)
            elif kind == 301:
                open_timer_section = None
        if jend is not None:
            stats['idle points (operations with a read)'] += 1
            for a, t in pending.items():
                if 'due_at' in t: continue
                if time_after_eq(jend, t['bexp']):
                    t['due_at'] = (index, jend)
                    notes.append((tid, index, 'predicted due at the read, no section in this operation', hex(a), t['name'], t['expires'], t['bexp'], jend))
                elif time_before(t['expires'], jend):
                    stats['between zone: expires < J_end but bucket expiry > J_end, correctly not fired'] += 1
                    notes.append((tid, index, 'between-zone', hex(a), t['name'], t['expires'], t['bexp'], jend))
        if nfired:
            stats['operations with firings'] += 1
            if op_ok: stats['operations with every firing predicted, in order'] += 1
            if nfired > 1:
                stats['operations with several firings'] += 1
                notes.append((tid, index, 'several firings', nfired, ''.join(order)))
        if 'T' in order and 'N' in order:
            pat = ''.join(order); stats['operations with timer and NET_RX sections'] += 1
            if pat.index('N') < pat.index('T'):
                stats['operations where a NET_RX section precedes the first timer section'] += 1
                notes.append((tid, index, 'order pattern', pat))
    # end of trace: every timer still marked due and never fired is a must-fire violation candidate
    for a, t in pending.items():
        if 'due_at' in t:
            dispositions['UNEXPLAINED: predicted due at a read, never fired, no deletion marker'] += 1
            problems.append((tid, t['due_at'][0], 'UNEXPLAINED must-fire: predicted due, never fired', dict(timer=hex(a), name=t['name'], expires=t['expires'], bexp=t['bexp'], read=t['due_at'][1])))
    if anchors: stats['traces with arms'] += 1

print(json.dumps(dict(sorted(stats.items())), indent=1))
print('dispositions of deletions and non-firings:')
print(json.dumps(dict(sorted(dispositions.items())), indent=1))
print('problems', len(problems))
for p in problems: print(json.dumps(p))
print('notes', len(notes))
for n in notes: print(json.dumps(n))
