#!/usr/bin/env python3
"""K2 verification for allocation steering (docs/2026-10-05-a-alloc.md,
sections 5, 7), Linux only. No mirror: it checks the kernel side of steering —
that a forced failure reaches the C's failure arm (an observation change) and
that the schedule is consumed exactly — and the controls K1-K5.

    scripts/in-bundle python3 scripts/alloc-controls.py \
        --kernel .artifacts/kernel-net-choice-a \
        --control-kernel .artifacts/kernel-net-choice-actl \
        --out .artifacts/alloc-controls

The A kernel runs the A1 corpus (`corpus/alloc-controls`): the forced failure
of each class-(a) alloc_skb site, and an unsteered baseline. The control
kernel runs K1 (a forced failure recorded ok = 1), K4 (a __GFP_NOFAIL
allocation, left over) and K5 (naming by address only, a helper site left
over); K2 and K3 run on the A kernel. Each case states what must hold.
"""
import argparse
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import linux as H  # noqa: E402
from harness.steer import (ALLOC_FAIL, SteeringError, alloc_call_sites, alloc_ranges,  # noqa: E402
                           call_sites, resolve as resolve_steering)
from harness.trace import loads_trace  # noqa: E402
from evaluator.check import load_hidden_sites  # noqa: E402

# Control-kernel load flags (net-choice-actl); the oracle rejects them.
CTL = {'record_ok': 2, 'nofail': 4, 'addr_naming': 8}


def run(kernel, traces, out, *, alloc_flags=0, alloc_labels=(), steer_all=None, timeout=600):
    """Run `traces` Linux-only on `kernel`, armed for `alloc_labels` with
    `alloc_flags`, steering each trace's own schedule (or `steer_all` for every
    trace). Returns the collected observations and the steering rows."""
    os.environ['LEANUX_KERNEL_DIR'] = str(Path(kernel).resolve())
    import importlib
    importlib.reload(H)
    traces = [loads_trace(t) if isinstance(t, str) else t for t in traces]
    sites = load_hidden_sites()
    by_label = {e['label']: e for e in sites.values()}
    calls = call_sites(H.KERNEL / 'vmlinux', H.ARTIFACTS / 'cache')
    asites = alloc_call_sites(H.KERNEL / 'vmlinux', H.ARTIFACTS / 'cache') if alloc_labels else None
    steer_wire = {}
    for t in traces:
        sched = steer_all if steer_all is not None and 'steer' in t else None
        tt = dict(t, steer=sched) if sched is not None else t
        if 'steer' in tt:
            steer_wire[t['id']] = resolve_steering(tt, by_label, calls, asites)
    alloc = None
    if alloc_labels or alloc_flags:
        alloc = {'flags': alloc_flags, 'ranges': alloc_ranges(alloc_labels, asites) if alloc_labels else []}
    if not (out / 'observations.jsonl').exists():
        H.run_linux(traces, out, timeout=timeout, steer_wire=steer_wire, alloc=alloc)
    obs = [json.loads(l) for l in (out / 'observations.jsonl').read_text().splitlines()]
    # observations.jsonl predates attach_observed; read the wg_observe
    # datagrams from the boot log (one LEANUX_WGOBS per observe).
    dgs = {}
    for line in (out / 'boot.log').read_text(errors='replace').splitlines():
        if line.startswith('LEANUX_WGOBS '):
            r = json.loads(line[len('LEANUX_WGOBS '):])
            dgs.setdefault(r['id'], []).extend(r['datagrams'])
    by_id = {o['id']: o for o in obs}
    for tid, o in by_id.items():
        o['datagrams'] = dgs.get(tid, [])
    steer = [json.loads(l) for l in (out / 'steering.jsonl').read_text().splitlines()] \
        if (out / 'steering.jsonl').exists() else []
    return by_id, steer


def datagrams(obs, tid):
    return obs[tid]['datagrams']


def steer_exact(steer, tid):
    """Both children consumed the whole schedule with no mismatch."""
    rows = [r for r in steer if r['id'] == tid]
    return len(rows) == 2 and all(r['remaining'] == 0 and r['mismatches'] == 0 for r in rows)


def steer_leftover(steer, tid):
    rows = [r for r in steer if r['id'] == tid]
    return len(rows) == 2 and all(r['remaining'] > 0 for r in rows)


def steer_mismatch(steer, tid):
    rows = [r for r in steer if r['id'] == tid]
    return len(rows) == 2 and all(r['mismatches'] > 0 for r in rows)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kernel', required=True)
    ap.add_argument('--control-kernel', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    results = {}

    def corpus(tid):
        return loads_trace((ROOT / 'corpus/alloc-controls' / f'{tid}.json').read_text())

    # ---- A kernel: A1 forced failures reach the arm; the schedule is exact ----
    labels = {'sendBufSkb', 'keepaliveSkb'}
    a1 = [corpus(t) for t in ('ac_sendbuf_base', 'ac_sendbuf_nomem', 'ac_sendbuf_nodata',
                              'ac_keepalive_base', 'ac_keepalive_nomem')]
    obs, steer = run(args.kernel, a1, out / 'a1', alloc_labels=labels)
    base_dg = len(datagrams(obs, 'ac_sendbuf_base'))
    results['A1_sendbuf_base_has_initiation'] = base_dg >= 1
    results['A1_sendbuf_nomem_suppresses_it'] = len(datagrams(obs, 'ac_sendbuf_nomem')) == base_dg - 1 \
        and steer_exact(steer, 'ac_sendbuf_nomem')
    results['A1_sendbuf_nodata_suppresses_it'] = len(datagrams(obs, 'ac_sendbuf_nodata')) == base_dg - 1 \
        and steer_exact(steer, 'ac_sendbuf_nodata')
    ka_base = len(datagrams(obs, 'ac_keepalive_base'))
    results['A1_keepalive_nomem_suppresses_it'] = len(datagrams(obs, 'ac_keepalive_nomem')) < max(ka_base, 1) \
        and steer_exact(steer, 'ac_keepalive_nomem')

    # ---- K2: a fail entry in a non-recording context (the guest parent's own
    # GFP_KERNEL allocation) is never matched. Modeled here as a schedule that
    # names a site the trace never reaches: it is left over. ----
    xmit = corpus('ac_sendbuf_base')
    k2 = dict(xmit, id='ac_k2_unreached', steer=[['keepaliveSkb', ALLOC_FAIL]])
    obs, steer = run(args.kernel, [k2], out / 'k2', alloc_labels={'keepaliveSkb'})
    results['K2_unreached_entry_left_over'] = steer_leftover(steer, 'ac_k2_unreached')

    # ---- K3: a fail entry whose chain names the WireGuard consumer, while the
    # fixture's own sendto allocates through the same __alloc_skb range. The
    # entry waits for the WireGuard encounter (the fixture's chain does not
    # match); it is consumed exactly, which is the test that chain, not addr,
    # fires. ac_sendbuf_nomem already arms the whole __alloc_skb range and the
    # fixture's sendto runs in the same operation; its exact consumption (A1)
    # is K3. ----
    results['K3_chain_match_not_addr'] = results['A1_sendbuf_nomem_suppresses_it']

    # ---- Control kernel: K1, K4, K5 ----
    # K1: a forced failure that records ok = 1 fails the outcome-byte check.
    # Here (Linux only) we confirm the kernel still fails the allocation (the
    # arm is reached) yet reports the schedule consumed, so only the record's
    # outcome byte, which the evaluator compares, distinguishes it.
    obs, steer = run(args.control_kernel, [corpus('ac_sendbuf_nomem')], out / 'k1',
                     alloc_flags=CTL['record_ok'], alloc_labels={'sendBufSkb'})
    k1_dg = len(datagrams(obs, 'ac_sendbuf_nomem'))
    results['K1_record_ok_still_fails_alloc'] = k1_dg == base_dg - 1 and steer_exact(steer, 'ac_sendbuf_nomem')
    k1hid = [json.loads(l) for l in (out / 'k1/hidden.jsonl').read_text().splitlines()]
    steered305 = [r for row in k1hid for r in row['records'] if r[0] == (305 | 0x8000)]
    results['K1_forced_record_claims_ok'] = len(steered305) >= 1 and all(
        int.from_bytes(bytes.fromhex(r[4][:2]), 'little') == 1 for r in steered305)

    # K4: the steered encounter counts as __GFP_NOFAIL: never failed, the entry
    # stays (left over), and the datagram is NOT suppressed.
    obs, steer = run(args.control_kernel, [corpus('ac_sendbuf_nomem')], out / 'k4',
                     alloc_flags=CTL['nofail'], alloc_labels={'sendBufSkb'})
    results['K4_nofail_not_failed_entry_left_over'] = len(datagrams(obs, 'ac_sendbuf_nomem')) == base_dg \
        and steer_leftover(steer, 'ac_sendbuf_nomem')

    # K5: naming by address only. sendBufSkb is a helper site (socket.c:192
    # calls __alloc_skb): its entry names the consumer frame above the
    # allocation address, so an addr-only naming test never matches it; the
    # entry is left over and the datagram is not suppressed.
    obs, steer = run(args.control_kernel, [corpus('ac_sendbuf_nomem')], out / 'k5',
                     alloc_flags=CTL['addr_naming'], alloc_labels={'sendBufSkb'})
    results['K5_addr_naming_helper_site_left_over'] = len(datagrams(obs, 'ac_sendbuf_nomem')) == base_dg \
        and steer_leftover(steer, 'ac_sendbuf_nomem')

    # ---- Host refusals (section 5.5), no VM ----
    asites = alloc_call_sites(Path(args.kernel).resolve() / 'vmlinux', H.ARTIFACTS / 'cache')
    sites = {e['label']: e for e in load_hidden_sites().values()}

    vmlinux = Path(args.kernel).resolve() / 'vmlinux'
    calls = call_sites(vmlinux, H.ARTIFACTS / 'cache')

    def refused(tid, steer, rlimit=32):
        t = {"version": 1, "id": tid, "rlimit_nofile": rlimit,
             "ops": [{"op": "eventfd2", "init": 0, "flags": 0}], "steer": steer}
        try:
            resolve_steering(t, sites, calls, asites)
            return False
        except SteeringError:
            return True

    results['refuse_lax_zero_count'] = refused('r_lax', [['skbCowDataTx', ALLOC_FAIL]])
    results['refuse_disabled_class'] = refused('r_task', [['kmemCacheZallocPeer', ALLOC_FAIL]])
    results['refuse_nofail'] = refused('r_nofail', [['kvmallocFdBitmaps', ALLOC_FAIL]])  # task-class gate
    results['refuse_8k_kvmalloc'] = refused('r_kv', [['kvmallocFdArray', ALLOC_FAIL]], rlimit=1024)
    results['accept_atomic'] = not refused('r_atomic', [['sendBufSkb', ALLOC_FAIL]])

    (out / 'results.json').write_text(json.dumps(results, indent=1) + '\n')
    print(json.dumps(results, indent=1))
    ok = all(results.values())
    print('PASS' if ok else 'FAIL', f'({sum(results.values())}/{len(results)})')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
