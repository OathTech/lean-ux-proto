"""Pipes stage-1 mutants (docs/2026-10-05-p-pipes.md section 8).

Each mutant is applied to a clean committed tree, verified as applied, checked
on the `pipes` suite (the handwritten corpus, corpus/pipes), then reverted.
Run from the repository root:

    scripts/in-bundle python3 scripts/pipes-mutants.py [NAME ...]

Every mutant must be rejected by the instrument named in its description:
its run must find something the unmutated baseline run (made first, on the
same suite) does not. With a passing baseline that is simply a failing run;
the baseline rule keeps the mutants informative while an open, known failure
(a stream's declared placeholder) is still in the tree. Stream P2's mutants (fs/pipe.c, kernel/signal.c) were written
against P2's code as merged into task/p3; an entry without a pattern is
reported as pending. P-NC is the negative control of section 8: `current_time` undeclared,
so every pipes trace fails with "choice from an undeclared consumer".

P-M4 needs a tick between the creation and the write before the one whose
operands differ (p_ticks pauses 5 ms before it); P-M13 needs a write whose
stamps differ (the same pauses).
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PIPE = 'Leanux/FS/Pipe.lean'
SIGNAL = 'Leanux/Kernel/Signal.lean'
INODE = 'Leanux/FS/Inode.lean'

# (name, what it changes and the instrument expected to reject it, file, old, new)
MUTANTS = [
  # stream P2 (fs/pipe.c, kernel/signal.c): patterns written against P2's
  # code as merged into task/p3 (8f4a437, 70cee6a); re-check at integration
  ('P-M1-ring-unmasked', 'bufs[slot] for bufs[slot & mask]: invariant (bounds) or A1 on p_wrap', PIPE,
   "  return (slot &&& (p.ringSize - 1).toUInt32).toNat\n",
   "  return slot.toNat\n"),
  ('P-M2-merge-strict', 'offset + chars < PAGE_SIZE at :480: A1 and A2 on p_merge_vs_slot', PIPE,
   "        branchCmp .pipeWriteFits (offset + chars <= PAGE_SIZE) (offset + chars) PAGE_SIZE\n",
   "        branchCmp .pipeWriteFits (offset + chars < PAGE_SIZE) (offset + chars) PAGE_SIZE\n"),
  ('P-M3-partial-merge', 'fills the last page and continues: A1 (atomicity), A3 (:480 operands)', PIPE,
   ["        branchCmp .pipeWriteFits (offset + chars <= PAGE_SIZE) (offset + chars) PAGE_SIZE\n",
    "      let (n, src') ← copyPageFromIter page offset chars src\n",
    "      if ← branchCmp .pipeWriteMergeShort (ret < chars) ret chars then return (-EFAULT, wasEmpty)\n"],
   ["        branchCmp .pipeWriteFits (offset < PAGE_SIZE) (offset + chars) PAGE_SIZE\n",
    "      let (n, src') ← copyPageFromIter page offset (min chars (PAGE_SIZE - offset)) src\n",
    "      if ← branchCmp .pipeWriteMergeShort (ret < min chars (PAGE_SIZE - offset)) ret chars then return (-EFAULT, wasEmpty)\n"]),
  ('P-M5-release-both', 'pipe_release decrements readers and writers: A1 on p_eof/p_epipe (or invariant)', PIPE,
   "    setPipe pid { p with readers := p.readers - 1 }\n",
   "    setPipe pid { p with readers := p.readers - 1, writers := p.writers - 1 }\n"),
  ('P-M6-packet-ignored', 'no truncation at :338-341: A1 digest on p_packet', PIPE,
   "        totalLen := chars\n        buf := { buf with len := 0 }\n",
   "        pure ()\n"),
  ('P-M7-tmp-page-ignored', 'always alloc_page: A2 (:512-518 witnesses)', PIPE,
   "      let mut page := p.tmpPage\n",
   "      let mut page : Option PageId := none\n"),
  ('P-M8-epipe-no-signal', '-EPIPE without send_sig: A1 (sigpipe) on p_epipe', PIPE,
   "    _ ← sendSig SIGPIPE 0\n    return (-EPIPE, false)\n",
   "    return (-EPIPE, false)\n"),
  ('P-M9-resize-copy-order', 'the wrapped copy puts the head part first (:1300-1304): A1 digest on '
   'p_resize_wrapped_copy', PIPE,
   "        bufs ← copyPipeBufs bufs p.bufs tsize 0 h\n      bufs ← copyPipeBufs bufs p.bufs 0 t tsize\n",
   "        bufs ← copyPipeBufs bufs p.bufs 0 0 h\n      bufs ← copyPipeBufs bufs p.bufs h t tsize\n"),
  ('P-M10-nr-accounted-stale', ':1321 nr_accounted dropped: A3 (pipe_bufs operand at :775)', PIPE,
   "  setPipe pid { (← getPipe pid) with maxUsage := nrSlots, nrAccounted := nrSlots }\n",
   "  setPipe pid { (← getPipe pid) with maxUsage := nrSlots }\n"),
  ('P-M11-no-legacy-queue', 'legacy_queue never finds SIGPIPE pending (a second sigqueue per -EPIPE): A2 '
   '(kernel/signal.c:1094-1095)', SIGNAL,
   "  if ← branch .sendSignalLegacy (← legacyQueue (← getK).task.pending sig) then return 0\n",
   "  if ← branch .sendSignalLegacy (← legacyQueue 0 sig) then return 0\n"),
  ('P-M14-packetized-reader', 'is_packetized tests the reading file: A1 on p_packet_setfl', PIPE,
   "      let flags := if ← branchCmp .pipeWritePacketized (hasFlag filp.fFlags O_DIRECT)\n"
   "          (filp.fFlags &&& O_DIRECT).toNat 0 then",
   "      let rdFlags := ((← getK).files.toList.filterMap fun (_, g) =>\n"
   "        if g.privateData == some (.pipe pid) && hasFlag g.fMode FMODE_READ then some g.fFlags else none).headD 0\n"
   "      let flags := if ← branchCmp .pipeWritePacketized (hasFlag rdFlags O_DIRECT)\n"
   "          (rdFlags &&& O_DIRECT).toNat 0 then"),
  ('P-M15-partial-eagain', 'ret = -EAGAIN unconditionally at :560: A1 on p_overfill_single', PIPE,
   "      if ← branchCmp .pipeWriteNoRet (ret == 0) ret 0 then ret := -EAGAIN\n",
   "      _ ← branchCmp .pipeWriteNoRet (ret == 0) ret 0\n      ret := -EAGAIN\n"),
  ('P-M16-round-unrounded', 'roundup_pow_of_two dropped at :1256: A1 on p_resize (4097 -> 8192)', PIPE,
   "  return roundupPowOfTwoUL size\n",
   "  return size\n"),
  ('P-M17-ebusy-off-by-one', 'nr_slots <= n at :1282: A1 on p_resize_ebusy', PIPE,
   "  if ← branchCmp .resizeRingBusy (nrSlots < n) nrSlots n then\n",
   "  if ← branchCmp .resizeRingBusy (nrSlots <= n) nrSlots n then\n"),
  # stream P3 (fs/inode.c)
  ('P-M4-mtime-not-stored', "inode_set_mtime_to_ts dropped: A3 (the next write's timespec64_equal operands)", INODE,
   "        setInode id { (← getInode id) with iMtime := now }   -- inode_set_mtime_to_ts\n",
   "        pure ()   -- P-M4: inode_set_mtime_to_ts dropped\n"),
  ('P-M12-noatime-ignored', 'touch_atime despite O_NOATIME: hidden (no record left) on p_noatime', INODE,
   "  if ← branchCmp .fileAccessedNotNoatime (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0 then\n",
   "  if (← branchCmp .fileAccessedNotNoatime (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0) || true then\n"),
  ('P-M13-no-second-clock-read', 'the update reuses a stamp instead of reading the clock again: hidden '
   '(a record was not consumed)', INODE,
   "      let now ← inodeSetCtimeCurrent id\n",
   "      let now ← do   -- P-M13: no second current_time\n"
   "        setInode id { (← getInode id) with iCtime := ino.iMtime }\n"
   "        pure ino.iMtime\n"),
  ('P-NC-undeclared-current-time', 'negative control: current_time is not a declared consumer (every pipes trace '
   'fails with "choice from an undeclared consumer")', 'Leanux/Kernel/Defs.lean',
   '  | .currentTime => ⟨18, "current_time", "clock", "fs/inode.c", 2648, 16, .mirror⟩\n',
   '  | .currentTime => ⟨18, "current_time", "clock", "fs/inode.c", 2649, 16, .mirror⟩\n'),
]
PENDING = {m[0] for m in MUTANTS if m[3] is None}


def mutate(name, text, old, new):
    """Apply one mutant's replacements (a pattern, or a list of patterns),
    each of which must occur exactly once."""
    olds, news = (old, new) if isinstance(old, list) else ([old], [new])
    for o, n in zip(olds, news, strict=True):
        assert text.count(o) == 1, f'{name}: pattern not unique/present: {o!r}'
        text = text.replace(o, n)
    return text


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def check(out):
    """Run the pipes suite into `out`; the report, or None with the stderr tail."""
    run(['rm', '-rf', out])
    proc = run(['timeout', '3000', sys.executable, '-m', 'evaluator.check', '--suite', 'pipes', '--out', out],
               capture_output=True, text=True)
    path = os.path.join(ROOT, out, 'report.json')
    return (json.load(open(path)) if os.path.exists(path) else None), proc


def signatures(report):
    """What a run found, per trace: its outcome and each problem (operation,
    decision label, kind). A mutant is rejected when its run has a signature
    the unmutated baseline does not (with a passing baseline: when it fails)."""
    found = set()
    for f in report['failures']:
        # a chunk-level failure (the Linux run, the mirror run) carries no id
        trace = f.get('id', '?')
        found.add((trace, 'outcome', f['outcome']))
        for p in f.get('problems', []):
            found.add((trace, p.get('index'), p.get('label'), p['problem']))
    if report['aborted']:
        found.add(('*', 'aborted', report['aborted'][:200]))
    return found


def main():
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
    head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    names = [m[0] for m in MUTANTS]
    selected = sys.argv[1:] or names
    unknown = sorted(set(selected) - set(names))
    if unknown:
        raise SystemExit(f'unknown mutants: {unknown}')
    # The baseline: the unmutated tree on the same suite. Its known failures
    # (if any) do not count as rejections.
    baseline, proc = check('.artifacts/check/mutant-baseline')
    if baseline is None:
        raise SystemExit(f'baseline run produced no report: {proc.stderr[-2000:]}')
    base = signatures(baseline)
    results = {'baseline': dict(base=head, status=baseline['status'], counts=baseline['counts'],
                                known=sorted(map(str, base))[:50])}
    print('baseline', baseline['status'], baseline['counts'], len(base), 'signatures', flush=True)
    for name, what, path, old, new in MUTANTS:
        if name not in selected:
            continue
        if name in PENDING:
            results[name] = dict(description=what, base=head, file=path, status='pending')
            print(name, 'pending (no pattern yet)', flush=True)
            continue
        full = os.path.join(ROOT, path)
        mutated = mutate(name, open(full).read(), old, new)   # before opening for writing
        open(full, 'w').write(mutated)
        try:
            diff = run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout
            assert path in diff, f'{name}: mutation not applied'
            out = f'.artifacts/check/mutant-{name}'
            report, proc = check(out)
            if report is None:
                results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status='error',
                                     stderr=proc.stderr[-2000:])
                print(name, 'error (no report)', proc.stderr[-400:], flush=True)
                continue
            new_found = sorted(map(str, signatures(report) - base))
            kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                           {f['outcome'] for f in report['failures']})
            results[name] = dict(description=what, base=head, file=path, exit=proc.returncode,
                                 status='rejected' if new_found else 'survived', check_status=report['status'],
                                 counts=report['counts'], failure_kinds=kinds, aborted=report['aborted'],
                                 beyond_baseline=new_found[:20], report=out + '/report.json')
            print(name, results[name]['status'], report['counts'], new_found[:6], flush=True)
        finally:
            run(['git', 'checkout', '--', path])
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
    os.makedirs(os.path.join(ROOT, '.artifacts/check'), exist_ok=True)
    json.dump(results, open(os.path.join(ROOT, '.artifacts/check/pipes-mutants-summary.json'), 'w'), indent=2)


if __name__ == '__main__':
    main()
