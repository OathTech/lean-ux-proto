"""Pipes stage-1 mutants (docs/2026-10-05-p-pipes.md section 8).

Each mutant is applied to a clean committed tree, verified as applied, checked
on the `pipes` suite (the handwritten corpus, corpus/pipes), then reverted.
Run from the repository root:

    scripts/in-bundle python3 scripts/pipes-mutants.py [NAME ...]

Every mutant must be rejected (status fail) by the instrument named in its
description. Entries without patterns belong to code not yet on this branch
(stream P2's fs/pipe.c and kernel/signal.c mirror): they are reported as
pending and their patterns are filled at integration, against the merged
code. P-NC is the negative control of section 8: `current_time` undeclared,
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
  # stream P2 (fs/pipe.c, kernel/signal.c): patterns filled at integration
  ('P-M1-ring-unmasked', 'bufs[tail] for bufs[tail & mask]: invariant (bounds) or A1 on p_wrap', PIPE, None, None),
  ('P-M2-merge-strict', 'offset + chars < PAGE_SIZE at :480: A1 and A2 on p_merge_vs_slot', PIPE, None, None),
  ('P-M3-partial-merge', 'fills the last page and continues: A1 (atomicity), A3 (:480 operands)', PIPE, None, None),
  ('P-M5-release-both', 'pipe_release decrements readers and writers: A1 on p_eof/p_epipe', PIPE, None, None),
  ('P-M6-packet-ignored', 'no truncation at :338-341: A1 digest on p_packet', PIPE, None, None),
  ('P-M7-tmp-page-ignored', 'always alloc_page: A2 (:512-518 witnesses)', PIPE, None, None),
  ('P-M8-epipe-no-signal', '-EPIPE without send_sig: A1 (sigpipe) on p_epipe', PIPE, None, None),
  ('P-M9-resize-copy-order', 'tsize/h swapped at :1300-1304: A1 digest on p_resize_wrapped_copy', PIPE, None, None),
  ('P-M10-nr-accounted-stale', ':1321 dropped: A3 (pipe_bufs operand at :775)', PIPE, None, None),
  ('P-M11-no-legacy-queue', 'a second sigqueue per -EPIPE: A2 (kernel/signal.c:1094-1095)', SIGNAL, None, None),
  ('P-M14-packetized-reader', 'is_packetized tests the reader: A1 on p_packet_setfl', PIPE, None, None),
  ('P-M15-partial-eagain', 'ret = -EAGAIN unconditionally at :560: A1 on p_overfill_single', PIPE, None, None),
  ('P-M16-round-unrounded', 'roundup_pow_of_two dropped at :1256: A1 on p_resize (4097 -> 8192)', PIPE, None, None),
  ('P-M17-ebusy-off-by-one', 'nr_slots <= n at :1282: A1 on p_resize_ebusy', PIPE, None, None),
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


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, **kw)


def main():
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == '', 'tree must be clean'
    head = run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    names = [m[0] for m in MUTANTS]
    selected = sys.argv[1:] or names
    unknown = sorted(set(selected) - set(names))
    if unknown:
        raise SystemExit(f'unknown mutants: {unknown}')
    results = {}
    for name, what, path, old, new in MUTANTS:
        if name not in selected:
            continue
        if name in PENDING:   # stream P2's code: the pattern is filled at integration
            results[name] = dict(description=what, base=head, file=path, status='pending')
            print(name, 'pending (no pattern yet)', flush=True)
            continue
        full = os.path.join(ROOT, path)
        text = open(full).read()
        assert text.count(old) == 1, f'{name}: pattern not unique/present'
        open(full, 'w').write(text.replace(old, new))
        try:
            diff = run(['git', 'diff', '--stat'], capture_output=True, text=True).stdout
            assert path in diff, f'{name}: mutation not applied'
            out = f'.artifacts/check/mutant-{name}'
            run(['rm', '-rf', out])
            proc = run(['timeout', '3000', sys.executable, '-m', 'evaluator.check', '--suite', 'pipes', '--out', out],
                       capture_output=True, text=True)
            report_path = os.path.join(ROOT, out, 'report.json')
            if not os.path.exists(report_path):
                results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status='error',
                                     stderr=proc.stderr[-2000:])
                print(name, 'error (no report)', proc.stderr[-400:], flush=True)
                continue
            report = json.load(open(report_path))
            kinds = sorted({p['problem'] for f in report['failures'] for p in f.get('problems', [])} |
                           {f['outcome'] for f in report['failures']})
            results[name] = dict(description=what, base=head, file=path, exit=proc.returncode, status=report['status'],
                                 counts=report['counts'], failure_kinds=kinds, aborted=report['aborted'],
                                 report=out + '/report.json')
            print(name, results[name]['status'], report['counts'], kinds, flush=True)
        finally:
            run(['git', 'checkout', '--', path])
    assert run(['git', 'status', '--porcelain'], capture_output=True, text=True).stdout == ''
    os.makedirs(os.path.join(ROOT, '.artifacts/check'), exist_ok=True)
    json.dump(results, open(os.path.join(ROOT, '.artifacts/check/pipes-mutants-summary.json'), 'w'), indent=2)


if __name__ == '__main__':
    main()
