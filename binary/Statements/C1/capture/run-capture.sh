#!/bin/sh
# C1 phase A: record, capture, analyse and check the insertions of the traces
# named in ../../../../docs/2026-11-10-c1-final-statement.md. From the worktree
# root, after `lake -d binary build`, with the saved s5 image available
# (LEANUX_BINARY_KERNEL_DIR, default .artifacts/kernel-net-choice-s5 in the
# main checkout) and a host Python with pyelftools:
#
#   binary/Statements/C1/capture/run-capture.sh            # all five traces
#   binary/Statements/C1/capture/run-capture.sh wireguard:b1_trie_routing
#
# Outputs go to .artifacts/check/c1-<trace> (the recording) and
# .tmp/c1/capture-<trace> (capture.json, analysis.json, lean-check.jsonl);
# they are ignored and not committed. About ten minutes in all, most of it
# the recordings and the verbatim readiness check on the 32 MiB buffer.
#
# The grid trace is not part of the corpus: it is copied into
# corpus/wireguard for its recording and removed again.
set -eu
root=$(cd "$(dirname "$0")/../../../.." && pwd)
here="$root/binary/Statements/C1/capture"
python="${binary_python:-/usr/bin/python3}"
cap() { if command -v capped >/dev/null 2>&1; then capped -- "$@"; else "$@"; fi; }
cd "$root"
traces="${*:-wireguard:c1_capture_grid alloc:a2_allowedips_root_nomem alloc:a2_allowedips_newnode_nomem alloc:a2_allowedips_split_nomem wireguard:b1_trie_routing}"
leanpath="$(cd binary && ../scripts/in-bundle lake env printenv LEAN_PATH)"
for item in $traces; do
  suite=${item%%:*}; trace=${item##*:}
  check="$root/.artifacts/check/c1-$trace"; out="$root/.tmp/c1/capture-$trace"
  if [ ! -e "$check/report.json" ]; then
    grid="$root/corpus/wireguard/c1_capture_grid.json"
    if [ "$trace" = c1_capture_grid ]; then cp "$here/c1_capture_grid.json" "$grid"; fi
    status=0
    LEANUX_QEMU_SLOTS="${LEANUX_QEMU_SLOTS:-16}" cap scripts/in-bundle "$python" -B - "$suite" "$trace" <<'PY' || status=$?
import subprocess, sys
sys.path.insert(0, 'binary')
from target import ROOT, kernel_environment
suite, trace = sys.argv[1:3]
sys.exit(subprocess.run([str(ROOT / 'scripts/in-bundle'), 'python3', '-B', '-m', 'evaluator.check',
    '--suite', suite, '--no-build', '--binary-coverage', '--binary-profile', 'allowedips-insert',
    '--trace', trace, '--out', str(ROOT / '.artifacts/check' / ('c1-' + trace))],
    cwd=ROOT, env=kernel_environment()).returncode)
PY
    if [ "$trace" = c1_capture_grid ]; then rm -f "$grid"; fi
    [ "$status" = 0 ] || { echo "FAIL: recording $trace" >&2; exit 1; }
  fi
  rm -rf "$out"
  LEANUX_QEMU_SLOTS="${LEANUX_QEMU_SLOTS:-16}" cap scripts/in-bundle "$python" -B "$here/capture_insertions.py" --check "$check" --out "$out"
  cap scripts/in-bundle "$python" -B "$here/analyse.py" "$out"
  (cd binary && cap ../scripts/in-bundle env LEAN_PATH="$leanpath" lean --run Statements/C1/capture/Check.lean \
    "$out/input.json" "$out/lean-input.json") > "$out/lean-check.jsonl"
  if [ "$trace" = c1_capture_grid ]; then
    (cd binary && cap ../scripts/in-bundle env LEAN_PATH="$leanpath" lean --run Statements/C1/capture/Check.lean \
      "$out/input.json" "$out/lean-input.json" "$out/coverage-call0.bin") > "$out/lean-full-entry.jsonl"
  fi
done
cap scripts/in-bundle "$python" -B "$here/summarise.py" $(for item in $traces; do echo "$root/.tmp/c1/capture-${item##*:}"; done)
