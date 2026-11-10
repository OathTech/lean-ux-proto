#!/bin/sh
# Run the executable rendering of the C1 statement on the saved s5 image.
# From the worktree root, after `lake -d binary build` (the statement modules
# StatementC1Contracts, StatementC1Headline, StatementC1CallbackImage and
# StatementC1Vacuity are roots of the package library) and
# `binary/allowedips_mutation.py` (which checks the ELF identity and writes
# .tmp/allowedips/mutation.json; run it with the host Python, which has
# pyelftools, as binary/README.md says:
# `scripts/in-bundle /usr/bin/python3 -B binary/allowedips_mutation.py`).
# The run is interpreted and takes about 20 minutes.
#
#   binary/Statements/C1/run-tests.sh
#
# Test.lean is not a package root: it has its own `main` and is not built.
set -eu
root=$(cd "$(dirname "$0")/../../.." && pwd)
cap() { if command -v capped >/dev/null 2>&1; then capped -- "$@"; else "$@"; fi; }
cd "$root/binary"
if grep -nE '\b(sorry|theorem|lemma|axiom|admit|native_decide)\b' StatementC1Contracts.lean StatementC1Headline.lean StatementC1CallbackImage.lean StatementC1Vacuity.lean | grep -v 'no theorem, no proof'; then
  echo "FAIL: a statement file contains a proof, an axiom or sorry" >&2; exit 1
fi
leanpath="$(../scripts/in-bundle lake env printenv LEAN_PATH)"
input="${1:-$root/.tmp/allowedips/mutation.json}"
# the three statement findings kept as regression tests (elaboration fails if either regresses)
for regression in TopOfMemory StateWord StackOffPeers; do
  cap ../scripts/in-bundle env LEAN_PATH="$leanpath" lean "Statements/C1/proof/$regression.lean" ||
    { echo "FAIL: Statements/C1/proof/$regression.lean" >&2; exit 1; }
done
cap ../scripts/in-bundle env LEAN_PATH="$leanpath" lean --run Statements/C1/Test.lean "$input"
