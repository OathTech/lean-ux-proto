# One-event removal probe

Baseline: `c63423ef`; fresh-eyes review finding 4. In a temporary copy of the
peer getter, remove exactly one emission site: the successful
`Peers.getPeerPrefix` branch's `h ++ [.read pid p.internalId]` becomes `h`.
The underlying `getPeer` call, its result and its failure branch are unchanged.
This deletes the read at every successful invocation of that one getter site.

The experiment copies the getter, its exact source equation and its erasure
proof from `Leanux/Proofs/WG/Peers/Access.lean` into a temporary module. It does
not mutate the tracked observer, run a mutated whole proof tree, or edit the
mirror. No resource options are needed for these declarations.

| Check | Result |
| --- | --- |
| Unchanged copied getter, `getPeerPrefix_run`, `getPeerPrefix_erases` | PASS, exit 0, no warnings |
| Same declarations after deleting the read emission | FAIL, exit 1, precisely at `getPeerPrefix_run`: its successful branch still promises the appended read |
| Mutated getter with unchanged erasure proof and a proof that a safe input history stays safe | PASS, exit 0, no warnings; only `propext`, `Classical.choice`, `Quot.sound` |

The lost connection is **successful original peer access → corresponding
ordered read observation**. Erasure still connects results and states. History
safety still constrains the remaining events. Neither alone establishes that
all concrete accesses have been observed. The source equation detects this
specific deletion while it is kept unchanged; if the coverage statement were
also weakened, the kernel would not independently recognize the missing
security event. This is evidence for retaining explicit coverage equations and
reviewing their source correspondence, not a universal mutation-coverage claim.

From a clone, with the declared toolchain:

```sh
lake build Leanux.Proofs.WG.Peers.Access
python3 docs/probe-observer-removal.py
```

On the shared box run both commands through `capped -- scripts/in-bundle`.
The script prints the expected red source-equation result and fails noisily if
the baseline, expected rejection or surviving claims do not behave as above.
Its temporary copies are deleted on exit. This is a one-off reproduction
recipe, not an added gate or mutation framework.
