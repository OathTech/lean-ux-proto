# Allowed-IPs binary refinement: scaling report

Status: work in progress on `task/binary-allowedips`, based on landed main
`1a69cebb`. Neither checkpoint A nor B is complete. The
[charter](2026-10-20-charter-binary-allowedips.md) defines the target; the
[independent review](2026-10-20-review-binary-allowedips-charter.md) records its
three findings. Work began at 2026-10-20 01:25:17 UTC, including preparation.

## First Rule Zero finding: the allowed-IPs sequence counter

The mirror's `AllowedIps.seq` is a Nat and insertion increments it without
truncation. Linux stores a u64, and the compiled wrappers increment that word.
This is observable state: the dump tests a saved counter against zero and the
current sequence. It cannot silently be reclassified as an unobserved epoch.

The constructed-state reproducer executes both compiled insertion wrappers,
the invalid-prefix path of `add.isra.0`, and the actual coverage/comparison
bodies, to the original ABI return. It supplies a mapped peer and empty list,
an empty table, network-order address storage, stack and coverage resources.
There are no allocator substitutions or calls on this path. This is not a
captured kernel entry or a theorem of entry reachability.

| Entry sequence | Families / CIDRs | Binary result / sequence | Mirror result / sequence |
| --- | --- | --- | --- |
| 1 | IPv4 / 33, IPv6 / 129 | `-EINVAL`, 2 | `-EINVAL`, 2 |
| 2^64 - 1 | IPv4 / 33, IPv6 / 129 | `-EINVAL`, 0 | `-EINVAL`, 2^64 |

Both undefined-value seeds (0 and all ones) produce these results. IPv4 executes
124 instructions and IPv6 127, including the real service bodies. The runner
checks the return PC/stack and callee-save registers. The permanent reproducer
fails with exit 1 for the mismatch; it is not a passing refinement test:

```sh
capped python3 -B binary/allowedips_seq_wrap.py
```

The script verifies the s5 image and clean private Kraken pin, extracts actual
instructions and DWARF offsets, builds `binary-allowedips-seq-wrap`, and runs it.
Its disposable input is `.tmp/allowedips/seq-wrap.json`. After a mirror fix the
same comparator should pass without changing its expected binary result.

F1 remains open pending the mirror correction. [USER 2026-10-20] The
coordinator owns the correction on the mirror lane; this branch continues
independent work and retains the failing witness. No non-wrapping precondition or modulo target has been introduced. The
charter retains exact counter correspondence and independent work continues.

## Review dispositions and preparation

F2 is addressed in the charter with separate live, retired and released
resources; pending forest child pointers survive logical erasure, the
`peer_list`/`rcu` union changes ownership, and only actual release permits reuse.
An explicit serialized event schedule dispatches the actual WireGuard callback
bodies. This design still needs implementation and proof.

F3 is addressed with an operation-specific ABI inventory, explicit accepted-run
limits for dying-peer retries, and a required frame lift from the old lookup
projection to table roots/counter, parent links and ownership lists. That lift
is part of checkpoint A, not an assumption about its successor.

The s5 inventory finds 506 instructions in `add.isra.0`, 26/29 in the insertion
wrappers, 120 in removal-by-peer, 37 in free, 80 in readout and 57 in each lookup
wrapper. The WireGuard-owned `root_remove_peer_lists`, `node_free_rcu` and
`root_free_rcu` bodies have 71, 7 and 58 instructions. These counts describe
work, not completed proof coverage. Register-form BT is an ISA gap on two
insertion paths, to be addressed privately with tests.

Baseline setup and validation pass: private pinned Kraken bootstrap, the
283-job paired-trie/callback executable build, the 130-job model build, and
136 fast-tier unit tests (one skip). No new headline theorem is claimed yet.
The counter mismatch was confirmed during the first ten minutes of work.

Development failures so far: an initial read targeted the already-removed
landing worktree; several guessed source paths did not exist; the first witness
draft missed required World fields and used an invalid Int64 conversion name;
one correction used the wrong working directory; the first binary input omitted
the shared `write_comp_data` tail and correctly failed on its missing PC.
These were repaired before the reported executions. The counter mismatch
remains a semantic failure. No KILLED banner, timeout or sandbox denial occurred.

## Register BT extension

The private Kraken branch now implements the register/register BT forms used by
insertion, at `907830a1fb207e86f7914764717e3995c1f0df2d`, reproducible as patch
0009. Register offsets wrap at the operand width; CF receives the selected bit,
ZF is preserved, and OF/SF/AF/PF are undefined, following
[Intel SDM volume 2A, BT](https://cdrdv2-public.intel.com/812383/253666-sdm-vol-2a.pdf).
Neither operand register changes, including the upper half on a 32-bit operand.
Unsupported 8-bit, memory, immediate and LOCK forms fail closed.

Focused Lean tests cover widths, boundary/wrapped offsets, aliases, register
preservation and all undefined flag choices; parser/printer roundtrips pass.
The native hardware comparison `test_bt.S` passes (1/1). Reproduce in the private
Kraken checkout with the consumer toolchain selected:

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 capped lake build Kraken.X64.BtTests Kraken.X64.PrintATTTests krakenrunner_x64 att2intel
capped python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm/test_bt.S
```

Test development exposed incomplete flag fixtures and missing execution-access
handling in the test traversal, then a missing meta printer import. The ATT
corpus test requires Kraken as its working directory. The native runner also
needed a Bool generator for previously added instruction fields; that test-only
repair is in the patch. These failed builds were repaired before the reported
passes. The full consumer proof rebuild remains due under this new pin.

## First retained-heap execution checkpoint

At roughly 27 minutes from the start, the paired mutation runner passes four
constructed sequences: IPv4 and IPv6, each with undefined-value seeds zero and
all ones. There are 54 insertion calls and 54 subsequent lookup calls. The
measured executable time is 2.573 seconds, excluding extraction and build.
This is runtime progress; neither A nor B has a function-level proof yet.

The cases cover invalid prefixes, empty-root allocation and failure, exact
reassignment, both child slots, covering roots, intermediate roots and children,
all three allocation failure sites, rollback and reuse of the released address.
IPv6 also exercises differing low words. Full reconstruction at every return
checks roots/counter, nodes/packed parents, ordered peer lists, peer counts and
the ghost allocation counter. Lookup runs against the same physical heap.

Generic allocator/free bodies are supplied interface returns, clearly labelled;
they are not claimed as executed. The WireGuard and coverage/comparison bodies
are interpreted. Successful allocation supplies zeroed fresh bytes and advances
the identity counter; rollback free removes the owned bytes and only then makes
the address reusable. Source allocation records use their real 40-byte shape
and site IDs. These are generated cases, not captured entry states.

The runner checks ABI result, stack/callee-save restoration, unchanged preempt
and pending words, and exact stored coverage prefix. Coverage accounting uses
the executable KCOV plan, including the buffer-full path. The initial test
version counted every callback encounter in its diagnostic list; that was
corrected before the measured rerun above. No later call rematerializes the
WireGuard heap. Reproduce:

```sh
capped python3 -B binary/allowedips_mutation.py
```

All 561 insertion instructions now have literal decoded layouts, across 137
small chunks, proved with standard axioms through the extended instruction
monotonicity lemma. These are layout witnesses, not simulated mutation regions.
The initial long-region layout proof exhausted default recursion depth.
Balanced region fetch and chunks of at most eight instructions close it at the
default limits; the checked instruction sequence is unchanged. Regenerate with:

```sh
capped python3 -B binary/generate_allowedips_mutation.py --check
capped lake -d binary build AllowedipsMutationCodeLayout PairAllowedipsState
```

Fast tier passes: 136 unit tests, one skip. The independent s5 recording for
`b1_trie_routing` is running with the new `allowedips-insert` coverage profile;
three-way comparison is still pending. Profile ranges come from ELF symbols,
with source attribution for local symbols; no guest or kernel change is needed.
Additional development failures were record-layout indentation, an image/layout
output-name collision, ambiguous local `lookup` extraction, and a check output
path outside the checker's required `.artifacts` tree. These were corrected.
