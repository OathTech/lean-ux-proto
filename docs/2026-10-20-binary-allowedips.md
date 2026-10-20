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

F1 remains open pending the mirror correction/target decision requested from the
user. No non-wrapping precondition or modulo target has been introduced. The
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
