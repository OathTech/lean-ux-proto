# H5: accepted namespace-pin alias leaves cleanup pending

Status: reproduced against main `3308c49a` and again after the carry to
main `1a69cebb`. This is an environment/fixture acceptance finding. It is runtime
evidence from the original initialized mirror and its exact boundary observer,
not a kernel-reduction theorem, a Linux capture or a kernel finding.

The foreign-creator fixture starts with its namespace pin at descriptor 9.
With the default descriptor limit of 32, run these three operations in
placeholder mode, with no supplied hidden records:

1. Duplicate literal descriptor 9. This returns descriptor 10.
2. Execute `wg_netns_close`.
3. Close the descriptor returned by operation 0.

Both original execution and the boundary observer accept. The observation is:

| Operation | Return | Supplied records | Pending worker indices |
| --- | ---: | --- | --- |
| duplicate pin | 10 | absent | `[]` |
| close fixed namespace holders | 0 | absent | `[]` |
| close retained alias | 0 | absent | `[12]` (`netnsCleanup`) |

This refutes literal pending-worker emptiness for every accepted placeholder
execution. It does not refute finite evaluation or assert unfinished packet
work. The runner's pending-work completion guard applies only when its final
hidden-record field is present; this execution uses the other mode.

Statement/domain check: the Python harness accepts this trace. Its literal
descriptor restriction excludes 0 through 7, not 9. Duplication is a descriptor
producer, and the reference to operation 0 is valid. The foreign fixture requires
exactly one `wg_netns_close`, which is present; there is no later injection.
A two-operation candidate lacking that opcode was discarded because it failed
the harness domain. A limit of 10 would also invalidate this witness by denying
the duplicate; the witness uses the default 32.

The fixture design assumes its fixed pin close drops the last reference. Neither
parser nor harness enforces that assumption. `FS.getFileRef` retains the alias;
`FS.fputFinal` queues cleanup on the actual last pin release. The syscall wrapper
invokes `Env.netnsCleanup` specifically after `wg_netns_close`, without checking
that retained aliases are gone. A later ordinary close can therefore queue a
new cleanup identity without that wrapper. The guest's operations likewise permit
duplication and close, but no guest comparison was run in this proof campaign.

Request to the mirror lane: establish the intended admissible fixture domain
and account for namespace-pin aliases and actual last release. Either enforce
the real fixture constraint with a fail-noisy domain rule, if justified, or
model cleanup scheduling at the actual last-release point. Do not merely clear
the pending identity to satisfy H5. This is an altitude-preserving environment
request; any correspondence validation belongs to that lane.

The corresponding harness input is:

```json
{"version":1,"id":"campaign2-namespace-pin-alias","net_fixture":"foreign-creator","ops":[{"op":"dup","fd":{"literal":9}},{"op":"wg_netns_close"},{"op":"close","fd":{"ref":0}}]}
```

The Python `harness.trace.validate_trace` accepts this object. The Lean recipe
uses its matching typed trace, avoiding an unrelated parser-reduction claim.

Reproducer:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean Leanux/Proofs/WG/Progress/NamespacePinPending.lean
```

The recipe fails explicitly if original acceptance, output agreement or any
listed boundary changes. Its source is
[NamespacePinPending.lean](../Leanux/Proofs/WG/Progress/NamespacePinPending.lean).
Two attempted direct kernel reductions did not close through the native
nonstructural dependencies; no proof declaration or resource-limit change was
retained. An independent read-only review confirmed the domain and source
chain. The mirror is unchanged by this campaign.

[AGENT 2026-10-20] Preserve the unrestricted completion claim as refuted and
request a fixture/environment disposition, while continuing independent
termination and committed-service proofs. Do not impose an undocumented
no-alias premise to report the original claim as proved.
