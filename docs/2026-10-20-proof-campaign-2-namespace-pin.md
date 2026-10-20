# H5: namespace-pin alias tears down early and leaves cleanup pending

Status: reproduced against main `3308c49a` and again after the carry to
main `1a69cebb`. This is a Rule Zero clause-1 mirror/environment defect:
premature teardown at operation 1, followed by unserviced pending cleanup at
operation 2. The independent [landing review, S3](2026-10-20-review-campaign-2-landing.md)
identifies the first symptom against the C. The observations are interpreter
evidence, not a kernel-reduction theorem or a differential Linux capture;
no kernel defect is asserted.

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

## Premature teardown, cause and supplied-mode refusal

The pending bit is the second symptom. At operation 1, `wg_netns_close`
closes fixed descriptor 9 while descriptor 10 still retains the pin's file.
Nevertheless its wrapper invokes `Env.netnsCleanup`: the mirror performs
`WG.netnsPreExit` (carrier off, socket reinitialization and endpoint-source
clearing) and the creator namespace's FIB teardown. The review's original-run
probe reports `wg_netns_pre_exit.creator=1` at operation 1, just as for the
plain `[wg_netns_close]` trace. Branch labels are a compared channel, so this
predicts divergence there, before operation 2's pending bit.

In the C, closing descriptor 9 with that alias retained does not reach the
file's `__fput`, hence does not call the pin's `put_net` or queue
`cleanup_net` (`net/core/net_namespace.c:697–703`). WireGuard's
`wg_netns_pre_exit` (`drivers/net/wireguard/device.c:409–428`) therefore does
not run at that close. The asynchronous cleanup after the actual last
`put_net` is legitimate C deferral; the mirror's earlier teardown is not.
This is not a wording artefact of the H5 pending-emptiness clause.

Two environment choices cause the premature effect. `Syscalls.netnsClose`
(`Leanux/Syscalls.lean:225–232`) assumes the fixed pin close releases the last
reference, but parser and harness permit aliases. `Env.netnsCleanup`
(`Leanux/Env.lean:1127–1131`) silently skips `resolveUnit` when `peekUnit`
finds no cleanup unit, then runs the worker section regardless. Later, the
ordinary `close(ref 0)` reaches the real last file release;
`FS.fputFinal` (`Leanux/FS/Fput.lean:68`) queues worker 12, and no cleanup
suffix services it there.

Supplied-record checking refuses this trace noisily: the real execution has
no cleanup section-start record at operation 1, so the attempted section
cannot be matched. Independently, an operation reaching the later pending
cut with supplied records would be refused by `Runner.lean:1197–1200`.
These are refusal points, not a claim that one execution reaches both.
The open acceptance path is the `--domain` placeholder filter
(`Leanux/Main.lean:43–45`), whose final pending guard is disabled. This is
the same environment-lifecycle class as request 4, fixed at `3f3879e0`, but
the namespace-pin case remains open. No supplied-mode trust-surface bypass
or new Linux capture is claimed.

The mirror lane has two possible fix shapes: reject a retained pin alias
with an explicit domain refusal, or queue and run cleanup at the actual last
release while modeling the C's asynchronous `cleanup_net`. Selecting and
validating either shape belongs to that lane. This report prescribes neither
and changes no mirror code. Both are altitude-preserving environment changes;
clearing the pending bit alone would leave the operation-1 defect intact.

The corresponding harness input is:

```json
{"version":1,"id":"campaign2-namespace-pin-alias","net_fixture":"foreign-creator","ops":[{"op":"dup","fd":{"literal":9}},{"op":"wg_netns_close"},{"op":"close","fd":{"ref":0}}]}
```

The Python `harness.trace.validate_trace` accepts this object. The Lean recipe
also parses it with `Runner.parseTrace` and checks that its original output
agrees with the typed trace and boundary observer. These remain interpreter
checks, not parser-reduction theorems.

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
