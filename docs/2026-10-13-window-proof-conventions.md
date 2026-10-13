# Conventions for cheaper mirror-proof ports

These are recommendations from the `fb2c29c` → `ef7c535` window-proof port,
not changes to the executable mirror or its standing no-proof policy.
Keep all C choice points, ordering, failures and observable state effects.
Ranked by expected reduction in future port effort; references name `ef7c535`.

1. **State property theorems over a small semantic projection.**
   **Altitude-preserving.** Relevant boundaries: `Leanux/WG/State.lean:55`
   (packet store), `Leanux/WG/Keypair.lean:49` (allocation) and
   `Leanux/WG/Types.lean:111` (replay counter). Keep lifetime
   identity, allocation frontier and receive-window state separate from queue,
   packet-store and scheduler representations. Give small named allocation,
   deletion and field-update operations stable operational boundaries; prove
   their projection contracts in the sidecar. The window and lifetime algebra
   then survive changes such as packet objects becoming IDs.
2. **Give callbacks explicit effect contracts.** **Altitude-preserving.**
   `Leanux/WG/Data.lean:108`, `Leanux/Kernel/Defs.lean:1317` and
   `Leanux/Env/Batch.lean:180` expose the relevant callback and iteration boundaries. A worker's name is not its
   effect: an encrypt poll now invokes NET_RX. State worker composition over
   arbitrary callbacks that satisfy the required frame/evolution relation.
   The current `workerIter`/Step separation and finite activation loops already
   support this convention better than recursive scheduler fuel.
3. **Expose a committed observation boundary.** **Altitude-preserving as an
   observer addition**, conditional on checked erasure and unchanged C-shaped
   state and choice points. Introducing history fields or proof-specific branches
   into the production mirror would **not** preserve its altitude; keep history
   in the proof-side observer or instrumentation cut.
   Sites: `Leanux/WG/RxData.lean:362`, `Leanux/Env/Batch.lean:197` and
   `Leanux/Runner.lean:828`. A single optional observer at
   the actual validator result would avoid recopying the entire caller chain
   merely to recover acceptance events from JSON-only output. Its default must
   preserve current behavior. A copied-World trial must discard its observations
   with its World; committing an activation retains both. This distinction should
   be explicit at any future trial/rollback boundary.
4. **Frame independently resumable operations locally.** **Altitude-preserving.**
   `Leanux/WG/NetlinkDump.lean:189`, `:322`, `:339` and
   `Leanux/Env/Batch.lean:180` already provide useful operation boundaries. Keep dump chunk,
   dump start, dump receive, activation iteration and lifecycle operations as
   named helpers. State each helper's contract over every successful initial
   World rather than over a particular trace fixture or caller representation.
   Preserve saved-value correspondence where a whole record is replaced.
5. **Export end-to-end relations and keep coverage review small.**
   **Altitude-preserving proof-side convention; no mirror rewrite required.**
   Relevant effects occur at `Leanux/Syscalls.lean:319`,
   `Leanux/Runner.lean:849` and `Leanux/Env.lean:249`. Whole-syscall
   S3 should expose lifecycle plus named-validator evolution over the original
   action, including return-to-user scheduling and ambient processing. A syscall
   constructor list is only a derived nonreceive corollary; update it when
   reachable effects change. A short source-call map should identify validator
   calls, committed callers and discarded probes. Erasure or a final-state frame
   alone cannot certify event completeness.

Keep generic monadic composition independent of concrete syscall observers.
Preserve compiler continuation sharing in proof tooling, and use loop-local
progress facts when an unbounded mirror loop needs framing. These conventions
reduce source-copy and proof elaboration costs without requiring the mirror to
adopt a high-level behavioral specification or add production proof gates.

[AGENT 2026-10-13] Recommend these conventions based on this port's demonstrated
repair boundaries. Their adoption requires a separate mirror change; none is
assumed by the spike's theorems.
