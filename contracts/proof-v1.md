# Local proof obligations, version 1

The first reference fragment is the configured Linux `eventfd_ctx_do_read` at
the pinned source revision. It chooses an output from the semaphore flag and
counter, assigns the output, then subtracts that value from the counter.

The source author maintains a distinct reference representation with UInt32
flags, a UInt64 counter and output slot, and explicit control points at entry,
after output assignment, and exit. The mirror uses
`Leanux.FS.Eventfd.Ctx` from `Leanux/FS/EventfdTypes.lean`. Its executable helpers
are `readValue : Ctx → UInt64` and `eventfdCtxDoRead : Ctx → ReadResult` in
`Leanux/FS/Eventfd.lean`. `ReadResult` contains `value` and `next`.

The relation equates counters, relates the reference's low semaphore flag bit to
the mirror boolean, and relates the assigned output to the mirror's `readValue`
at the intermediate point. At exit it relates the updated counter and output to
`eventfdCtxDoRead`. Quantify over all UInt64 counters and all UInt32 flag patterns
consistent with this relation, including zero/nonzero and both semaphore modes.
The mirror must preserve the semaphore field. Corresponding state updates and
effects are required at each point; an unrelated proposition is insufficient.

Record the lock-held, writable storage, disjoint output/context storage, and
absent external interference conditions behind this restricted reference. These
conditions are explicit context assumptions of the source bridge; no C memory
semantics or lock theorem is claimed. Provide inhabited examples for every branch
and explain how callers in the supported API domain establish the preconditions.

The second obligation concerns the actual executable FD state and close helper:
under well-formedness and two distinct live descriptors naming the same object,
closing one preserves lookup and access through the other. The source/model team
must settle the exact state API and freeze the corresponding proposition and
definitions before accepting proof repairs.

Freeze the reference transitions, relations, admission predicates, effect
comparison, interface definitions, theorem types, and their noncandidate
dependencies by content identity when those Lean definitions are first accepted.
The reference must not call mirror functions to define reference behavior.
Candidate changes may modify the designated mirror implementation and proof
terms, not weaken the protected definitions or statement.

The permitted logical baseline is Lean's kernel plus the standard declarations
`propext`, `Classical.choice`, and `Quot.sound` when they occur transitively.
Record the actual dependency list for each theorem. Reject proof holes,
`sorryAx`, additional axioms, and unapproved computation-oracle assumptions.
Use kernel-checked proof terms; a successful build alone is not proof acceptance.

The accepted evidence category is **encoded-fragment simulation**, with the
reviewed configured-source-to-reference correspondence an open formalization
obligation. No theorem connecting this reference to a formal semantics of real
kernel C is claimed by version 1.
