# Independent review: allowed-IPs scaling charter

Reviewed on 2026-10-20 against landed base
`1a69cebb93fc6c5b5adf010562c709e126413c3e` and the proposed
[charter](2026-10-20-charter-binary-allowedips.md). This is a static review of
the charter, existing binary interfaces, mirror definitions and local Linux
source; it does not claim a new executed witness or kernel acceptance.

The target is useful: insertion tests new allocation and mutation obligations,
and insertion followed by lookup on retained memory tests whether the existing
work composes. The sequential assumptions are appropriate for the stated
experiment. However, the unrestricted exact-state target currently encounters
a concrete mirror discrepancy, and the retirement and operation interfaces
need the clarifications below. Independent insertion and reconstruction work
can continue while the discrepancy is resolved; it must not be counted as a
completed checkpoint.

## F1 — Blocking: exact sequence-counter reconstruction fails at wraparound

The charter includes the sequence counter in reconstruction, requires arbitrary
finite accepted sequences, and forbids silently excluding machine-width edges.
Those requirements cannot all hold for the current definitions.

Evidence:

- [AllowedIps.seq](../Leanux/WG/Types.lean#L46) is a `Nat`.
- [insert](../Leanux/WG/AllowedIps.lean#L180) increments it with natural-number
  addition before calling `add`. Removal and clearing also use natural-number
  increments.
- Linux `drivers/net/wireguard/allowedips.h` declares `struct allowedips.seq` as
  `u64`; `allowedips.c:287` and `:298` increment it before calling `add`.
- [NetlinkDump.getPeer](../Leanux/WG/NetlinkDump.lean#L140) observes the counter
  through a zero sentinel and equality tests. It is not a universally invisible
  ghost field for the eventual whole-WireGuard target.

A short constructed-state witness avoids allocator behavior entirely:

1. Start with an otherwise valid empty IPv4 table whose mirror and binary
   sequence counters both equal `2^64 - 1`; provide a mapped four-byte address,
   ordinary call/coverage resources, and a valid peer interpretation.
2. Execute `wg_allowedips_insert_v4` with CIDR 33, paired with mirror `insert 4`
   on the same arguments.
3. Both return `-EINVAL` without allocating. The mirror counter becomes
   `2^64`; the binary counter becomes zero. Exact reconstructed state differs.

This is a semantic deduction from the definitions, not yet an executed binary
counterexample. The implementation agent has been notified and is preparing
that execution. Repeating updates from initialization is another way to expose
the same problem, but is unnecessary for the witness.

Required disposition: preserve the witness and report this as a Rule Zero
finding. Obtain a mirror correction or an explicitly approved change to the
target abstraction before closing the affected theorem. A non-wrapping
precondition is not a repair under this charter. A modulo projection or an
epoch ghost is a target change that needs an explanation of which future
observations it supports; it is not an automatic whole-WireGuard solution.
Continue independent obligations without presenting the exact unrestricted
checkpoint as achievable against the current mirror.

## F2 — High: logical retirement must retain the physical callback resources

The charter includes WireGuard's reclamation callbacks and says to justify
abstracting unreachable retired objects. It does not yet specify the physical
state that survives retirement, or the schedule connecting a logical free to
its eventual callback and reuse. The distinction matters for actual supported
reads, even under fully serialized execution.

Evidence:

- Mirror [free](../Leanux/WG/AllowedIps.lean#L272) erases the old subtrees from
  its node store during the operation.
- Linux `allowedips.c:258–278` detaches the roots, removes peer-list links and
  queues `root_free_rcu`; `root_free_rcu` at `:56–67` subsequently reads the
  retired nodes' child pointers while traversing and freeing the forest.
- `struct allowedips_node` in `allowedips.h` overlays `peer_list` and `rcu` in
  a union. An enqueue can overwrite bytes which the live-node list assertion
  used to interpret. Keeping the entire old live-node assertion unchanged is
  therefore also incorrect.

Required disposition: put a concrete lifecycle in the charter before the B
implementation depends on it. One sufficient design distinguishes live nodes,
detached objects/forests retained for a pending callback, and actually released
allocations. The retired resource must preserve the fields and ownership used
by the relevant callback, allow the queue's specified writes to the union,
and prohibit reuse until release. Callback execution can stutter at the mirror
level while changing this physical resource. Its traversal and release coverage
remain proof obligations, not promises supplied by the RCU service contract.

Choose and state a serialized release schedule. Exercise clear, a later callback,
and reuse; also exercise the individual-node retirement path. This does not
require a general RCU correctness proof. It makes the proposed finite-sequence
claim and the identity interpretation well-defined.

## F3 — Medium: specify the operation observations and supported domain

The charter's common phrase "same result" does not yet define a comparison for
all operations in checkpoint B. Literal ABI results and mirror results have
different shapes, and the existing lookup proof supplies a narrower projection
than the new component relation.

Evidence:

- Linux `wg_allowedips_read_node` returns `AF_INET`/`AF_INET6` (2/10 on the target)
  and writes the prefix/address through output pointers. Mirror
  [readNode](../Leanux/WG/AllowedIps.lean#L286) returns a triple with family 4/6.
  For IPv4, C writes four address bytes, not the entire 16-byte output array.
- The source/destination wrappers read `skb->protocol`, the network-header
  location and address bytes. Mirror [lookupDst](../Leanux/WG/Device.lean#L41)
  receives a family and an integer; [lookupSrc](../Leanux/WG/RxData.lean#L162)
  receives a family and packet bytes.
- Mirror lookup explicitly refuses a dying-peer retry
  ([Device.lean](../Leanux/WG/Device.lean#L29)). Under a serialized environment,
  the corresponding binary retry can continue indefinitely. The existing
  [lookup_checked](../binary/PairCallAdequacy.lean#L60) assumes an accepted
  source run and does not prove a returning lookup for that case.
- [PairTrie.State and target](../binary/PairTrie.lean#L30) currently reconstruct
  nodes' key/child/peer fields and peer counts. They omit the roots, sequence,
  packed parents and ownership lists. Root identities are supplied separately
  to its heap assertion. Reusing that theorem is useful but does not itself
  preserve the new component relation.

Required disposition: add a compact operation-interface inventory to the
charter. State each mirror entry point, binary entry, argument decoding,
result/output-buffer observation, and existing explicit refusal. Specify that
CIDR and address inputs originate from the binary-width argument decoding;
arbitrary unbounded mirror Naturals are not identical ABI arguments. Keep the
lookup retry refusal visible as a limitation of accepted-run refinement, with
its binary retry test, rather than calling it a proved returning path.

For checkpoint A, explicitly require deriving lookup's input root from the
retained table bytes and proving that lookup preserves the extended component
assertion, using its write footprint. Run this stronger assertion before and
after lookup in the executable sequence as well. Output and packet argument
bytes can remain local interface resources; they do not require extending the
global relation into unrelated kernel state. Count this adapter/frame work as
composition work in the measurements.

## Other assessment

The charter correctly separates tested cases from universal proofs, states
external service hypotheses, requires executable witnesses, forbids assuming
future correspondence, and separates the external kernel gate from builds.
Requiring service contracts to avoid supplying WireGuard's own mutations is
particularly important for allocation rollback and removal. The proposed
four-hour report is a calibration checkpoint, not evidence that B fits within
four hours.

No additional audit infrastructure is needed for these findings. Resolve them
in the charter and the existing assertion/theorem/report workflow. A successful
A would support a concrete scaling comparison; B remains a further substantial
proof target, especially its list traversal and reclamation resource.

## Recheck of the revised charter

Rechecked on 2026-10-20 after the operation-interface inventory, retired-resource
schedule and explicit review disposition were added. This recheck also inspected
the in-progress `AllowedipsSeqWrapMain.lean` and `allowedips_seq_wrap.py`; it did
not run a second build or independent execution.

| Finding | Disposition after recheck |
| --- | --- |
| F1 | **Accepted, still blocking exact unrestricted closure.** The implementation agent reports execution of both invalid-prefix wrappers to return with real callback bodies: 124/127 instructions, agreement for ordinary counter 1, and binary zero versus mirror `2^64` at wrap, under both undefined-value seeds. The reproducer source uses actual service interpretation, checks the ABI return and signed errno, and reports equality failure noisily. This report of execution is attributed to the implementation agent; the reviewer independently checked its code, not a second run. A mirror-lane correction or approved target change remains necessary. |
| F2 | **Addressed at charter level.** The revised lifecycle separates live, retired and released allocations; retains callback-readable child graphs; transfers ownership of the list/RCU union; permits dispatch only between API calls; and permits reuse only after the free service. Pending callbacks may remain after a finite prefix, with explicit draining events. These choices settle the scheduling/resource ambiguity without importing general RCU verification. Their preservation and callback traversal remain implementation proof obligations. |
| F3 | **Addressed at charter level.** The operation inventory now specifies ABI decoding, void returns, family translation, byte-sized output observations, packet/header input resources and initialization as a correspondence lemma. The dying-peer retry refusal is explicit. Checkpoint A now requires reading the lookup root from retained table memory and preserving the extended component assertion through the existing lookup proof and its frame. |

No additional charter blocker was found in this recheck. Proceed with the
independent obligations under the revised plan. F1 must remain visible in the
status and report until resolved; closing F2/F3 here does not certify their
implementation or turn the current branch into a completed refinement result.
