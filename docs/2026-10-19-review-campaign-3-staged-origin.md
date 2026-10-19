# Staged-origin and transmit-binding review

[AGENT 2026-10-19] Independent source review of the parent worktree's pending
staged-origin closure, based on its uncommitted files above `483691ae`.
The review was read-only. It examined the four final modules, their source
carriers and receipt definitions, the native send path, and T2 in the charter.
The parent was repairing compilation concurrently; this note makes no new
build or kernel-validation claim. No mirror defect was established.

The new links establish useful initialized provenance. They do not yet
establish the whole T2 outcome. The following boundaries must remain visible
when packaging that outcome.

## 1. Historical key ownership is not in the socket conclusion

**Required before the full T2 ownership claim.**
`StagedSocketFinal.lean:23` returns
`AllocationSelection.Earlier` for the socket peer and the actual encryption's
`Responder.KeyCore`. This proves that the selected peer's current slot held
that allocation and sending material. It does not assert the selected key's
own peer association. `HandshakeSecurity/ResponderProjection.lean:9–15`
retains only allocation identity, role and sending key; changing `Keypair.peer`
does not change this projection. `AllocationSelection.lean:10–13` likewise
contains no owner equality.

Consequently, the current conclusion does not discharge the explicit
key-peer clause at charter lines 227–230. A peer's current slot pointing at a
key associated with another peer satisfies the local selection/core shape;
excluding that state requires the initialized ownership fact. This is a
missing connection in the exported claim, not evidence that such a state is
reachable in the mirror.

There is a narrow existing route to the missing fact. The initialized
`ResidentMaterial.Bounds` already includes `CurrentSlots.Inv`;
`Queues/CurrentSlots.lean:18` derives nullable current-key compatibility.
`Queues/RxIngressStable.lean:829`, `compatible_peerDeref`, combines that
compatibility with the actual successful native key-owner dereference to
identify its returned peer. The staging source performs that dereference
before allocation (`WG/Send.lean:270`). Currently
`ResidentMaterialSelection.lean:26–40` retains only the frontier bound, and
`ResidentMaterialStaging.lean:114–120` frames the dereference without retaining
its ownership conclusion. A historical admission certificate at this cut can
bind the selected allocation and sending core to `key.peer = some pid`.
Afterward, retain the immutable core; requiring the mutable owner word to
remain nonnull at encryption would be an unjustified strengthening across
retirement. No new H1 assumption is indicated by these local facts.

## 2. Batch-local distinctness does not provide conservation

**Required before marking T2 complete; already an acknowledged open boundary.**
`StagedOrigins.lean:61–63` supplies a distinct ticket list for one batch.
Its `Inv` is one-way, from resident staged packets to earlier births
(`:100–102`), and `Safe` checks selections (`:109–117`). Neither predicate
accounts for every admission, consumes a birth ticket, relates tickets between
two allocations, or records pending versus terminal outcomes.

The final encryption theorem further reduces the alignment to membership
(`StagedEncryptionFinal.lean:17–20,47–53`). This proves that the plaintext has
an earlier matching birth, but drops its specific allocation ordinal and
ticket assignment. Two separate allocations can satisfy these propositions
with the same birth ticket. This is a countermodel to the predicates being
sufficient for conservation, not an initialized mirror execution.

The final conservation join therefore needs a consistent occurrence assignment
across allocations and a disjoint partition into pending obligations and named
terminal outcomes. Existing physical packet-identity nonreuse does not by
itself supply uniqueness of the earlier staging birth: separately allocated
packet identities can share a payload. Keep both the allocation index and its
assigned staging ticket through that join.

## 3. Receipt binding needs the converse emission coverage

**Required to quantify over every emitted datagram.**
`StagedSocketFinal.initialized_socket` starts from an actual `.socket` event
(`:13–16`). `Completion.SocketReceipt.Valid` certifies its native packet read,
peer read and socket call; `SocketEmission` describes zero or one added
datagram, appropriately allowing a failed send. The result does not itself
show that every appended or subsequently delivered transport datagram has
such a receipt. That converse must come from the final emission-accounting
carrier, including socket calls before later Stop and delivery-cleared
prefixes. The reviewed proof should remain described as receipt binding until
that join is made.

## Connections that check out

The initialized staged closure uses the actual shared driver and runner,
with no incoming carrier hypothesis. Its source proofs preserve saved batches
through selection and no-key restoration; allocation is not incorrectly
treated as a fresh plaintext birth. The final joins use exact ordered journal
projections and actual receipt positions, rather than equating independently
instrumented histories from output erasure.

For a routed birth, `RoutingReceipts.Receipt.selection` (`:174`) provides the
native lookup/splice cut and checks every input packet's destination against
the routed address. Thus `Born.routed` is not merely an arbitrary caller
label. `initialized_allocation` also retains the selected peer's allocation
stamp, device epoch, and exact MTU-normalized plaintext sequence. Keepalive
births require the actual successful native preparation on an empty staged
queue and retain its caller peer and MTU.

The current-key connection retains the actual allocation stamp and sending
material; it does not equate key incarnations merely because numeric slots
match. Socket ciphertext binding also reuses the earlier encryption's exact
packet material and bytes. These are the right connections for the three
selection times required by T2.

The declarative longest-prefix interpretation remains separately available
through R3. `RoutingReceipts.Receipt.authorized` (`:193`) reuses its native
contract with an explicit `RoutedView` premise. The new final statements do
not compose R3's separate initialized outgoing journal into this one. Native
destination lookup is already established; a final claim about the flat
routing history must retain or derive that additional relation at the same
receipt, rather than infer it from common erasure.

Reviewed content identifiers (SHA-256):

- `StagedInitialized.lean`: `9683762cdbf4a296dd3ab3f700a7862fdceec633e41b7f5a3608d21d0a8d75c1`
- `StagedAllocationFinal.lean`: `803ea4f34eb0a826ccadd3c3853309965a906c1857edaffc2a773c39fb83c59d`
- `StagedEncryptionFinal.lean`: `58473191c082d21e034e539614f28ce3963f9c40042810416f5aeae84e21af12`
- `StagedSocketFinal.lean`: `21e445e03ad6563cdeca905b052f3aceefa6ba253dfc2a94b47f8480304a3964`

## Disposition

[AGENT 2026-10-19] All three findings are accepted as missing connections
for the full T2 outcome. The checkpoint exports explicitly retain their
boundaries and T2 remains open. Historical key-owner evidence is being added
at the native admission dereference. Cross-allocation conservation and the
converse emission carrier remain active campaign obligations; neither is
discharged by the present provenance theorems. No mirror change is proposed.
