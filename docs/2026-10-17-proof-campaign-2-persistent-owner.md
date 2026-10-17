# Persistent keepalive needs more than local hashed-owner coherence

[AGENT 2026-10-17] Classify this as a statement-domain finding. The witness is
an arbitrary native state, not a history accepted from initialization. It
does not establish a mirror discrepancy or a kernel defect. No mirror change
is requested.

The proposed preservation statement was that the original
expiredSendPersistentKeepalive preserves OwnerCoherentSafe on normal return
under that invariant alone. The checked counterexample refutes that statement.
The invariant requires each hashed entry's owner to name a resident peer with
a positive reference; it says nothing about a peer's current-key slot naming
a keypair whose embedded owner is that same peer.

The concrete entry has two peers and two keypairs. Peer 0 has one reference,
is dead, has one staged empty packet, current keypair 1 and a nonzero persistent
interval. Peer 1 has one reference. Hashed keypair 0 names peer 0; selected
keypair 1 names peer 1 and has a valid sending key. Both keypairs have one
reference. Queues, pending timers and wheel entries needed by peer 0's final
release are empty. The one supplied birthdate clock record has site 6 and
eight zero bytes; this is an actual input record, not placeholder time.

The original callback takes the staged path, retains keypair 1, assigns
nonce zero, and acquires peer 1 through that keypair's embedded owner.
createData refuses the dead caller, puts keypair 1 and releases caller peer 0.
That last release removes peer 0. The new packet is freed and the callback
returns normally, while hashed keypair 0 remains with peer word some 0.
The resulting owner predicate is false.

The source proof establishes this normal execution for every native realization
of the fixed Device and single-record projected premise. Other WG and Ambient
fields are universally quantified. The claim includes the entry-coherence
proof and the actual callback's successful projected outcome; it supplies no
successful-prefix witness. Numeric table uniqueness is not what fails here.

The pristine C has the same acquisition/release structure: send.c:386–389
acquires keypair->entry.peer and calls create_data with the caller peer;
send.c:311–331 releases that caller on the failure path. A slot-owner relation
or stronger initialized lifetime invariant is needed to justify substituting
one peer for the other. This source comparison supports the statement-domain
classification; it is not a proof that the witness is reachable in C.

The same witness does not establish a normal-return counterexample for
expiredSendKeepalive: that callback subsequently reads peer 0 and Stops.
Its potential preservation proof would require a relational staged-send
contract and that later successful read.

Artifacts are Index/OwnerCoherencePersistentFindingModel (seven witness
definitions and entry coherence), Source (total actual native execution),
Claims (the projected refutation), and the literal terminal
original_persistent_keepalive_owner_coherence_counterexample in Statements.
All four theorem declarations are checked at default proof limits. Independent
source review finds no issue. Scoped build, standard-axiom audit and fresh
replay are recorded with the checkpoint in the campaign report.

Reproduce in the campaign worktree:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle \
  lake build Leanux.Proofs.WG.Index.Statements
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle \
  lake env leanchecker --fresh Leanux.Proofs.WG.Index.Statements
~~~

The broader direct staged/keepalive preservation composition would overlap
six shared families: cpumaskChooseOnline, enqueuePerDeviceAndPeer,
enqueuePerPeerTx, createData, sendStagedPackets and sendKeepalive.
The alternative owned Config staged contracts cover absent/invalid-key
fallback, not this valid-key failure path. Neither architecture supplies the
missing relation. That layer remains inventoried in the shared-frame followup;
this counterexample copies none of it.
