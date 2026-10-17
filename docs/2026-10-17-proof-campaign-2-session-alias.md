# Session publication needs slot/cursor freshness

This is an arbitrary-state invariant finding over mirror b700659, not an
initialized trace, a mirror divergence or a kernel defect. The proof-only
witness is in Index/SessionAliasModel, Source and Claims, with terminal
original_session_alias_owner_coherence_counterexample.

A Device has one live responder peer 0, handshake owner word 0, and index
row (7, handshake 0). The key store is empty and its allocation cursor is 1,
but the peer's previous slot already names 1. Its current and next slots are
empty. DeviceTablesSafe, HashedOwnersCoherent and KeypairStoreBounded all
hold: none constrains that dangling slot.

The projected input also supplies the actual successful allocation record
(first byte 1 followed by 39 zeros), the eight-zero-byte birthdate record,
and the allocation-arm membership. The existing total session contract's
release readiness is proved from this state, not assumed as an execution
witness. Other native/Ambient fields and the serial counter remain arbitrary.

The original beginSession allocates key 1 with one reference. Responder
rotation puts that same key through the captured previous slot and erases
it. Index replacement then publishes (7, keypair 1) and returns true.
The final numeric table remains safe, the cursor is 2 and the serial counter
increases by one; owner coherence is false. The actual immediately following
indexLookup [.keypair] 7 stops with invariant “dangling keypair 1”, rather
than returning a miss or another owner. Both observations use the same
actual intermediate execution.

The C has the same control ordering: noise.c:198–252 installs responder next
and puts captured next/previous slots; noise.c:816–856 allocates, rotates,
then replaces the index; peerlookup.c:166–190 replaces the old row.
This comparison does not establish a reachable C state corresponding to the
dangling-slot fixture. No upstream report or mirror repair is requested.

Two proof architectures were considered. A positive publication-to-lookup
composition can use SessionInstalled and the existing lookup contracts, but
its named SessionRotationFresh premise excludes the allocation ID from the
rotation's puts. The three tested local invariants do not imply that premise.
The concrete source/effect composition above instead checks that inadequacy
directly. Initialized slot/cursor freshness and broader driver propagation
remain open; the local finding does not discharge them.

Reproduce the scoped build and fresh replay of Leanux.Proofs.WG.Index.Statements
with scripts/in-bundle, plus its axiom inspection. On the shared host use
capped, LEAN_NUM_THREADS=32 and LEANUX_QEMU_SLOTS=16. The full inherited
CounterWindow/ReplayWindow gate remains a separate failed aggregate.
