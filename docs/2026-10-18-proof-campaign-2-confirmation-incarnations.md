# H1 finding: keypair store IDs are local to a device incarnation

## Disposition

The proposed whole-run generalization that every accepted initialized run
has pairwise distinct successful confirmation **raw KeypairIds** is false.
An ordinary device deletion/recreation reuses store slot 0 for a different
allocation. This is a statement artefact, not evidence of a mirror defect or
a kernel bug. The charter's once-per-keypair-allocation claim remains open;
this example neither refutes it nor proves it.

The raw KeypairId is the mirror's key-store location. It is not the wire
session index, and it is not Keypair.internalId, the allocation stamp.
Existing fixed native-history uniqueness theorems exclude device recreation
and retain their stated initial frontier premise; they are unchanged.

## Accepted model counterexample

Start from the actual initialized Runner. Execute the six operations in
corpus/wireguard/d2_respond_then_data.json, then wgDelete and wgCreate, then
the same six operations again. Duplicate the fixture's two steering inputs
in the same order. No arbitrary execution state is supplied.

Both original Runner.executeTrace and the existing
RxCredits.RunnerAccount.observed return normally in placeholder mode and
produce identical JSON. The committed history contains exactly these two
consumption receipts:

| Device ifindex | Store KeypairId | Allocation internalId | Entry next | Exit next | Exit current |
| ---: | ---: | ---: | ---: | --- | ---: |
| 3 | 0 | 1 | 0 | absent | 0 |
| 4 | 0 | 2 | 0 | absent | 0 |

Both original receivedWithKeypair comparisons take their successful
promotion branches at zero-based operation indices 3 and 11. Deletion and
creation return zero at indices 6 and 7. The final allocation counter is 2;
the final device has ifindex 4 and local allocation frontier 1.

The observer's committed allocation events are (slot 0, stamp 1), then
(slot 0, stamp 2). Both receipt summaries come from the actual normal
consumeDataDone entry/exit witnesses. The reproduction requires exactly
two such events and complete summaries, so missing lookup data cannot
silently disappear from the check.

## Why the raw-ID formulation fails

wgSetup installs a new Device whose nextKeypairId starts at zero. The
allocation counter lives in the surrounding WireGuard world and survives
wgDelete/wgCreate. Consequently these are two different keypair objects.
The per-allocation formulation must track the existing internalId stamp
through initialization, publication and confirmation; a lifetime invariant
must exclude already-confirmed stamps from pending slots. No new mirror
field or mirror change is requested.

An independent review checked initialization, deletion, creation, allocation
and the runtime observer, including receipt completeness and both actual
confirmation comparisons. It found no source-path or witness defect.

## Reproduction and evidence boundary

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/Noise/ReplayConfirmationIncarnations.lean < corpus/wireguard/d2_respond_then_data.json
```

The module constructs the typed trace from the unmodified fixture and fails
noisily on any Stop, output disagreement, missing receipt, unexpected
allocation, comparison, lifecycle result or final frontier. It prints only
the compact conclusion; no generated trace or evidence dump is committed.

This is runtime evidence from the accepted initialized model in its declared
placeholder mode. It is not a Linux capture, a differential check, or a
kernel-proved closed evaluation of the 14-operation trace. The existing
observer has a generic kernel-checked erasure theorem; that does not turn
this concrete execution into a kernel-normalization proof. No extra
assumption or trusted executable-evaluation axiom was introduced.

Development used eight capped stdin probes: three passed, five failed.
Two failures corrected exploratory syntax/representation issues. Three
bounded attempts to obtain a closed kernel execution failed during
elaboration/reduction; none is credited as a proof. The final standalone
runtime reproducer passed independently from its committed source. No
infrastructure rerun, increased resource limit or killed process occurred.

The campaign stops at this finding with the closed receive-step and socket
support committed. H1 still needs per-allocation initialized uniqueness and
whole caller tag composition; H2–H6 retain their reported open whole-run
scope. There is no new request for the mirror team or upstream tray.
