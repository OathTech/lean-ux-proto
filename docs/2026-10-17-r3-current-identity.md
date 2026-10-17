# R3: configured and current peer identity

This extension follows the completed state-split retrofit at 525a861d.
It leaves the executable mirror unchanged over b3f56807, whose executable
sources equal b700659. Initialized packet authorization remains open.

## What is established

The actual empty fixture establishes configured-table coherence and current
session support for both network/bare flags. Initialization fixes only the
original seven WG store fields. Native key clearing, handshake clearing and
sending-key invalidation retain configured identity and existing session
support. Allowed-IP root/list clearing and eight timer operations retain the
configured peer cells on their actual normal returns.

[AGENT 2026-10-17] Keep historical material and current peer identity in one
supporting session witness. Separate historical/current existence claims do
not establish that they describe the same identity.

CurrentIdentity adds a conditional comparison to the existing session receipt:
when a valid resident key names a resident peer, its allocation stamp and static
key match that receipt's Context. Missing keys, invalid keys, missing peers and
cleared owner words remain admissible. Its history-free retention relation
composes exact receiving-material transport with the surviving peer fields.
Concrete erase, saved-cell write, fresh-frontier allocation and key-owner
clearing lemmas support later native composition. Exact configured-view frames
supply the peer-field part without an affiliation premise.

Nullable affiliation supplies RX/current-key compatibility directly. Actual
successful decrypt publication preserves the resident peer through its reference
increment and NAPI write. The stronger certificate joins its AEAD input/output,
packet stamp, stored CRYPTED packet and current peer to one configured session
witness; projecting it recovers the earlier historical certificate. The main
theorem retains the weaker RX-compatibility premise. Full affiliation is a
separate corollary. DEAD publication receives no successful-decryption claim.

These are initialization and local composition results. Whole-run configured
affiliation/current support, transport of publication certificates to consume,
and the routing-history join at the reached delivery cut remain open. No
cryptographic authenticity, Linux simulation or new counterexample is claimed.

## Counts and validation

Eight modules add 55 theorems and eight definitions. Three R3 terminal exports
add fixture identity, nullable compatibility and successful current-identity
publication. All 141 earlier R3 terminal bodies are unchanged; R3 now has 144.
The proof tree moves from 452 files/6,564 theorems to 460 files/6,622 theorems.
The terminal surface is 520 declarations: 518 theorems and two definitions.

Complete candidate source checks and all 63 new module roots pass with only
the three permitted axioms and zero warnings. Independent full-source reviews
pass. Review identified an unnecessary full-affiliation input to the publication
strengthening; the final theorem restores weaker RX compatibility and provides
the affiliation wrapper separately. Current-identity transport was reviewed
against the actual native source and the seven-field initialization boundary.

The central scoped build passes all 337 jobs. The complete proof gate passes
all 518 jobs and 520 terminal declarations in 5.52 seconds, including forbidden
tokens and import/target boundaries. Its sole warning is the already reported
String.mk deprecation in the unchanged mirror. Fresh root replay passes in 98.01 seconds without warnings.

The 25 capped output-free development checks comprise fourteen ordinary
failures and eleven passes: maintenance 7/2, clearing/timers 4/2, current identity
2/2, compatibility 0/1, publication peer 0/1, current publication 1/3 (FAIL/PASS).
Failures were source-factor normalization, missing binder types and an equality
already rewritten by case analysis. Two failed checks printed recovery
sorryAx dependencies; those checks were rejected. No such dependency is in the
accepted source. There was no crash, infrastructure retry or limit increase.
The next prepare/session/removal candidates are outside this checkpoint.
During subsequent affiliation development, a status wrapper failed after its
completed failed Lean check. Before correction, dirty worktrees were preserved
under refs/snapshots/proof-campaign-r3-status-driver-recovery-20261017T065225Z/;
branch tips and the validated artifacts were unchanged. The failed Lean check
and wrapper error belong to that next candidate's ledger.

## Reproduction

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle scripts/proof-gate
cap scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
~~~
