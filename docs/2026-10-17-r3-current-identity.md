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

## Session, preparation and retirement extension

Four more modules add 15 theorems and four terminal exports: 464 proof files,
6,641 theorems, and 524 terminal declarations (522 theorems/two definitions).
All previous 144 R3 terminal bodies remain unchanged; R3 now exports 148.
The executable mirror remains unchanged.

CurrentSession carries the same configured witness through actual session
installation and the once-only observer. The normal whole-session tail supplies
configuration; a completed front preceding a Stop does not. Arbitrary unrelated
incoming receipts need no global validity premise. PublicationPrepare locates
the fresh actual decrypt receipt and derives the current certificate only on
successful decryption, using the existing weaker RX-compatibility premise.

CurrentPeerRetains covers actual peer payment and make-dead calls without a
positivity, affiliation or initialized-state premise. Deletion is allowed;
survivors retain both stamp and static key. AffiliationMaintenance establishes
the empty seven-field fixture for both flags and preserves nullable affiliation
through slot clearing; handshake clearing and expiry retain its exact view.

Full-source independent reviews pass for all four modules and terminal exports.
The 11 output-free candidate checks comprise six failures and five passes:
affiliation 1/1, session 2/2, retirement 3/1, preparation 0/1 (FAIL/PASS).
These were ordinary proof-construction failures; recovery sorryAx dependencies
in failed elaborations were rejected. The affiliation wrapper error and recovery
ref are recorded above. The first central build failed on two incorrect
namespace qualifiers in the new exports; the corrected build passed 482 jobs.
The full proof gate passed 522 jobs/524 terminal declarations in 2.55 seconds;
fresh root replay passed in 99.01 seconds without warnings. The gate still
reports only the unchanged mirror's String.mk deprecation. No infrastructure
rerun, cap increase, mirror or guest change occurred.

Initialized configured/current support, publication-to-consume transport and
the initialized routing/Stack join remain open.
