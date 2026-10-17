# Initialized give-up cleanup without session allocation

## Result and classification

The actual initialized mirror runner accepts a generated 23-operation history
that sends an initiation, performs nineteen retries, and then gives up.
Give-up enqueues the zero-key cleanup timer although every observed operation
boundary has allocation counter zero, an empty keypair store and empty peer
key slots. Every operation's actual decision log also contains no keypair
allocation or session-begin decision.

This is runtime evidence over the executable mirror, with the original runner
and the proof-tree boundary observer producing identical complete JSON.
It is not a Linux capture, a closed execution proved by kernel reduction,
or a universal theorem about intermediate states. The witness adds no theorem
or terminal-headline credit.

The too-strong formulation identifies all zero-key timer arms with successful
session creations. This example separates give-up cleanup from session-derived
arming. Source inspection agrees with a statement artefact: the pristine
Linux timers.c:41--63 explicitly schedules cleanup after excessive failed
handshake attempts, to remove residue of a partial exchange. Its separate
session-derived hook is at timers.c:199--207. No discrepancy with the mirror
is identified and no kernel-bug or upstream report is proposed.

[AGENT 2026-10-17] Count session-derived hook events separately from give-up
cleanup arms. Continue to distinguish a hook invocation, its guarded logical
timer effect and a physical enqueue. The already proved SessionArmEvent and
local partial-exchange arm contracts retain their scopes; complete caller
deltas and general session-relative histories remain open.

## Executed history

The generator reads the tracked d3_retransmit_gives_up corpus configuration.
It sets persistent keepalive to zero and supplies explicit deterministic
draws, clocks, dispatch records and timer-wheel records. Its operations are
configuration, device up, one transmit, and twenty advances of 1450 ticks.
These are generated inputs, not recorded Linux observations.

The driver uses the existing Progress.executeTraceWithBoundaries observer.
Its proved all-errors erasure starts at the actual runnerInitial and follows
the original syscalls, ambient-record consumption and final guards. The
driver also executes the original Runner.executeTrace and requires identical
complete output. Neither execution is reconstructed from a snapshot.

| Boundary | Attempts | Sent initiations | Timer enqueue count |
| --- | ---: | ---: | ---: |
| Initial transmit | 0 | 1 | 1 |
| Retry callback 19 | 19 | 20 | 20 |
| Give-up callback 20 | 19 | 20 | 21 |

All 23 accepted boundaries have zero keypair counter, empty key store and
empty previous/current/next slots. The per-operation decision logs exclude
keypairCreateNoMem, all five session-begin decisions and both incoming/outgoing
session-begun decisions. Each advance has one actual retransmit callback.
The give-up comparison has operands (19,18); it purges the one staged packet,
detaches retransmit, sends nothing further and leaves zero-key pending with
expiry equal to the actual caller tick plus ZERO_KEY_MATERIAL_TICKS.
The wheel entry's enqueue stamp is 21. The listener contains twenty distinct
148-byte initiations; device totals are twenty packets, 2960 bytes and one drop.

Boundary emptiness alone would not exclude a transient allocation followed
by erasure. The decision checks and source audit are separate evidence:
Leanux/WG/Keypair.lean:63 contains the only operational keypairCounter
assignment in WG/Env/Runner, an increment after keypairCreateNoMem.
This source observation is not advertised as a newly proved universal
monotonicity theorem.

## Validation and reproduction

The scratch runtime probe passes first time without warnings; it explicitly
uses --root . because the generator is then below .tmp. Independent review
checks the actual runner connection, fail-closed assertions, per-operation
log reset, wheel calculations, due-timer selection and final guards. It
requests only a more precise keypair-allocation output label; that is fixed.
The installed generator's docs location supplies the repository root by default.
The corrected installed command also passes without warnings. There is no
failed run, infrastructure retry, cap/limit increase or guest boot.

The standalone Lean module builds in 71 jobs; its only warning is the
inherited Env:865 String.mk deprecation. Source build, axiom inspection and
kernel replay check this executable's definitions and imported proofs; they
do not turn its runtime assertions into a closed-execution theorem.

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle bash -o pipefail -c \
  'python3 -B docs/proof-campaign-2-giveup.py |
   lake env lean --run Leanux/Proofs/WG/TimerDiscipline/ReplayInitializedGiveUp.lean'
~~~

The source artefacts are
[the generator](proof-campaign-2-giveup.py) and
[the runtime driver](../Leanux/Proofs/WG/TimerDiscipline/ReplayInitializedGiveUp.lean).
Regenerate the JSON and runtime output; no trace dump or log is committed.
