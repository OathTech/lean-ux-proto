# Charter: the receive counter window, proved over the mirror

A long-cycle proof assignment for a Codex agent and its subagents: days, not
hours, left alone to cook. It sets one challenge problem with a clear success
criterion and leaves the proof architecture to the agent.

Provenance: [USER 2026-10-12] asked for a proof spike on top of the mirror with
layered intermediate models, a clear success criterion, Rule Zero, room to
reshape the property when the code's property differs slightly, and no hard
stops. [AGENT, coordinator] wrote the charter; the raft-proofs charters
(`/home/dev/projects/_retired/raft-proofs/docs/2026-09-22_abstract-safety-proof-charter.md`,
its `CLAUDE.md` Rule Zero and briefs) are the pattern it follows.

## 1. What this is, and what it is not

Two proof directions matter to this project. Code to mirror, a separation-logic
simulation against the C, is future work in another tool and is **not** this
assignment. Mirror to property is this assignment: a property of WireGuard
proved over the executable mirror's own definitions, with whatever Lean models
sit in between (a state machine of the window, a refinement from the monadic
mirror to it, a ghost history, framing lemmas). The intermediate structures are
the agent's to design; what is fixed is the object, the statements and the
criterion below.

The mirror is the fixed object. `AGENTS.md` forbids theorems on `main`; this
work lives on a branch that is reported, never merged. Its value is twofold:
the theorem, and the list of places where the mirror's shape resists proof,
which feeds the mirror's altitude review.

## 2. Setup

- Repository `/home/dev/projects/lean-ux-proto`. Pin `main` at the commit you
  start from (record it in your document). `git worktree add
  .worktrees/spike-window -b spike/window <commit>`; work only there. Other
  agents work in other `.worktrees/*`; do not touch them, and do not touch
  `main`.
- Build through `capped -- scripts/in-bundle lake build`
  (`~/.claude/CLAUDE.md`: every heavy job through `capped`; exit 137 is a
  failure). No differential checks, no QEMU guests: the mirror is checked
  against Linux elsewhere; here it is a definition.
- Add files only under `Leanux/Spikes/` (and `docs/`). `Leanux/` outside
  `Leanux/Spikes/` stays byte-identical to the pin. `lakefile.toml` may gain
  the spike library if the build needs it.
- Read first: `AGENTS.md` (the altitude principle, the gates), the mirror's
  receive path (`Leanux/WG/RxData.lean`: `counterValidate`, the window
  update; `Leanux/WG/Types.lean`: `ReplayCounter`, `Keypair.receivingCounter`),
  the runner (`Leanux/Runner.lean`: `executeTrace`, the operations and the
  monad `M`), and the C it mirrors (`drivers/net/wireguard/receive.c`
  `counter_validate`, `noise.h` `noise_replay_counter`, in the locked source
  `.deps/linux`).

## 3. Rule Zero

The kernel code may contain bugs, and the mirror follows the code. So:

- The mirror is the authority on what the code does; the WireGuard paper,
  protocol description and the code's own comments are the authority on what
  it is meant to do. When they disagree, that is a finding, not a proof
  obstacle.
- Claims are never reshaped to fit a bug. If a statement below is false of the
  mirror because of what the code does, record a concrete counterexample
  (a trace and record stream the mirror runs, the two accepted packets or the
  divergence), say whether the code's behaviour is a bug against its intent or
  a legitimate design nuance, and continue: prove the statement under a named
  premise that excludes the trigger and cites the finding, or leave that
  statement unproved with the counterexample recorded. Do not patch the mirror
  or the kernel; findings go to the user, who decides on filing upstream.
- Reshaping for a legitimate nuance is allowed and expected. If the code's real
  property is slightly different from the statement as worded (a boundary
  inclusive where the wording said exclusive, a window update that differs in
  an edge the wording did not foresee, an acceptance that depends on state the
  wording omitted), prove the property the code has, record the original
  wording, the proved wording and the reason side by side, and keep the
  meaning: no packet accepted twice under one keypair, acceptance is the C's
  rule. The user reviews the delta; the agent does not wait for it.

## 4. The challenge

Prove, over the mirror's own definitions, that the receive counter window is
replay-free and is the C's rule. Binding wording; names and architecture are
yours.

- **S1, no replay.** For every trace and every record stream that the runner
  accepts (`Leanux.Runner.executeTrace`), in the execution's sequence of
  accepted data packets no two packets share (keypair, counter).
- **S2, the window is the C's.** `counterValidate kp theirs` returns true in
  a state exactly when `counter_validate` would: `theirs < REJECT_AFTER_MESSAGES`,
  the keypair's counter `< REJECT_AFTER_MESSAGES + 1`, `theirs` within
  `COUNTER_WINDOW_SIZE` of the highest seen, and the bit for `theirs` not yet
  set; and when it returns true the resulting `ReplayCounter` is the C's update
  (the backtrack bitmap shifted and the bit set).
- **S3, framing.** Every operation the runner executes other than the
  data-receive path leaves every keypair's `receivingCounter` unchanged; and
  on the data-receive path only the keypair the packet names changes.

S1 is the point. S2 pins the window to the C. S3 is the lemma a later
code-to-mirror simulation will reuse, and it is where the monadic mirror's
shape will push back hardest. Expect to introduce an abstract window state
machine and prove the mirror refines it; expect to need a ghost history of
accepted packets, populated by the mirror's own steps; expect framing to be
most of the work.

## 5. Success criterion

All required:

1. S1, S2 and S3 are `theorem`s under `Leanux/Spikes/`, with no `sorry`, and
   `#print axioms` on each shows only `propext`, `Quot.sound` and
   `Classical.choice`. A `Leanux/Spikes/Axioms.lean` that prints them for every
   top-level statement is the check.
2. `capped -- scripts/in-bundle lake build` succeeds for the whole project with
   the spike included; `git diff <pin> -- Leanux ':!Leanux/Spikes'` is empty.
3. `docs/2026-10-13-spike-window.md` records: the pin; the proof architecture
   (each intermediate model, what it abstracts, the refinement theorem for it);
   any reshaped statement with the original and the reason; any Rule Zero
   finding with its counterexample; the effort; and a ranked list of mirror
   changes that would have made the proof routine, each with file and line
   references and marked altitude-preserving or not under `AGENTS.md`'s
   principle.

A Rule Zero finding with a counterexample and the remaining statements proved
is a success. A reshaped statement that keeps the meaning is a success. A
statement left unproved with its blocker precisely written is a partial
result, reported as such.

## 6. Working conditions

- Multi-day. Use subagents freely, each on branches off `spike/window` or in
  the same worktree with one writer at a time; never on `main`. Keep a short
  progress section at the top of the document, updated at least daily: what
  is proved, what is in progress, what blocks, what was reshaped.
- No hard stops. When blocked on a statement, write the blocker down and move
  to another statement, a weaker intermediate result, or the framing lemmas;
  come back later. Stop only when the criterion is met, when every remaining
  statement has a written blocker you have tried at least two architectures
  on, or when the user says so.
- Take checkpoint commits at each proved intermediate model, with a one-line
  message of what it proves.
- Neutral formal-verification framing throughout. Your own commit
  attribution. No merge, no push.

## 7. What comes after

The findings list feeds the mirror's altitude review and the W13 decision. The
natural second challenge, once the window proof exists and reuses its framing,
is the key-lifetime rules: no transport under an unconfirmed keypair or one
past `REJECT_AFTER_TIME` and `REJECT_AFTER_MESSAGES`, with time from the
recorded clock reads.
