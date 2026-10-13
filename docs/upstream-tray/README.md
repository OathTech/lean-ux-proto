# A reader's guide to the tray

This directory holds draft reports about behaviour of the Linux kernel
that this project found while mirroring it and that might concern the
kernel's maintainers. It follows the form of the upstream tray in
`cerberus-lean-proj/lem-lean/doc/upstream-tray/` [USER 2026-10-13]. The
ranked list is [INDEX.md](INDEX.md); the drafts are the numbered files next
to it.

## 1. Where the reports come from

The repository builds an executable mirror of configured Linux code
(WireGuard, pipes, eventfd, epoll, seccomp on 6.12.110) and checks it
against the kernel running under QEMU, decision by decision, with the
kernel's hidden inputs recorded and replayed ([README](../../README.md)).
Three activities produce findings: the differential check (a trace on which
the kernel does something the mirror's reading of the C did not predict),
the correspondence audits (a fresh reader walking a mirror module against
the C), and the proof campaign over the mirror (a property that cannot be
proved because the implementation does not have it, with a counterexample).
Rule Zero of the proof charter applies throughout: the mirror follows the
code; a finding never changes the mirror.

## 2. Our stance

Every claim cites `file:line` in the pristine 6.12.110 source
(`.deps/linux` in this repository, the locked tarball), and every
reproducer is a trace in this repository's corpus whose observations were
captured on the approved oracle build named in
`kernel/identity-x86_64-net-choice.txt`, a single-CPU x86-64 configuration
(`kernel/config-x86_64-net-choice`). The classifications are our reading;
where we could not tell what the maintainers intended, the draft says so
as a question.

## 3. How to read a draft

- **Title**, **target** (the file and lines, the configuration where it
  matters), **state** and the **date drafted**.
- **Affected code**, cited as `file:line`.
- **Classification**: **TRUE BUG** (the code's evident intent and its
  behaviour disagree), **DESIGN NUANCE** (the behaviour follows from a
  documented choice; reported because its consequence seemed worth
  raising), **OBSERVABILITY GAP** (the behaviour is defensible but leaves
  no trace an operator can see), or **QUESTION**. Each with its argument.
- **Reproducer**: the trace in this corpus, the exact observation, and what
  a reader without this repository would do to see the same.
- **Expected versus actual**, **impact** (who is affected, whether an
  attacker steers it), and **how this repository found it**.
- **Provenance**: the finding and the draft are the work of AI agents
  (Claude, Anthropic) under the direction and review of a human operator.
  Any filed issue must say so.

## 4. States

**Draft** = prepared, no recorded submission. **Filed** = the upstream
reference is recorded in the draft and the index. **Withdrawn** = the
draft was found wrong or moot, with the reason kept in the file.

## 5. Reports only

The tray prepares reports, not patches: no patch branches, no pull
requests to upstream from this repository. Whether and when to file is the
user's call. The trace that shows each finding stays in the corpus, so the
behaviour remains checked as the kernel version moves.
