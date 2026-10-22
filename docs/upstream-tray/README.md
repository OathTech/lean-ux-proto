# A reader's guide to the tray

This directory holds draft observations and questions about Linux behavior
found while building and checking the mirror. The
[project health warning](../../README.md) applies. These are research drafts,
not confirmed vulnerabilities or upstream determinations. The
[index](INDEX.md) lists each report's classification and evidence.

## 1. Where the reports come from

The repository builds an executable mirror of configured Linux code
(WireGuard, pipes, eventfd, epoll, seccomp on 6.12.110) and checks it
against the kernel running under QEMU using observable results, declared
branch witnesses and comparison operands, with recorded inputs replayed ([README](../../README.md)).
Three activities produce findings: the differential check (a trace on which
the kernel does something the mirror's reading of the C did not predict),
the correspondence audits (a fresh reader walking a mirror module against
the C), and the proof campaign over the mirror (counterexamples to proposed properties).
A failed proof alone is not a kernel finding: first check the statement and
the mirror, then seek evidence in the C or kernel execution. The mirror must
follow the implementation; it is not changed to make a desired theorem true.

## 2. Our stance

Reports cite the pristine Linux 6.12.110 source, available from the locked
tarball in `.deps/linux`. Reports 01 and 02 include corpus traces exercised
on the instrumented single-CPU x86-64 oracle. Reports 03 and 04 concern races
outside this fixture and explicitly have no reproducer in this corpus; they
are based on source analysis and describe what would need to be tested.

Classifications are the authors' assessment, not maintainer confirmation.
The evidence and remaining questions in each report matter more than the
label. See the [comparison guide](../../correspondence/README.md) for what
an oracle run establishes and what it does not.

## 3. How to read a draft

- **Title**, **target** (the file and lines, the configuration where it
  matters), **state** and the **date drafted**.
- **Affected code**, cited as `file:line`.
- **Classification**: **TRUE BUG** (the code's evident intent and its
  behaviour disagree), **DESIGN NUANCE** (the behaviour follows from a
  documented choice; reported because its consequence seemed worth
  raising), **OBSERVABILITY GAP** (the behaviour is defensible but leaves
  no trace an operator can see), or **QUESTION**. Each with its argument.
- **Reproducer or evidence gap**: the corpus trace and observed result where
  available; otherwise an explicit statement that the behavior has not been
  reproduced here, and a proposed way to investigate it.
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
user's call. Where a reproducing trace exists, it stays in the corpus as a regression
case. A source-only report does not acquire execution evidence from being
listed here.
