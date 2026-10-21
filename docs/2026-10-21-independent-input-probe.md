# Independent input and single-CPU interference probe

Baseline `c63423ef`, fresh-eyes review finding 2 and upstream-tray 04.

## Selection fixed before execution

[AGENT 2026-10-21] Take the first 16 candidates returned by
`generate_wireguard(20261021, 16, max_ops=12, steered=.15, data=.15,
timers=.10, alloc=.05, lifecycle=.10, routing=.05, netns=.03)`.
Keep every candidate and every failure; no replacements. The date-derived
seed and count are fixed before running the mirror or Linux. The generator
still embodies its existing fixture grammar, wait budget and deduplication;
this is independence from the mirror's domain verdict, not an unbiased sample
of arbitrary Linux programs or packets.

The emitted JSONL has SHA-256
`563a3c011e9f9dd0ae7f8841d9c5de9fd35b1a0c274de9ef90c1afdb3ca74e48`.

`docs/probe-input-sample.py --emit` reproduces the selection. Its `--run` mode
uses the existing checker's kernel identity, Linux runs, hidden-input replay,
observation, control-flow and operand checks. It substitutes only the loader
and singleton chunking in its own process, and makes a domain-filter call an
error. A singleton per candidate prevents one unsupported case from masking
the remainder of the sample. Syntax/fixture input refusals are reported as
scope findings, not silently removed or counted as agreement.

The selection recipe is committed before its first execution. Outcomes and
the source audit follow in a separate commit.
