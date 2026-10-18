# Paired index insertion: execution report

Status: started on `task/binary-pair-runner` at baseline `41675f86` under the
[charter](2026-10-18-charter-paired-index-insertion.md).

Start: **2026-10-18 17:23:07 UTC**. Reassessment if incomplete:
**2026-10-19 17:23:07 UTC**. Supporting runtime optimization allowance: two
focused hours, zero used. No merge, push or changes to mirror/oracle/global state.

Mirror pin `cb2348e` now lags main `783510e850e187549cbb9380e53790e1ed232c77`.
Private Kraken remains clean at `7ebba06a30eaf08c10b26b28ca14bfee1c791576`,
Lean v4.35.0; approved s4 ELF SHA256
`16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774`.
The previous subsystem's external export gate is pending; its user command has
been requested. A separate read-only trust-surface review is in progress.

Initial inspection confirms 109 insertion instructions. The common unlink
segment, finite bucket decoder and storage frames are reuse candidates.
The new service boundary is `get_random_u32`, whose wrapper calls the raw
entropy provider and `kcov_choice_ip`; input coupling must remain explicit and
must not assume arbitrary draws from a fixed deterministic machine state.

No new theorem or passing insertion test is claimed at this start checkpoint.

## Independent review disposition

The [surface review](2026-10-18-review-paired-index-subsystem.md) permits the
insertion extension on the existing conditional sequential foundation. It
found no circular future-Pre/execution premise. Each finding is retained:

- **R1, medium:** the old sequence permission domain covers arbitrary prepared
  heaps. The insertion extension will restrict the *permission quantifier* to
  a readiness domain derived by composition. This weakens the environment
  hypothesis, not the source domain or R. The prior exported theorem is unchanged.
- **R2, medium:** the old returning-history premise also covers histories that
  returned earlier and later reached the same boundary again. This is a stronger
  assumption, not a first-return safety result. It remains explicitly open while
  the insertion execution/history boundary is designed. Do not describe the
  current premise as excluding all executed caller continuations. A repair must
  derive a first-boundary property rather than assume future R or termination.
- Intermediate Ready is established and used by old composition, but absent
  from its exported per-call Observed relation. The extended theorem should
  expose the paired boundary states if its claimed observations require them.

The interruption left only the review document uncommitted. It was preserved,
including that untracked file, at recovery ref
`refs/recovery/binary-pair-runner/20261018T172711Z`; branch HEAD was not changed
by preservation. No other worktree was modified. The preceding external export
was observed running under the user's command; acceptance awaits its result.
