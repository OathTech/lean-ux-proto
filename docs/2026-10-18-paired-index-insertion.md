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
