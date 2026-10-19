import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseKeepalive

/-! Original-entry certificates for the two fixed canonical source trees.
Semantic coverage is derived, not supplied by a caller. It includes stopped
paths and every saved receipt boundary, with literal continuations at points.
Finite allocation/create/queued/repayment children remain their named source
contracts: allocation aliases and expanded CreatePhase points are exported
separately. This is local coverage, not initialized global native coverage. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points
set_option maxHeartbeats 600000

theorem staging_source_phases (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    let actual:=runWGPrefix (Driver.stagingObserved hooks pid) w a h
    Execution (stagingShape pid) w a h actual.1 actual.2 ∧
      Covers (Evidence ledger debts locals) (stagingShape pid) w a h :=
  ⟨Staging.Points.staging_cases pid w a h,staging_covers before pid a⟩

theorem keepalive_source_phases (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    let actual:=runWGPrefix (Driver.keepaliveObserved hooks pid) w a h
    Execution (keepaliveShape pid) w a h actual.1 actual.2 ∧
      Covers (KeepaliveEvidence h ledger debts locals pid w a) (keepaliveShape pid) w a h :=
  ⟨Staging.Points.keepalive_source_cases pid w a h,keepalive_covers before pid a⟩

/-- The failure retains its actual reason/history and the same source phase
certificate. There is deliberately no post-error native world. -/
theorem staging_stopped_phases (before : Accounted h ledger debts locals w)
    (failed : runWGPrefix (Driver.stagingObserved hooks pid) w a h=(.error reason,last)) :
    Execution (stagingShape pid) w a h (.error reason) last ∧
      Covers (Evidence ledger debts locals) (stagingShape pid) w a h := by
  have actual:=staging_source_phases before pid a
  dsimp only at actual
  rw [failed] at actual
  exact actual

theorem keepalive_stopped_phases (before : Accounted h ledger debts locals w)
    (failed : runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=(.error reason,last)) :
    Execution (keepaliveShape pid) w a h (.error reason) last ∧
      Covers (KeepaliveEvidence h ledger debts locals pid w a) (keepaliveShape pid) w a h := by
  have actual:=keepalive_source_phases before pid a
  dsimp only at actual
  rw [failed] at actual
  exact actual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
