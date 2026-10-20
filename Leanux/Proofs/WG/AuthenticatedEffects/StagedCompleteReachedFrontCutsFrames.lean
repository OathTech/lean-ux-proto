import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedFrontCutsSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrimPointsFrames

/-! The original front entry supplies trim tickets and the pending birth
receipt. A native splice does not pretend that its still-unrecorded birth
already belongs to the journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FrontCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Transmit Transmit.Front Transmit.Front.Residual

theorem input_account (input : Input) (before : Accounted h ledger debts locals w) :
    Accounted (inputHistory input h) ledger debts locals w :=
  before.append_quiet [.transmitInput input]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)

inductive Evidence (initial : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) : History → WGWorld → Ambient → Prop where
  | accounted (ledger : Ledger) (step : Staged.Obligations.Step initial ledger)
      (account : Accounted h ledger debts locals w) : Evidence initial debts locals h w a
  | trim (point : TrimPoints.Evidence h initial debts locals pid w a) : Evidence initial debts locals h w a
  | pendingRouted (before : Accounted h initial debts locals w)
      (path : Transmit.Path input h w a value v b middle) : Evidence initial debts locals middle v b

/-- Security: overflow points keep their original pending tickets, and a
splice keeps the actual pending routed receipt that will create its births. -/
theorem Point.evidence (before : Accounted h ledger debts locals w)
    (point : Point input w a h v b middle) : Evidence ledger debts locals middle v b := by
  cases point with
  | entry=>exact .accounted _ (.refl _) before
  | inputMarked=>exact .accounted _ (.refl _) (input_account input before)
  | selected path=>exact .accounted _ (.refl _) (path.accounted (input_account input before))
  | trim selected point=>exact .trim (point.evidence (selected.accounted (input_account input before)))
  | trimRecorded selected performed=>
      obtain ⟨after,account,step,_⟩:=trim_account (selected.accounted (input_account input before)) performed
      exact .accounted after step account
  | spliced selected trim splice=>exact .pendingRouted before (selected_splice selected trim splice)
  | preReceipt path=>exact .pendingRouted before path

theorem RootPoint.evidence (before : Accounted h ledger debts locals w.wg)
    (point : RootPoint input w h u middle) : Evidence ledger debts locals middle u.wg u.ambient := by
  cases point with
  | source point=>exact point.evidence before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FrontCuts
