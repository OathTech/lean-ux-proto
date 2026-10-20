import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxRepaymentSource

/-! Repayment preserves packet accounting through key accesses and the
counted peer-release source. Its pending receipt remains explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations

inductive Evidence (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (h : List CausalJournal.Event) (w : World) : Prop where
  | accounted (next : Ledger) (step : Staged.Obligations.Step ledger next)
      (account : Accounted h next debts locals w.wg)
  | peer (evidence : NestedPeer.Evidence ledger debts locals h w)

/-- Security: cached-key repayment preserves the same packet ledger;
peer retirement uses the actual counted release and retains its precise
pending receipt before emission. -/
theorem Point.evidence (before : Accounted h ledger debts locals w.wg)
    (point : Point pid key w h u middle) : Evidence ledger debts locals middle u := by
  cases point with
  | entry=>exact .accounted ledger (.refl _) before
  | keyAccess point=>exact .accounted ledger (.refl _) (point.accounted before)
  | peer paid point=>exact .peer (point.evidence (KeyAccess.returned before paid))
  | returned performed=>
    have returned:=Converse.Dead.repay_cases pid key before
    change runPrefix (DeadEntry.repay pid key) w h=_ at performed
    rw [performed] at returned
    obtain ⟨next,steps,account⟩:=returned.entry
    exact .accounted next steps account

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
