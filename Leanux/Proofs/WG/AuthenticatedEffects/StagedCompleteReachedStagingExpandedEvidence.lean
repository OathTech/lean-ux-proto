import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingExpandedSource

/-! The expanded staging family derives each semantic phase from its one
original ledger. Native allocation aliases and pending disposal receipts
remain explicit rather than being called idle packet ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier StagingComposition

inductive Evidence (root : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) : List Event → WGWorld → Ambient → Prop where
  | phase (evidence : StagingPhase.Evidence root debts locals h w a) : Evidence root debts locals h w a
  | allocation (current : Ledger) (steps : Staged.Obligations.Step root current)
      (cut : Allocation.Interval h current debts locals generation pid peer position kid packets origin a count items w) :
      Evidence root debts locals h w a
  | creation (evidence : CreateExpanded.Evidence root debts locals pid items h w) : Evidence root debts locals h w.wg w.ambient

/-- Every declared staging cut conserves its original packet lineage,
including silent allocation and disposal intervals before their receipts. -/
theorem Point.evidence (point : Point pid w a h v b last)
    (before : Accounted h ledger debts locals w) : Evidence ledger debts locals last v b := by
  cases point with
  | canonical point=>exact .phase ((StagingPhase.staging_covers before pid a).point point)
  | reserve selected call point=>
    obtain ⟨after,_,steps,ready,_⟩:=reserve_from_selection before selected call point
    exact .phase (.selected after steps ready)
  | repayment selected guarded call point=>
    obtain ⟨after,_,steps,ready,_⟩:=repayment_from_rejection before selected guarded call point
    exact .phase (.selected after steps ready)
  | queued selected guarded prefixRun restoreRun point=>
    obtain ⟨_,_,steps,account,_⟩:=queued_from_restoration before selected guarded prefixRun restoreRun point
    exact .phase (.accounted _ steps account)
  | allocation selected guarded _ path=>
    obtain ⟨after,_,steps,cut,_⟩:=allocation_from_submission before selected guarded path
    exact .allocation after steps cut
  | allocationNative selected guarded _ point=>
    obtain ⟨count,items,rfl,path⟩ := point.path
    obtain ⟨after,_,steps,cut,_⟩ := allocation_from_submission before selected guarded path
    exact .allocation after steps cut
  | creation selected guarded allocated point=>
    exact .creation (all_create_from_submission before selected guarded allocated point).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
