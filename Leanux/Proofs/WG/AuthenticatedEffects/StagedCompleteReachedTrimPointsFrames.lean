import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrimPointsSource

/-! Accounting is derived at fixed overflow points from the actual entry.
Removed tickets remain pending until the original overflow receipt, including
the interval in which queue removal precedes its counter charge. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.TrimPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Residual

inductive Evidence (h : List Event) (ledger : Ledger)
    (debts : List AllocatedObligation.CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (pid : PeerId) : WGWorld → Ambient → Prop where
  | accounted (before : Accounted h ledger debts locals w) : Evidence h ledger debts locals pid w a
  | iteration (cut : TrimCut h ledger debts locals pid w a n v b) : Evidence h ledger debts locals pid v b
  | guarded (cut : TrimCut h ledger debts locals pid w a n v b)
      (device : v.dev=some d) (resident : d.peers[pid]?=some p) :
      Evidence h ledger debts locals pid v (clock b (decide (p.staged.length>MAX_STAGED_PACKETS)))
  | dropped (cut : TrimCut h ledger debts locals pid w a n v b)
      (device : v.dev=some d) (resident : d.peers[pid]?=some p)
      (excess : p.staged.length>MAX_STAGED_PACKETS) :
      Evidence h ledger debts locals pid (droppedWorld pid p d v) (clock b true)
  | returned (before : Accounted h ledger debts locals w)
      (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) : Evidence h ledger debts locals pid v b

/-- Security: every removed queue position retains its original pending
ticket until the actual overflow receipt, even before its counter charge. -/
theorem Point.evidence (before : Accounted h ledger debts locals w)
    (point : Point pid w a v b) : Evidence h ledger debts locals pid v b := by
  cases point with
  | entry=>exact .accounted before
  | iteration device resident path=>exact .iteration ⟨before,path,_,_,device,resident⟩
  | guarded device resident path current peer=>exact .guarded ⟨before,path,_,_,device,resident⟩ current peer
  | dropped device resident path current peer excess=>exact .dropped ⟨before,path,_,_,device,resident⟩ current peer excess
  | returned performed=>exact .returned before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.TrimPoints
