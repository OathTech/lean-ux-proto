import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeInterpretation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeRecordsAccounts

/-! Receipt intervals complete by their fixed records alone. Only partial
allocation and an active trim loop still require native progress. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive Transient : History → WGWorld → Prop where
  | allocating (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v) :
      Transient h v
  | trimLoop (cut : Transmit.Front.Residual.TrimCut h ledger debts locals pid w a n v b) : Transient h v
  | trimDrop (cut : Transmit.Front.Residual.TrimCut h ledger debts locals pid w a n v b)
      (device : v.dev=some d) (resident : d.peers[pid]?=some p)
      (excess : p.staged.length>MAX_STAGED_PACKETS) : Transient h (Transmit.Front.Residual.droppedWorld pid p d v)

def Frontier (h : History) (w : WGWorld) : Prop :=
  Stable h w ∨ (∃last,RecordsDue h w last ∧ Stable last w) ∨ Transient h w

theorem Frontier.of_records (due : RecordsDue h w last) : Frontier h w :=
  Or.inr (Or.inl ⟨last,due,due.accounted⟩)

theorem Interval.frontier (cut : Interval h w) : Frontier h w := by
  cases cut with
  | taking cut=>exact .of_records (.taking cut)
  | restoring cut=>exact .of_records (.restoring cut)
  | allocating cut=>exact Or.inr (Or.inr (.allocating cut))
  | keepalive before device resident empty allocated=>exact .of_records (.keepalive before device resident empty allocated)
  | purge before device resident=>exact .of_records (.purge before device resident)
  | release before native=>exact .of_records (.release before native)
  | nestedRelease before native=>exact .of_records (.nestedRelease before native)
  | nestedErase before checked=>exact .of_records (.nestedErase before checked)
  | createFree cut phase=>exact .of_records (.createFree cut phase)
  | deadFree waiting=>exact .of_records (.deadFree waiting)
  | socket waiting=>exact .of_records (.socket waiting)
  | trimLoop cut=>exact Or.inr (Or.inr (.trimLoop cut))
  | trimDrop cut device resident excess=>exact Or.inr (Or.inr (.trimDrop cut device resident excess))
  | trimReturned before performed=>exact .of_records (.trimReturned before performed)
  | routed before path=>exact .of_records (.routed before path)

theorem Classified.frontier (cut : Classified h w) : Frontier h w := by
  rcases cut with current|interval
  · exact Or.inl current
  · exact interval.frontier

/-- Security: each declared initialized point has a current complete ticket
account, the original pending records that restore it on the same native
world, or an actual partial allocation or trim interval. There is no incoming
accounting premise; finer native source coverage remains separate. -/
theorem initialized_frontier (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    Runner.Points.Covered (children nativeConsume nativeNapi nativeWorker nativeWork nativeDispatch)
      (fun h w=>Frontier h w.wg) (Runner.Points.executeShape trace placeholders) [] := by
  intro site u middle point
  exact (initialized_classification trace placeholders site u middle point).frontier

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
