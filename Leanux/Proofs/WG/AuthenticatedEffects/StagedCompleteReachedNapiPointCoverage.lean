import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointResidual

/-! Every original NAPI and RX/stack branch has the fixed canonical source witness.
Interior coverage is conditional precisely on the five named child families;
native boundaries and original successful prefixes have concrete carrier frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {native inside : ChildPoints} {Good : History → World → Prop}

abbrev Boundary : ChildPoints := fun _ _ _ _ _ => False

theorem boundary_carrier (point : Point Boundary shape w h site u middle)
    (before : Carrier h w) : Carrier middle u := by
  induction point with
  | entry shape => exact before
  | returned shape performed => exact shape.normal before performed
  | interior token point => exact False.elim point
  | metadata point =>
      obtain ⟨ledger,account⟩ := before
      exact ⟨ledger,account.same_view point.frame⟩
  | rx point =>
      obtain ⟨ledger,account⟩ := before
      exact ⟨ledger,account.same_view point.frame⟩
  | free point =>
      obtain ⟨ledger,account⟩ := before
      exact ⟨ledger,NapiMetadata.free_account point account⟩
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)
  | marked label point ih => exact ih before

def Remainders (children : ChildContracts native inside Good) {α : Type} {action : PrefixM Event α}
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point native shape w h site u middle →
    ∃ remaining : PrefixM Event α, Residual children shape w h site u middle remaining

theorem source_covered (carrierGood : ∀ h w, Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (shape : Shape action)
    (before : Carrier h w)
    (performed : runPrefix action w h = (result,last)) :
    Execution shape w h result last ∧ Covered native Good shape w h ∧ Remainders children shape w h :=
  ⟨execution_cases shape performed,covered carrierGood children shape before,
    fun _ _ _ point => point.residual children⟩

theorem softirq_cases
    (performed : runPrefix (Driver.softirqObserved hooks) w h = (result,last)) :
    Execution softirqShape w h result last := execution_cases _ performed

theorem inline_cases
    (performed : runPrefix (Driver.inlinePollObserved hooks) w h = (result,last)) :
    Execution inlineShape w h result last := execution_cases _ performed

theorem irq_cases
    (performed : runPrefix (Driver.irqExitObserved hooks) w h = (result,last)) :
    Execution irqShape w h result last := execution_cases _ performed

theorem poll_cases (pid : PeerId) (budget : Nat)
    (performed : runPrefix (Driver.nativePollObserved hooks pid budget) w h = (result,last)) :
    Execution (pollShape pid budget) w h result last := execution_cases _ performed

theorem stack_cases (bytes : List UInt8)
    (performed : runPrefix (Driver.stackObserved hooks bytes) w h = (result,last)) :
    Execution (stackShape bytes) w h result last := execution_cases _ performed

theorem softirq_covered (carrierGood : ∀ h w, Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (Driver.softirqObserved hooks) w h = (result,last)) :
    Execution softirqShape w h result last ∧ Covered native Good softirqShape w h ∧
      Remainders children softirqShape w h := source_covered carrierGood children _ before.1 performed

/-- The real scope receipt precedes the buffered entry's own bytes. A later
stack failure retains this same native world and the original entered event. -/
theorem tagged_body_entry (entry : GroOccurrence.Entry) :
    Point inside (taggedShape entry) w h (.marked (.tagged entry) (.right (.left .entry)))
      w (h ++ [.scope (.entered ⟨h.length,.stackInput entry⟩)]) :=
  .marked _ (.right (.native (.enter (.stackInput entry))) _ rfl (.left _ (.entry _)))

/-- A fixed failing source atom never creates a returned world or reaches
its original continuation. The precise error and unchanged journal remain. -/
theorem failed_cases {α β : Type} {body : PrefixM Event α} (failure : Failure body) (next : α → PrefixM Event β) (w : World) (h : History) :
    ∃ reason, runPrefix (body >>= next) w h = (.error reason,h) := by
  obtain ⟨reason,run⟩ := failure.run w h
  exact ⟨reason,by rw [runPrefix_bind,run]⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
