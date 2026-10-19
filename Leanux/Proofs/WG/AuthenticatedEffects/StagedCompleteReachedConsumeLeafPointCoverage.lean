import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointReceive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointResidual

/-! Each original helper branch has its fixed canonical source witness.
Interior coverage is conditional precisely on the named deeper child families;
native boundaries and original successful prefixes have concrete carrier frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {native inside : ChildPoints} {Good : History → World → Prop}

abbrev Boundary : ChildPoints := fun _ _ _ _ _ => False

theorem boundary_carrier (point : Point Boundary shape w h site u middle)
    (before : Carrier h w) : Carrier middle u := by
  induction point with
  | entry shape => exact before
  | returned shape performed => exact shape.normal before performed
  | interior token point => exact False.elim point
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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
