import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointResidual

/-! Every original iteration branch has the fixed canonical source witness.
Interior coverage is conditional precisely on the eight named child families;
native boundaries and original successful prefixes have concrete carrier frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {native inside : ChildPoints} {Good : History → World → Prop}

abbrev Boundary : ChildPoints := fun _ _ _ _ _ => False

theorem boundary_carrier (point : Point Boundary shape w h site u middle)
    (before : CompleteProduct.Carrier h w) : CompleteProduct.Carrier middle u := by
  induction point with
  | entry shape => exact before
  | returned shape performed => exact shape.normal before performed
  | interior token point => exact False.elim point
  | peer point => exact Reads.peer_carrier point before
  | packet point => exact Reads.packet_carrier point before
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)
  | marked label point ih => exact ih before

def Remainders (children : ChildContracts native inside Good) {α : Type} {action : PrefixM Event α}
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point native shape w h site u middle →
    ∃ remaining : PrefixM Event α, Residual children shape w h site u middle remaining

theorem source_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (shape : Shape action)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h = (result,last)) :
    Execution shape w h result last ∧ Covered native Good shape w h ∧ Remainders children shape w h :=
  ⟨execution_cases shape performed,covered carrierGood children shape before,
    fun _ _ _ point => point.residual children⟩

theorem iteration_cases (activation : Activation)
    (performed : runPrefix (Driver.iterationObserved hooks activation) w h = (result,last)) :
    Execution (iterationShape activation) w h result last := execution_cases _ performed

theorem iteration_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (activation : Activation)
    (before : CompleteProduct.Carrier h w)
    (performed : runPrefix (Driver.iterationObserved hooks activation) w h = (result,last)) :
    Execution (iterationShape activation) w h result last ∧ Covered native Good (iterationShape activation) w h ∧
      Remainders children (iterationShape activation) w h := source_covered carrierGood children _ before performed

theorem crypt_ahead_cases (pid : PeerId)
    (performed : runPrefix (Driver.cryptAheadObserved hooks pid) w h = (result,last)) :
    Execution (aheadShape pid) w h result last := execution_cases _ performed

theorem encrypt_cases
    (performed : runPrefix (Driver.encryptIterObserved hooks) w h = (result,last)) :
    Execution encryptShape w h result last := execution_cases _ performed

theorem decrypt_cases
    (performed : runPrefix (Driver.decryptIterObserved hooks) w h = (result,last)) :
    Execution decryptShape w h result last := execution_cases _ performed

theorem receive_cases
    (performed : runPrefix (Driver.receiveIterObserved hooks) w h = (result,last)) :
    Execution receiveShape w h result last := execution_cases _ performed

/-- Poll selection and NAPI are the original successful left prefixes. The
encryption child receives that exact selected item and reached world. -/
theorem encrypt_item_entry (polled : runPrefix hooks.poll w h = (.ok (item,u),middle))
    (napi : runPrefix (Driver.softirqObserved hooks) u middle = (.ok ((),v),last)) :
    Point inside encryptShape w h
      (.marked .encrypt (.right (.right (.marked (.encryptTail item) (.left .entry))))) v last :=
  .marked _ (.right (.child .poll) _ polled
    (.right (.child .softirq) _ napi (.marked _ (.left _ (.entry _)))))

/-- The prepare callback's returned owner is passed unchanged to IRQ and the
subsequent actual reference release. No release child exists on the none arm. -/
theorem decrypt_release_entry
    (napi : runPrefix (Driver.softirqObserved hooks) w h = (.ok ((),u),middle))
    (prepared : runPrefix hooks.prepare u middle = (.ok (some pid,v),last))
    (irq : runPrefix (Driver.irqExitObserved hooks) v last = (.ok ((),x),ending)) :
    Point inside decryptStepShape w h (.right (.right (.right (.left .entry)))) x ending :=
  .right (.child .softirq) _ napi (.right (.child .prepare) _ prepared
    (.right (.child .irqExit) _ irq (.left _ (.entry _))))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
