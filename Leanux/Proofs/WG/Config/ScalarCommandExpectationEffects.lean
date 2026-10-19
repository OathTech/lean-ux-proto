import Leanux.Proofs.WG.Config.ScalarCommandExpectationModel
import Leanux.Proofs.WG.Config.ScalarExpectationEffects
import Leanux.Proofs.WG.Config.RequestWgChainModel

/-! Pure paired-receipt and existing WG-chain composition; no operational traversal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG

theorem receiptSteps_length {rs : List RequestOrder.Receipt} {actions : List Action}
    (steps : ReceiptSteps rs actions) : rs.length=actions.length :=
by
  induction steps with
  | nil=>rfl
  | cons head tail ih=>exact congrArg Nat.succ ih

theorem receiptSteps_chain {start finish : Campaign2.State}
    {rs : List RequestOrder.Receipt} {actions : List Action}
    (chain : RequestOrder.WgLinks.Chain start rs finish)
    (steps : ReceiptSteps rs actions) :
    Steps (values start.device) actions (values finish.device) := by
  induction chain generalizing actions with
  | nil state=>
    cases steps
    exact Steps.nil _
  | @cons state final r rest before tail ih=>
    cases steps with
    | cons head later=>
      obtain ⟨attrs,kind,matched,step⟩:=head
      exact Steps.cons (by simpa only [observation,before] using step) (ih later)

theorem receiptSteps_fold {start finish : Campaign2.State}
    {rs : List RequestOrder.Receipt} {actions : List Action}
    (chain : RequestOrder.WgLinks.Chain start rs finish)
    (steps : ReceiptSteps rs actions) :
    Agrees (fold (values start.device) actions) (values finish.device) :=
  (receiptSteps_chain chain steps).fold

theorem receiptSteps_exists (rs : List RequestOrder.Receipt)
    (each : ∀r∈rs,∃action,ReceiptStep r action) :
    ∃actions,ReceiptSteps rs actions := by
  induction rs with
  | nil=>exact ⟨[],ReceiptSteps.nil⟩
  | cons r rs ih=>
    obtain ⟨action,head⟩:=each r (by simp)
    obtain ⟨actions,tail⟩:=ih (fun q member=>each q (List.mem_cons_of_mem r member))
    exact ⟨action::actions,ReceiptSteps.cons head tail⟩

theorem receiptSteps_advance {start finish : Campaign2.State} {expected : Map}
    {rs : List RequestOrder.Receipt} {actions : List Action}
    (chain : RequestOrder.WgLinks.Chain start rs finish)
    (steps : ReceiptSteps rs actions) (input : Agrees expected (values start.device)) :
    Agrees (fold expected actions) (values finish.device) :=
  (receiptSteps_chain chain steps).advance input

theorem receiptSteps_position {rs : List RequestOrder.Receipt} {actions : List Action}
    (steps : ReceiptSteps rs actions) (i : Nat) (r : RequestOrder.Receipt)
    (selected : rs[i]?=some r) :
    ∃action,actions[i]?=some action ∧ ReceiptStep r action := by
  induction steps generalizing i with
  | nil=>simp only [List.getElem?_nil] at selected;cases selected
  | @cons head action rs actions point tail ih=>
    cases i with
    | zero=>
      have same:head=r:=Option.some.inj selected
      subst r
      exact ⟨action,rfl,point⟩
    | succ i=>
      exact ih i selected

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
