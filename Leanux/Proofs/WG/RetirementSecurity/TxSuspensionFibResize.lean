import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFibCore

/-! Mutual native resize recursion retains suspended activations at every fuel
index. Exhaustion remains the original explicit stop. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
open Leanux Leanux.Net Leanux.Net.Fib
open Leanux.Proofs.Framing Lifetimes Queues

theorem resize_family (fuel : Nat) :
    (∀tp i,Keeps (resizeAt fuel tp i)) ∧
    (∀tp i old tn freed,Keeps (replace fuel tp i old tn freed)) ∧
    (∀tp i old,Keeps (inflate fuel tp i old)) ∧
    (∀tp i old,Keeps (halve fuel tp i old)) := by
  induction fuel with
  | zero=>
    refine ⟨?_,?_,?_,?_⟩
    · intro tp i; rw [resizeAt]; exact exhausted _
    · intro tp i old tn freed; rw [replace]; exact exhausted _
    · intro tp i old; rw [inflate]; exact exhausted _
    · intro tp i old; rw [halve]; exact exhausted _
  | succ fuel ih=>
    obtain ⟨resize_previous,replace_previous,inflate_previous,halve_previous⟩:=ih
    refine ⟨?_,?_,?_,?_⟩
    · intro tp i
      rw [resizeAt]
      suspension_source [] using [branch,compare,invariant,should_inflate,should_halve,
        should_collapse,collapse_node,inflate_previous,halve_previous]
    · intro tp i old tn freed
      rw [replace]
      suspension_source [] using [branch,put_root,update_children,tnode_free,tnode_full,resize_previous]
    · intro tp i old
      rw [inflate]
      suspension_source [] using [branch,invariant,tnode_new,tnode_full,put_child,tnode_free,replace_previous]
    · intro tp i old
      rw [halve]
      suspension_source [] using [branch,invariant,tnode_new,put_child,tnode_free,replace_previous]

theorem resize_node (fuel : Nat) (tp : KeyVector) (i : Nat) : Keeps (resizeAt fuel tp i) :=
  (resize_family fuel).1 tp i

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
