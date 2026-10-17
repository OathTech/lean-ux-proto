import Leanux.Proofs.WG.Config.AllowedInsertModel
import Leanux.Proofs.WG.Config.Returns
import Leanux.Proofs.WG.Noise.ComponentFrames
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
theorem allocRootNode_effect (n : AipNode) (d : Device) :
    Ensures (liftAip (allocNode .allocNode190 n)) (fun g => g.dev = some d)
      (fun result g => match result with
        | none => g.dev = some d
        | some id => id = d.nextNode ∧ g.dev = some
            { d with nextNode := id + 1, nodes := d.nodes.insert id n }) := by
  intro g ambient result final after device run
  cases halloc : (AmbientM.hiddenAlloc .allocNode190).run ambient with
  | error stop =>
    simp [liftAip, allocNode, getDev, device, hiddenAlloc, halloc] at run
    cases run
  | ok out =>
    rcases out with ⟨allocated, next⟩
    cases allocated <;>
      simp [liftAip, allocNode, getDev, device, hiddenAlloc, halloc, modifyDev] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals simp

theorem add_empty_root_effect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (resident : d.peers[pid]? = some p)
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4) :
    Ensures (add (allowedRoot v4) (allowedBits v4) addr cidr (some pid))
      (fun g => g.dev = some d)
      (fun ret g => (ret = -ENOMEM ∧ g.dev = some d) ∨
        (ret = 0 ∧ g.dev = some (emptyRootInserted v4 d pid p addr cidr))) := by
  intro g ambient result final after device run
  cases v4 <;>
    simp only [allowedRootValue, allowedBits, allowedRoot, Bool.false_eq_true, ite_false, ite_true] at root width run ⊢
  all_goals
    have haip {α : Type} (x : AipM α) : (liftM x : WG.M α) = liftAip x := rfl
    simp [add, branch, AmbientM.branch, branchCmp, AmbientM.branchCmp, haip, slotGet, liftAip, getDev, modifyDev, device,
      root, Nat.not_lt.mpr width, allocNode, hiddenAlloc] at run
    generalize choice : (AmbientM.hiddenAlloc .allocNode190).run _ = out at run
    cases out with
    | error stop => cases run
    | ok out =>
      rcases out with ⟨allocated, next⟩
      cases allocated <;>
        simp [listAddTail, connectNode, getDev, getPeer, setPeer,
          getNode, setNode, slotSet, modifyDev, newNode] at run
      case false =>
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact Or.inl ⟨rfl, rfl⟩
      case true =>
        have hok {α β : Type} (x : α) (f : α → Except Stop β) :
            ((Except.ok x : Except Stop α) >>= f) = f x := rfl
        simp [hok, resident] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact Or.inr ⟨rfl, rfl⟩
theorem setAllowedip_empty_root_effect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (resident : d.peers[pid]? = some p)
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4) :
    Ensures (setAllowedip pid (allowedAttrs v4 addr cidr)) (fun g => g.dev = some d)
      (fun ret g => ∃ final, g.dev = some final ∧ EmptyRootInsertEffect v4 d pid p addr cidr ret final) := by
  have ha := add_empty_root_effect v4 (insertSequenceDevice d) pid p addr cidr resident root width
  intro g ambient result final after device run
  cases v4
  all_goals
    simp only [allowedBits, allowedRoot, Bool.false_eq_true, ite_false, ite_true] at ha width
    simp [setAllowedip, allowedAttrs, AF_INET, AF_INET6, branch, AmbientM.branch,
      WG.andM, WG.orM, Leanux.WG.insert, modifyDev, device, width] at run
    have effect := ha _ _ result final after rfl run
    rcases effect with ⟨rfl, state⟩ | ⟨rfl, state⟩
    · exact ⟨_, state, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, state, Or.inr ⟨rfl, rfl⟩⟩
end Leanux.Proofs.WG.Config
