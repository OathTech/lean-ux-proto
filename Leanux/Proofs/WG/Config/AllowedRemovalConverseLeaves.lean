import Leanux.Proofs.WG.Config.AllowedPairsEffects
import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem slotSet_effect_pairs (d : Device) (slot : Slot) (value : Option NodeId)
    (pairs : NodePairs d) :
    Ensures (liftAip (slotSet slot value)) (fun g => g.dev = some d)
      (fun _ g => ∃ final, g.dev = some final ∧ SlotWrite d slot value final) := by
  intro g ambient result final after device run
  cases slot with
  | root4 =>
    simp [liftAip, slotSet, getDev, modifyDev, device] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨_, rfl, .root4 d value⟩
  | root6 =>
    simp [liftAip, slotSet, getDev, modifyDev, device] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨_, rfl, .root6 d value⟩
  | child parent bit =>
    cases resident : d.nodes[parent]? with
    | none =>
      simp [liftAip, slotSet, getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some n =>
      by_cases valid : bit ≤ 1
      · simp [liftAip, slotSet, getNode, setNode, getDev, modifyDev, device,
          resident, Nat.not_lt.mpr valid] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨_, rfl, .child d parent bit n value resident valid (pairs parent n resident)⟩
      · simp [liftAip, slotSet, getNode, getDev, device, resident,
          Nat.lt_of_not_ge valid, invariant, AmbientM.invariant] at run
        cases run

theorem reparentSibling_effect (d : Device) (sibling : Option NodeId) (slot : Slot) :
    Ensures (reparentSibling sibling slot) (fun g => g.dev = some d)
      (fun _ g => ∃ final, g.dev = some final ∧ ChildReparent d sibling slot final) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases sibling with
  | none =>
    simp [reparentSibling, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, device, .none d slot⟩
  | some id =>
    cases resident : d.nodes[id]? with
    | none =>
      simp [reparentSibling, reparentNode, branch, AmbientM.branch,
        aipLift, liftAip, getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some n =>
      simp [reparentSibling, reparentNode, branch, AmbientM.branch,
        aipLift, liftAip, getNode, setNode, getDev, modifyDev, device, resident] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨_, rfl, .some d id n slot resident⟩

theorem freeNode_effect (d : Device) (id : NodeId) :
    Ensures (liftAip (freeNode id)) (fun g => g.dev = some d)
      (fun _ g => (∃ n, d.nodes[id]? = some n) ∧
        g.dev = some {d with nodes := d.nodes.erase id}) := by
  intro g ambient result final after device run
  cases resident : d.nodes[id]? with
  | none =>
    simp [liftAip, freeNode, getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some n =>
    simp [liftAip, freeNode, getNode, getDev, modifyDev, device, resident] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨⟨n, rfl⟩, rfl⟩

theorem leafParentDecision_effect (d : Device) (slot : Slot) :
    Ensures (leafParentDecision slot) (fun g => g.dev = some d)
      (fun choice g => g.dev = some d ∧ ParentChoice d slot choice) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases slot with
  | root4 =>
    simp [leafParentDecision, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨device, .root4 d⟩
  | root6 =>
    simp [leafParentDecision, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨device, .root6 d⟩
  | child parent bit =>
    cases resident : d.nodes[parent]? with
    | none =>
      simp [leafParentDecision, branch, AmbientM.branch, aipLift, liftAip, getNode,
        getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some n =>
      simp [leafParentDecision, branch, AmbientM.branch, aipLift, liftAip, getNode,
        getDev, modifyDev, device, resident] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, .child d parent bit n resident⟩

/-- The original full-state law remains generic over arbitrary product state. -/
theorem removal_returns_ensures {α σ : Type} {a : StateT σ (Except Stop) α} {P : σ → Prop}
    {Q : α → σ → Prop} (returns : Config.Product.Returns a P Q) : Noise.Product.Ensures a P Q := by
  intro w result final pre run
  obtain ⟨r, v, actual, post⟩ := returns w pre
  rw [run] at actual
  cases actual
  exact post

/-- The native companion quantifies every ambient realization as well. -/
theorem removal_returns_ensures_native {α σ : Type} {a : StateT σ AmbientM α} {P : σ → Prop}
    {Q : α → σ → Prop} (returns : Returns a P Q) : Ensures a P Q := by
  intro g ambient result final after pre run
  obtain ⟨r, v, next, actual, post⟩ := returns g ambient pre
  rw [run] at actual
  cases actual
  exact post

theorem reparentNode_effect (d : Device) (id : NodeId) (slot : Slot) :
    Ensures (reparentNode id slot) (fun g => g.dev = some d)
      (fun _ g => ∃ n, d.nodes[id]? = some n ∧
        g.dev = some (writeNode d id {n with parent := slot})) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases resident : d.nodes[id]? with
  | none =>
    simp [reparentNode, aipLift, liftAip, getNode, getDev, device, resident,
      invariant, AmbientM.invariant] at run
    cases run
  | some n =>
    simp [reparentNode, aipLift, liftAip, getNode, setNode, getDev, modifyDev, device, resident] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨n, rfl, rfl⟩

theorem unaryAfterLink_effect (side : Bool) (d : Device) (id : NodeId) :
    Ensures (unaryAfterLink side id) (fun g => g.dev = some d)
      (fun result g => result = .yield () ∧ (∃ n, d.nodes[id]? = some n) ∧
        g.dev = some {d with nodes := d.nodes.erase id}) := by
  intro g ambient result final after device run
  have aipLift {α : Type} (a : AipM α) : (monadLift a : WG.M α) = liftAip a := rfl
  cases resident : d.nodes[id]? with
  | none =>
    cases side <;>
      simp [unaryAfterLink, branch, AmbientM.branch, aipLift, liftAip, freeNode,
        getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
    all_goals cases run
  | some n =>
    cases side <;>
      simp [unaryAfterLink, branch, AmbientM.branch, aipLift, liftAip, freeNode,
        getNode, getDev, modifyDev, device, resident] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact ⟨rfl, ⟨n, rfl⟩, rfl⟩

end Leanux.Proofs.WG.Config
