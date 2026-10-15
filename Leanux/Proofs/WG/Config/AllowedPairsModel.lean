import Leanux.WG.AllowedIps

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- A representation-shape premise only: no ownership, reachability, or acyclicity. -/
def NodePairs (d : Device) : Prop :=
  ∀ (id : NodeId) (n : AipNode), d.nodes[id]? = some n → n.bit.size = 2

theorem array_pair_shape {α : Type} (a : Array α) (size : a.size = 2) :
    ∃ left right, a = #[left, right] := by
  rcases a with ⟨items⟩
  cases items with
  | nil => simp at size
  | cons left rest =>
    cases rest with
    | nil => simp at size
    | cons right rest =>
      cases rest with
      | nil => exact ⟨left, right, rfl⟩
      | cons item rest => simp at size

end Leanux.Proofs.WG.Config
