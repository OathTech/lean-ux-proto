import Leanux.Proofs.WG.Roaming.RemoteRetentionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- A final destination comes from the initial map or a witnessed caller in
the accumulated history. A caller can select an already equal endpoint;
this relation does not claim that each invocation physically writes it. -/
def RemoteCovered {Event : Type} (entry : RemoteMap)
    (cause : Event → PeerId → Nat × Nat × Nat × Nat → Prop)
    (events : List Event) (final : RemoteMap) : Prop :=
  ∀ pid remote, final pid = some remote →
    entry pid = some remote ∨ ∃ event ∈ events, cause event pid remote

variable {Event : Type}
variable {cause : Event → PeerId → Nat × Nat × Nat × Nat → Prop}
variable {entry middle final : RemoteMap} {left right : List Event}

theorem RemoteCovered.of_retained (kept : RemoteRetained entry final) :
    RemoteCovered entry cause [] final :=
  fun pid remote present => Or.inl (kept pid remote present)

theorem RemoteCovered.append_history (covered : RemoteCovered entry cause left final) :
    RemoteCovered entry cause (left ++ right) final := by
  intro pid remote present
  rcases covered pid remote present with initial | ⟨event,member,origin⟩
  · exact Or.inl initial
  · exact Or.inr ⟨event,List.mem_append_left _ member,origin⟩

theorem RemoteCovered.retained (covered : RemoteCovered entry cause left middle)
    (kept : RemoteRetained middle final) : RemoteCovered entry cause left final :=
  fun pid remote present => covered pid remote (kept pid remote present)

theorem RemoteCovered.append (first : RemoteCovered entry cause left middle)
    (second : RemoteCovered middle cause right final) :
    RemoteCovered entry cause (left ++ right) final := by
  intro pid remote present
  rcases second pid remote present with earlier | ⟨event,member,origin⟩
  · exact first.append_history pid remote earlier
  · exact Or.inr ⟨event,List.mem_append_right _ member,origin⟩

theorem RemoteCovered.receipt (covered : RemoteCovered entry cause left middle)
    (event : Event) (effect : ∀ pid remote, final pid = some remote →
      middle pid = some remote ∨ cause event pid remote) :
    RemoteCovered entry cause (left ++ [event]) final := by
  apply covered.append
  intro pid remote present
  rcases effect pid remote present with earlier | origin
  · exact Or.inl earlier
  · exact Or.inr ⟨event,by simp,origin⟩

theorem RemoteCovered.updated (covered : RemoteCovered entry cause left middle)
    (event : Event) (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (origin : cause event pid remote)
    (kept : RemoteRetained (updateRemote middle pid remote) final) :
    RemoteCovered entry cause (left ++ [event]) final := by
  apply covered.receipt event
  intro other value present
  by_cases same : other = pid
  · subst other
    have equal := kept.updated_selected present
    subst value
    exact Or.inr origin
  · exact Or.inl (kept.updated_other same present)

def RemoteHistoryValid (valid : Event → Prop) (events : List Event) : Prop :=
  ∀ event ∈ events, valid event

theorem RemoteHistoryValid.append {valid : Event → Prop}
    (first : RemoteHistoryValid valid left) (second : RemoteHistoryValid valid right) :
    RemoteHistoryValid valid (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact first event member
  · exact second event member

theorem RemoteHistoryValid.snoc {valid : Event → Prop}
    (prior : RemoteHistoryValid valid left) {event : Event} (checked : valid event) :
    RemoteHistoryValid valid (left ++ [event]) := by
  apply prior.append
  intro item member
  have same : item = event := by simpa using member
  subst item
  exact checked

end Leanux.Proofs.WG.Roaming
