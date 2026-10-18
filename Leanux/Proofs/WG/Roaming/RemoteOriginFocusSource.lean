import Leanux.Proofs.WG.Roaming.RemoteOriginSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem focused_covered {E F State α : Type}
    (entry : RemoteMap) (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop) (valid : E→Prop)
    (encode : F→E) (decode : E→Option F) (inverse : ∀e,decode (encode e)=some e)
    (encoded : ∀e,valid (encode e)) (view : State→RemoteMap)
    (lowerCause : F→PeerId→Nat×Nat×Nat×Nat→Prop)
    (causes : ∀ e f,decode e=some f→∀pid remote,lowerCause f pid remote→cause e pid remote)
    (observed : PrefixT F State α) (appends : Appends observed)
    (covered : ∀initial,PrefixPreserves
      (fun h w=>RemoteCovered initial lowerCause h (view w)) (fun _=>True) observed) :
    PrefixPreserves (fun h w=>Inv entry cause valid h (view w)) (RemoteHistoryValid valid)
      (focusPrefix encode decode observed) := by
  intro w h prior
  obtain ⟨suffix,append⟩:=appends w (h.filterMap decode)
  have actual:=focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl append)
  have safe : RemoteHistoryValid valid (h++suffix.map encode) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩:=List.mem_map.mp member
    exact encoded original
  rw [actual]
  refine ⟨suffix.map encode,rfl,safe,?_⟩
  have normal:=(covered (view w) w (h.filterMap decode)
    (fun _ _ present=>Or.inl present)).choose_spec.2.2
  cases run:(runPrefix observed w (h.filterMap decode)).1 with
  | error stop=>trivial
  | ok out=>
    obtain ⟨value,final⟩:=out
    simp only [run] at normal
    refine ⟨?_,safe⟩
    intro pid remote present
    rcases normal pid remote present with earlier | ⟨event,member,origin⟩
    · exact prior.1.append_history pid remote earlier
    · rw [append] at member
      rcases List.mem_append.mp member with old | fresh
      · obtain ⟨outer,member,decoded⟩:=List.mem_filterMap.mp old
        exact Or.inr ⟨outer,List.mem_append_left _ member,causes outer event decoded pid remote origin⟩
      · exact Or.inr ⟨encode event,List.mem_append_right _ (List.mem_map.mpr ⟨event,fresh,rfl⟩),
          causes _ _ (inverse event) pid remote origin⟩

end Leanux.Proofs.WG.Roaming.RemoteOrigin
