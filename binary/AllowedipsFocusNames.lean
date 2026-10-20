import AllowedipsHeapOwnership

namespace Binary.Pair.Allowedips

theorem name_addresses {names o m d} (related : Corresponds names o m d) :
    (names.trie.nodes.map Prod.snd).Nodup ∧ (names.trie.peers.map Prod.snd).Nodup := by
  have valid := (reconstruct_fields related).valid
  unfold validate at valid
  obtain ⟨_,valid,_⟩ := bind_ok valid
  unfold Trie.validate at valid
  obtain ⟨_,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,unique,_⟩ := bind_ok valid
  have all := forIn_ok (P := fun pairs : List (Nat×Nat) => (pairs.map Prod.snd).Nodup)
    (fun pairs _ _ _ run => by
      obtain ⟨checked,run⟩ := check_ok _ _ _ _ run
      have lengths : (pairs.map Prod.fst).eraseDups.length=pairs.length ∧
          (pairs.map Prod.snd).eraseDups.length=pairs.length := by simpa using checked
      exact ⟨(),(Except.ok.inj run).symm,nodup_of_eraseDups_length _ (by simpa using lengths.2)⟩) unique
  exact ⟨all _ (by simp),all _ (by simp)⟩

theorem node_addresses {names o m d} (related : Corresponds names o m d) :
    (names.trie.nodes.map Prod.snd).Nodup := (name_addresses related).1

theorem find_address {pairs : List (Nat×Nat)} {id base}
    (unique : (pairs.map Prod.snd).Nodup) (member : (id,base) ∈ pairs) :
    pairs.find? (·.2==base)=some (id,base) := by
  induction pairs with
  | nil => cases member
  | cons pair pairs ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl|member
    · simp
    · have different : pair.2≠base := by
        intro equal
        exact parts.1 (equal ▸ List.mem_map.mpr ⟨(id,base),member,rfl⟩)
      simpa only [List.find?_cons,show (pair.2==base)=false from by simp [different]] using ih parts.2 member

theorem pointer_named {pairs : List (Nat×Nat)} {id base}
    (unique : (pairs.map Prod.snd).Nodup) (member : (id,base) ∈ pairs)
    (positive : 0<base) (path : String) : Trie.pointer pairs path base=.ok (some id) := by
  simp only [Trie.pointer,show (base==0)=false from by simp [Nat.ne_of_gt positive],Bool.false_eq_true,
    ite_false,find_address unique member]

theorem node_peer_link_ne {names o id base pid peer}
    (g : Geometry names o) (layout : o.nodeSize=72)
    (node : (id,base) ∈ names.trie.nodes) (owner : (pid,peer) ∈ names.trie.peers) :
    base+56≠peer+1096 := by
  have apart := g.slices_apart (node_allocation node) (peer_allocation owner) 56 8 1096 8
    (by dsimp only; rw [layout]; decide) (by dsimp only; decide) (fun _ => .inl (by decide))
  intro same
  apply apart (.ofNat 64 (base+56)) ⟨0,by decide,by simp⟩
  exact ⟨0,by decide,by simp [same]⟩

theorem Ring.Fields.rehead {names m oldHead head p link q id}
    (fields : Ring.Fields names m oldHead p link q id) (different : link≠head) :
    Ring.Fields names m head p link q id :=
  ⟨fields.known,different,fields.valid,fields.owner,fields.back,fields.forward⟩

theorem Ring.Chain.previous_slot {names m head nodes link p q id}
    (shape : Ring.Chain names m head head nodes) (headSlot : LinkSlot names head)
    (member : (link,id) ∈ nodes) (fields : Ring.Fields names m head p link q id) : LinkSlot names p := by
  rcases shape.back_origin member fields with ⟨same,_⟩|⟨parent,current,previous,_,same,parentFields⟩
  · exact same ▸ headSlot
  · exact same ▸ parentFields.slot

theorem Ring.Chain.next_slot {names m head previous nodes link p q id}
    (shape : Ring.Chain names m head previous nodes) (headSlot : LinkSlot names head)
    (member : (link,id) ∈ nodes) (fields : Ring.Fields names m head p link q id) : LinkSlot names q := by
  induction shape with
  | nil => cases member
  | cons first tail ih =>
    rcases List.mem_cons.mp member with equal|member
    · cases equal
      have same := word_values first.forward fields.forward
      cases tail with
      | nil => exact same ▸ headSlot
      | cons child rest => exact same ▸ child.slot
    · exact ih member

#print axioms node_addresses
#print axioms node_peer_link_ne
end Binary.Pair.Allowedips
