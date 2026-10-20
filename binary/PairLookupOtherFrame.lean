import PairLookupFrame

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

theorem CallFacts.owner_frame {n o coverage s w d query kinds ra after owner base}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after)
    (named : (owner,base) ∈ n.owners) (other : (callConfig n w d query kinds).focus.owner≠some owner)
    (path : String) : word s.data.dmem path base 8=word after path base 8 := by
  have validation := validate_basic (reconstruct_components facts.related).1
  have layout := validation.1
  have bytes : SpansFrame [(base,8)] s.data.dmem after := by
    intro span member a inside
    have equal := List.mem_singleton.mp member
    subst span
    apply facts.heap_frame frame (owner_heap layout ⟨(base,8),List.mem_map.mpr ⟨(owner,base),named,rfl⟩,inside⟩)
    rintro (⟨selected,focus,written⟩ | ⟨_,count⟩)
    · obtain ⟨value,present⟩ := selected_word facts.related focus
      obtain ⟨selectedBase,_,selectedNamed,_,_⟩ := owner_named facts.related present
      have address := (interpretation_owner facts.names selectedNamed).1
      change InRange (physicalOwner n selected) 8 a at written
      rw [address] at written
      have separate := entry_fields_apart facts.storage named selectedNamed
        (offset := 0) (size := 8) (otherOffset := 0) (otherSize := 8)
        (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (by
          intro same
          have identities := unique_second validation.2.2.1 named (same ▸ selectedNamed)
          exact False.elim (other (identities ▸ focus)))
      exact separate a (by simpa only [Nat.add_zero,Span.contains] using inside) (by simpa only [Nat.add_zero] using written)
    · obtain ⟨span,member,atSpan⟩ := count_cover facts.related a count
      exact spansApart_sound facts.countApart (List.mem_map.mpr ⟨(owner,base),named,rfl⟩) member inside atSpan
  simpa only [Nat.add_zero] using bytes.word (List.mem_singleton_self _) 0 8 (by omega) path

theorem CallFacts.count_frame {n o coverage s w d query kinds ra after id base}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after)
    (named : (id,base) ∈ n.peers) (other : (callConfig n w d query kinds).focus.peer≠some id)
    (path : String) : word s.data.dmem path (base+o.peerRefcount) 4=word after path (base+o.peerRefcount) 4 := by
  have validation := validate_basic (reconstruct_components facts.related).1
  have layout := validation.1
  have bytes : SpansFrame [(base+o.peerRefcount,4)] s.data.dmem after := by
    intro span member a inside
    have equal := List.mem_singleton.mp member
    subst span
    apply facts.heap_frame frame ((DataSlot.count id base named).heap layout a inside)
    rintro (owner | ⟨_,⟨selected,focus,written⟩⟩)
    · obtain ⟨span,member,atSpan⟩ := owner_cover facts.related facts.names a owner
      exact spansApart_sound facts.countApart member (List.mem_map.mpr ⟨(id,base),named,rfl⟩) atSpan inside
    · obtain ⟨peer,present⟩ := call_peer (w := w) (query := query) (kinds := kinds) facts.related focus
      obtain ⟨selectedBase,selectedNamed,_⟩ := peer_named facts.related present
      change InRange (Trie.interpretation n.peers selected+.ofNat 64 Layouts.peer_refcount) 4 a at written
      rw [Trie.interpretation_of_mem validation.2.2.2.1 selectedNamed,←layout.peerRefcount,←BitVec.ofNat_add] at written
      have separate := storage_slices_apart facts.storage (count_storage named) (count_storage selectedNamed)
        (a := base+o.peerRefcount) (size := 4) (b := selectedBase+o.peerRefcount) (otherSize := 4)
        ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by
          intro same
          have addresses := congrArg Prod.fst same
          have bases : base=selectedBase := by dsimp only at addresses; omega
          have identities := unique_second validation.2.2.2.2 named (bases ▸ selectedNamed)
          exact False.elim (other (identities ▸ focus)))
      exact separate a inside written
  simpa only [Nat.add_zero] using bytes.word (List.mem_singleton_self _) 0 4 (by omega) path

#print axioms CallFacts.owner_frame
#print axioms CallFacts.count_frame
end Binary.Pair.IndexLookup
