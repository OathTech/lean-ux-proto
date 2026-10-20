import PairLookupBucket

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index LookupRelation

theorem selected_present {n w d query kinds owner}
    (focused : (callConfig n w d query kinds).focus.owner=some owner) :
    ∃ entry ∈ d.indexTable, entry.owner=owner := by
  unfold callConfig at focused
  obtain ⟨entry,found,selected⟩ := Option.bind_eq_some_iff.mp focused
  have member := List.mem_filter.mp (List.mem_of_find?_eq_some found)
  split at selected
  · exact ⟨entry,member.1,Option.some.inj selected⟩
  · cases selected

theorem selected_word {n o m w d query kinds owner}
    (related : Corresponds n o m d)
    (focused : (callConfig n w d query kinds).focus.owner=some owner) :
    ∃ value, OwnerWord.value d owner=some value := by
  obtain ⟨entry,member,ownerEq⟩ := selected_present focused
  obtain ⟨f,entryEq⟩ := reconstruct_focus related member
  have named := f.fields.named
  rw [entryEq,ownerEq] at named
  obtain ⟨value,_,present,_,_⟩ := named_owner related named
  exact ⟨value,present⟩

theorem call_focus {n o m w d query kinds} (related : Corresponds n o m d) :
    EntryFocus (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d) := by
  refine ⟨rfl,?_⟩
  cases focus : (callConfig n w d query kinds).focus.owner with
  | none =>
    change ((callConfig n w d query kinds).focus.owner.bind fun owner => (OwnerWord.value d owner).join)=none
    rw [focus]; rfl
  | some owner =>
    obtain ⟨value,present⟩ := selected_word related focus
    change (callConfig n w d query kinds).focus.owner.bind (OwnerWord.value d)=_
    change _=some ((callConfig n w d query kinds).focus.owner.bind fun owner => (OwnerWord.value d owner).join)
    simp only [focus,Option.bind_some,present,Option.join_some]

theorem call_peer {n o m w d query kinds pid} (related : Corresponds n o m d)
    (focused : (callConfig n w d query kinds).focus.peer=some pid) :
    ∃ peer, d.peers.get? pid=some peer := by
  change ((callConfig n w d query kinds).focus.owner.bind fun owner => (OwnerWord.value d owner).join)=some pid at focused
  obtain ⟨owner,_,word⟩ := Option.bind_eq_some_iff.mp focused
  have present : OwnerWord.value d owner=some (some pid) := by
    cases h : OwnerWord.value d owner with
    | none => rw [h] at word; cases word
    | some value =>
      rw [h] at word
      exact congrArg some word
  exact referenced_peer related present

theorem call_physical {n o s w d query kinds}
    (related : Corresponds n o s.data.dmem d) (storage : storageCheck n o=true)
    (names : interpretationCheck n=true) :
    Physical (callConfig n w d query kinds) [s] [LookupObservation.call "wg_index_hashtable_lookup" s]
      s (callView (callConfig n w d query kinds) d) := by
  let c := callConfig n w d query kinds
  have endpoint : Sequential.At c s.data.dmem (callView c d) := by
    refine ⟨rfl,?_,?_,?_⟩
    · exact bucket_physical related storage names
    · cases focus : c.focus.owner with
      | none => simp only [callView,focus,Option.bind_none]
      | some owner =>
        obtain ⟨value,present⟩ := selected_word related focus
        obtain ⟨base,raw,named,read,pointer⟩ := owner_named related present
        have validation := validate_basic (reconstruct_components related).1
        have interpreted := interpretation_owner names named
        have valueEq := (peerId_value validation.2.2.2.1 (word_bound read) pointer).1
        refine ⟨value,by simp only [callView,focus,Option.bind_some,present],?_⟩
        change s.data.dmem.loadInt (physicalOwner n owner) 8=some ((OwnerWord.pointer (peerPointer n) value).toNat : Int)
        rw [interpreted.1,valueEq]
        simpa only [validation.1.peer,Nat.add_zero] using word_loadInt _ _ _ _ _ read
    · cases focus : c.focus.peer with
      | none => simp only [callView,focus,Option.bind_none]
      | some pid =>
        obtain ⟨peer,present⟩ := call_peer related focus
        obtain ⟨base,named,read⟩ := peer_named related present
        have validation := validate_basic (reconstruct_components related).1
        refine ⟨peer.refcount,by simp only [callView,focus,Option.bind_some,present,Option.map_some],
          interpretation_peer names named,?_⟩
        change s.data.dmem.loadInt (Trie.interpretation n.peers pid+.ofNat 64 Layouts.peer_refcount) 4=some (peer.refcount : Int)
        rw [Trie.interpretation_of_mem validation.2.2.2.1 named]
        simpa only [validation.1.peerRefcount,BitVec.ofNat_add] using word_loadInt _ _ _ _ _ read
  have physical := (Sequential.at_iff c s _).mp endpoint
  simpa [Physical,countPhase,helperActive,helperTag,LookupObservation.call,List.foldl_cons,List.foldl_nil,
    OwnerFieldAt,ownerPending,lastHelperReturn] using physical

#print axioms call_physical
end Binary.Pair.IndexLookup
