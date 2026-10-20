import PairLookupNames

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

theorem target_owner_iff {d : Device} {owner : IndexOwner} {value : Option PeerId} :
    (owner,value) ∈ (target d).ownerWords ↔ OwnerWord.value d owner=some value := by
  cases owner with
  | handshake id =>
    simp only [target,Id.run,Pure.pure,List.mem_append,List.mem_map,OwnerWord.value]
    constructor
    · rintro (⟨⟨pid,p⟩,member,equal⟩ | ⟨⟨kid,k⟩,_,equal⟩)
      · obtain ⟨ownerEq,valueEq⟩ := Prod.mk.inj equal
        cases IndexOwner.handshake.inj ownerEq
        have present := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
        change _=some value
        change d.peers.get? pid=some p at present
        rw [present]
        exact congrArg some valueEq
      · cases (Prod.mk.inj equal).1
    · intro valueAt
      cases present : d.peers.get? id with
      | none => rw [present] at valueAt; cases valueAt
      | some p =>
        have equal : p.handshakeEntryPeer=value := by simpa only [present,Option.map_some,Option.some.injEq] using valueAt
        exact .inl ⟨(id,p),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,by simp [equal]⟩
  | keypair id =>
    simp only [target,Id.run,Pure.pure,List.mem_append,List.mem_map,OwnerWord.value]
    constructor
    · rintro (⟨⟨pid,p⟩,_,equal⟩ | ⟨⟨kid,k⟩,member,equal⟩)
      · cases (Prod.mk.inj equal).1
      · obtain ⟨ownerEq,valueEq⟩ := Prod.mk.inj equal
        cases IndexOwner.keypair.inj ownerEq
        have present := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
        change d.keypairs.get? kid=some k at present
        rw [present]
        exact congrArg some valueEq
    · intro valueAt
      cases present : d.keypairs.get? id with
      | none => rw [present] at valueAt; cases valueAt
      | some k =>
        have equal : k.peer=value := by simpa only [present,Option.map_some,Option.some.injEq] using valueAt
        exact .inr ⟨(id,k),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,by simp [equal]⟩

theorem named_owner {n o m d owner base} (related : Corresponds n o m d)
    (named : (owner,base) ∈ n.owners) : ∃ value raw,
    OwnerWord.value d owner=some value ∧
    word m s!"owner[{repr owner}].peer" (base+o.peer) 8=.ok raw ∧
    peerId n s!"owner[{repr owner}].peer" raw=.ok value := by
  obtain ⟨pair,member,decoded⟩ := (mapM_ok (reconstruct_components related).2.2.1).left (owner,base) named
  obtain ⟨raw,read,decoded⟩ := bind_ok decoded
  obtain ⟨value,pointer,done⟩ := bind_ok decoded
  have equal : (owner,value)=pair := Except.ok.inj done
  rw [←equal] at member
  exact ⟨value,raw,target_owner_iff.mp member,read,pointer⟩

theorem owner_named {n o m d owner value} (related : Corresponds n o m d)
    (present : OwnerWord.value d owner=some value) : ∃ base raw,
    (owner,base) ∈ n.owners ∧
    word m s!"owner[{repr owner}].peer" (base+o.peer) 8=.ok raw ∧
    peerId n s!"owner[{repr owner}].peer" raw=.ok value := by
  obtain ⟨⟨other,base⟩,named,decoded⟩ :=
    (mapM_ok (reconstruct_components related).2.2.1).right (owner,value) (target_owner_iff.mpr present)
  obtain ⟨raw,read,decoded⟩ := bind_ok decoded
  obtain ⟨peer,pointer,done⟩ := bind_ok decoded
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj done)
  exact ⟨base,raw,named,read,pointer⟩

theorem named_peer {n o m d id base} (related : Corresponds n o m d)
    (named : (id,base) ∈ n.peers) : ∃ peer, d.peers.get? id=some peer ∧
      word m s!"peer[{id}].refcount" (base+o.peerRefcount) 4=.ok peer.refcount := by
  obtain ⟨pair,member,decoded⟩ := (mapM_ok (reconstruct_components related).2.2.2).left (id,base) named
  obtain ⟨count,read,done⟩ := bind_ok decoded
  have equal : (id,count)=pair := Except.ok.inj done
  rw [←equal] at member
  obtain ⟨⟨pid,peer⟩,present,equal⟩ := List.mem_map.mp member
  obtain ⟨rfl,countEq⟩ := Prod.mk.inj equal
  exact ⟨peer,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present,countEq ▸ read⟩

theorem peer_named {n o m d id peer} (related : Corresponds n o m d)
    (present : d.peers.get? id=some peer) : ∃ base, (id,base) ∈ n.peers ∧
      word m s!"peer[{id}].refcount" (base+o.peerRefcount) 4=.ok peer.refcount := by
  have member : (id,peer.refcount) ∈ (target d).refcounts :=
    List.mem_map.mpr ⟨(id,peer),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
  obtain ⟨⟨pid,base⟩,named,decoded⟩ := (mapM_ok (reconstruct_components related).2.2.2).right _ member
  obtain ⟨count,read,done⟩ := bind_ok decoded
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj done)
  exact ⟨base,named,read⟩

theorem referenced_peer {n o m d owner pid} (related : Corresponds n o m d)
    (present : OwnerWord.value d owner=some (some pid)) : ∃ peer, d.peers.get? pid=some peer := by
  obtain ⟨_,raw,_,_,pointer⟩ := owner_named related present
  have converted : Trie.pointer n.peers "peer" raw=.ok (some pid) := by
    unfold peerId at pointer
    unfold Trie.pointer
    split at pointer
    · cases pointer
    · rename_i nonzero
      rw [ite_eq_right nonzero]
      cases found : n.peers.find? (·.2==raw) with
      | none => rw [found] at pointer; cases pointer
      | some pair => rw [found] at pointer; cases pair; exact pointer
  obtain ⟨base,named⟩ := Trie.pointer_some_named converted
  obtain ⟨peer,present,_⟩ := named_peer related named
  exact ⟨peer,present⟩

#print axioms owner_named
#print axioms referenced_peer
end Binary.Pair.IndexLookup
