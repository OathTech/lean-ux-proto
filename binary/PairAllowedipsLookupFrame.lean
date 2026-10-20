import PairAllowedipsMetadata
import PairCallAdequacy

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem named_peer_count {names o m d id a} (related : Trie.Corresponds names o m d)
    (named : (id,a) ∈ names.peers) (path : String) :
    ∃ peer, d.peers.get? id=some peer ∧ word m path (a+o.peerRefcount) 4=.ok peer.refcount := by
  obtain ⟨⟨id',count⟩,member,identity,read⟩ := (Trie.reconstruct_fields related).peers.left (id,a) named
  subst id'
  obtain ⟨⟨pid,peer⟩,present,equal⟩ := List.mem_map.mp member
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  exact ⟨peer,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present,word_path path read⟩

/-- Upgrade the old decoder's count effect using the physical metadata frame.
The source equations supplied here are proved from the accepted source run. -/
theorem reconstruct_from_core {names o before after d final}
    (related : Corresponds names o before d)
    (core : Trie.Corresponds names.trie o after final)
    (same : MetadataSame names o before after) (f : Nat → Nat → Nat)
    (peers : ∀ id peer, d.peers.get? id=some peer →
      ∃ next, final.peers.get? id=some next ∧ next.refcount=f id peer.refcount)
    (targetEffect : target final=mapCounts f (target d)) :
    Corresponds names o after final := by
  have counts (id a : Nat) (named : (id,a) ∈ names.trie.peers) :
      word after "peer.refcount" (a+o.peerRefcount) 4=
        (word before "peer.refcount" (a+o.peerRefcount) 4).map (f id) := by
    obtain ⟨old,oldPresent,oldRead⟩ := named_peer_count related.trie named "peer.refcount"
    obtain ⟨next,nextPresent,nextRead⟩ := named_peer_count core named "peer.refcount"
    obtain ⟨expected,present,effect⟩ := peers id old oldPresent
    have equal : next=expected := Option.some.inj (nextPresent.symm.trans present)
    subst next
    rw [oldRead,nextRead,effect]
    rfl
  unfold Corresponds
  rw [reconstruct_mapCounts names o before after f same counts,related,targetEffect]
  rfl

theorem reconstruct_miss {names o before after d}
    (related : Corresponds names o before d)
    (core : Trie.Corresponds names.trie o after d)
    (same : MetadataSame names o before after) : Corresponds names o after d := by
  apply reconstruct_from_core related core same (fun _ count => count)
  · intro id peer present
    exact ⟨peer,present,rfl⟩
  · simp [mapCounts]

theorem reconstruct_hit {names o before after d id peer count}
    (related : Corresponds names o before d) (present : d.peers.get? id=some peer)
    (core : Trie.Corresponds names.trie o after
      {d with peers := d.peers.insert id {peer with refcount := count}})
    (same : MetadataSame names o before after) :
    Corresponds names o after {d with peers := d.peers.insert id {peer with refcount := count}} := by
  apply reconstruct_from_core related core same (fun pid old => if pid=id then count else old)
  · intro pid old oldPresent
    by_cases equal : pid=id
    · subst pid
      exact ⟨{peer with refcount := count},by simp,by simp⟩
    · exact ⟨old,by simpa [Std.TreeMap.getElem?_insert,Ne.symm equal] using oldPresent,by simp [equal]⟩
  · exact target_mapCounts d id count peer present

#print axioms reconstruct_from_core
#print axioms reconstruct_hit
end Binary.Pair.Allowedips
