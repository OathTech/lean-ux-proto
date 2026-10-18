import PairLookupPre
import OwnerStore

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG LookupRelation
set_option maxRecDepth 2048

/-- A source frame, not an extra relation clause: the one selected owner
word and referenced count are the only fields lookup can change. -/
structure SourceFrame (c : Config) (before after : Device) : Prop where
  table : after.indexTable=before.indexTable
  peerIds : after.peers.toList.map Prod.fst=before.peers.toList.map Prod.fst
  keypairIds : after.keypairs.toList.map Prod.fst=before.keypairs.toList.map Prod.fst
  owners : ∀ owner, c.focus.owner≠some owner → OwnerWord.value after owner=OwnerWord.value before owner
  counts : ∀ id, c.focus.peer≠some id → (after.peers.get? id).map (·.refcount)=(before.peers.get? id).map (·.refcount)

theorem SourceFrame.refl (c : Config) (d : Device) : SourceFrame c d d :=
  ⟨rfl,rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
theorem SourceFrame.trans {c first second third} (left : SourceFrame c first second)
    (right : SourceFrame c second third) : SourceFrame c first third :=
  ⟨right.table.trans left.table,right.peerIds.trans left.peerIds,right.keypairIds.trans left.keypairIds,
    fun owner other => (right.owners owner other).trans (left.owners owner other),
    fun id other => (right.counts id other).trans (left.counts id other)⟩

theorem tree_insert_ids (tree : Std.TreeMap Nat α) (id : Nat) (old value : α)
    (present : tree.get? id=some old) :
    (tree.insert id value).toList.map Prod.fst=tree.toList.map Prod.fst := by
  rw [Trie.tree_insert_present tree id old value present,List.map_map]
  rfl

theorem SourceFrame.count {c d id peer} (present : d.peers.get? id=some peer)
    (focused : c.focus.peer=some id) (count : Nat) :
    SourceFrame c d {d with peers := d.peers.insert id {peer with refcount := count}} := by
  refine ⟨rfl,tree_insert_ids _ _ _ _ present,rfl,?_,?_⟩
  · intro owner _
    exact owner_value_count_update d id peer count present owner
  · intro other different
    have ne : id≠other := fun equal => different (equal ▸ focused)
    simp [Std.TreeMap.getElem?_insert,ne]

theorem SourceFrame.handshake {c d id peer} (present : d.peers.get? id=some peer)
    (focused : c.focus.owner=some (.handshake id)) (word : Option PeerId) :
    SourceFrame c d {d with peers := d.peers.insert id {peer with handshakeEntryPeer := word}} := by
  refine ⟨rfl,tree_insert_ids _ _ _ _ present,rfl,?_,?_⟩
  · intro owner different
    cases owner with
    | keypair _ => rfl
    | handshake other =>
      have ne : id≠other := fun equal => different (equal ▸ focused)
      simp [OwnerWord.value,Std.TreeMap.getElem?_insert,ne]
  · intro other _
    by_cases same : id=other
    · subst other
      have present : d.peers[id]?=some peer := present
      simp only [Std.TreeMap.get?_eq_getElem?,Std.TreeMap.getElem?_insert_self,present,Option.map_some]
    · simp [Std.TreeMap.getElem?_insert,same]

theorem SourceFrame.keypair {c d id keypair} (present : d.keypairs.get? id=some keypair)
    (focused : c.focus.owner=some (.keypair id)) (word : Option PeerId) :
    SourceFrame c d {d with keypairs := d.keypairs.insert id {keypair with peer := word}} := by
  refine ⟨rfl,rfl,tree_insert_ids _ _ _ _ present,?_,fun _ _ => rfl⟩
  intro owner different
  cases owner with
  | handshake _ => rfl
  | keypair other =>
    have ne : id≠other := fun equal => different (equal ▸ focused)
    simp [OwnerWord.value,Std.TreeMap.getElem?_insert,ne]

theorem setter_frame {c w final d owner old value}
    (device : w.k.wg=some d) (present : OwnerWord.value d owner=some old)
    (focused : c.focus.owner=some owner) (run : (owner.setPeerWord value).run w=.ok ((),final)) :
    ∃ d', final.k.wg=some d' ∧ SourceFrame c d d' ∧ OwnerWord.value d' owner=some value := by
  cases owner with
  | handshake id =>
    cases found : d.peers.get? id with
    | none => rw [OwnerWord.value,found] at present; cases present
    | some peer =>
      rw [OwnerWord.set_handshake_run w d id peer value device found] at run
      have equal := congrArg Prod.snd (Except.ok.inj run)
      dsimp only at equal
      rw [←equal]
      refine ⟨_,rfl,SourceFrame.handshake found focused value,?_⟩
      simp only [OwnerWord.value,Std.TreeMap.get?_eq_getElem?,Std.TreeMap.getElem?_insert_self,Option.map_some]
  | keypair id =>
    cases found : d.keypairs.get? id with
    | none => rw [OwnerWord.value,found] at present; cases present
    | some keypair =>
      rw [OwnerWord.set_keypair_run w d id keypair value device found] at run
      have equal := congrArg Prod.snd (Except.ok.inj run)
      dsimp only at equal
      rw [←equal]
      refine ⟨_,rfl,SourceFrame.keypair found focused value,?_⟩
      simp only [OwnerWord.value,Std.TreeMap.get?_eq_getElem?,Std.TreeMap.getElem?_insert_self,Option.map_some]

#print axioms setter_frame
end Binary.Pair.IndexLookup
