import PairTrie

namespace Binary.Pair.Trie
open Leanux Leanux.WG

def replaceCount (id count : Nat) (state : State) : State :=
  {state with counts := state.counts.map fun (pid,old) => (pid,if pid=id then count else old)}

/-- Updating an existing map entry changes values without changing the
ordered identity list used by reconstruction. No tree shape is observed. -/
theorem tree_insert_present (peers : Std.TreeMap Nat α) (id : Nat) (old value : α)
    (present : peers[id]? = some old) :
    (peers.insert id value).toList = peers.toList.map (fun (pid,p) => (pid,if pid=id then value else p)) := by
  have equivalent : (peers.insert id value).Equiv (peers.map (fun pid p => if pid=id then value else p)) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro pid
    by_cases same : id=pid
    · subst pid
      simp [present]
    · simp [Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_map,same,Ne.symm same]
  simpa only [Std.TreeMap.toList_map] using equivalent.toList_eq

theorem target_replaceCount (d : Device) (id count : Nat) (peer : Peer)
    (present : d.peers.get? id = some peer) :
    target {d with peers := d.peers.insert id {peer with refcount := count}} = replaceCount id count (target d) := by
  unfold target replaceCount
  congr 1
  rw [tree_insert_present d.peers id peer _ present]
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨pid,p⟩ _
  by_cases same : pid=id <;> simp [same]

#print axioms target_replaceCount
end Binary.Pair.Trie
