import PairAllowedipsDecode

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

def mapCounts (f : Nat → Nat → Nat) (s : State) : State :=
  {s with peers := s.peers.map fun (id,count,list) => (id,f id count,list)}

theorem target_mapCounts (d : Device) (id count : Nat) (peer : Peer)
    (present : d.peers.get? id = some peer) :
    target {d with peers := d.peers.insert id {peer with refcount := count}} =
      mapCounts (fun pid old => if pid=id then count else old) (target d) := by
  unfold target mapCounts
  congr 1
  rw [Trie.tree_insert_present d.peers id peer _ present]
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨pid,p⟩ member
  by_cases same : pid=id
  · subst pid
    have equal : p=peer := Option.some.inj
      ((Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member).symm.trans present)
    subst p
    simp
  · simp [same]

/-- The live lookup changes counts only. Roots, counter, packed parents and
ordered list links come from an execution frame, not a stronger state relation. -/
structure MetadataSame (names : Names) (o : AllowedipsProbe.Offsets)
    (before after : DataMem) : Prop where
  table : ∀ offset ∈ [AllowedipsMutationLayout.root4,AllowedipsMutationLayout.root6,AllowedipsMutationLayout.seq],
    ∀ path, word after path (names.table+offset) 8=word before path (names.table+offset) 8
  nodes : ∀ id a, (id,a) ∈ names.trie.nodes →
    decodeNode names o after id a=decodeNode names o before id a
  heads : ∀ id a, (id,a) ∈ names.trie.peers →
    word after "peer.list.head" (a+AllowedipsMutationLayout.allowedips_list) 8=
      word before "peer.list.head" (a+AllowedipsMutationLayout.allowedips_list) 8
  lists : ∀ id a, (id,a) ∈ names.trie.peers → ∀ first,
    peerList names after (a+AllowedipsMutationLayout.allowedips_list)
      (names.trie.nodes.length+1) first (a+AllowedipsMutationLayout.allowedips_list) []=
    peerList names before (a+AllowedipsMutationLayout.allowedips_list)
      (names.trie.nodes.length+1) first (a+AllowedipsMutationLayout.allowedips_list) []

theorem reconstruct_mapCounts (names : Names) (o : AllowedipsProbe.Offsets)
    (before after : DataMem) (f : Nat → Nat → Nat)
    (same : MetadataSame names o before after)
    (counts : ∀ id a, (id,a) ∈ names.trie.peers →
      word after "peer.refcount" (a+o.peerRefcount) 4=
        (word before "peer.refcount" (a+o.peerRefcount) 4).map (f id)) :
    reconstruct names o after=(reconstruct names o before).map (mapCounts f) := by
  have ns : names.trie.nodes.mapM (fun (id,a) => decodeNode names o after id a)=
      names.trie.nodes.mapM (fun (id,a) => decodeNode names o before id a) := by
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    exact same.nodes id a member
  have ps : names.trie.peers.mapM (fun (id,a) => decodePeer names o after id a)=
      (names.trie.peers.mapM (fun (id,a) => decodePeer names o before id a)).map
        (List.map fun (id,count,list) => (id,f id count,list)) := by
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    simp only [decodePeer,counts id a member,same.heads id a member,same.lists id a member]
    cases word before "peer.refcount" (a+o.peerRefcount) 4 with
    | error e => rfl
    | ok count =>
      cases word before "peer.list.head" (a+AllowedipsMutationLayout.allowedips_list) 8 with
      | error e => rfl
      | ok first =>
        dsimp only [Bind.bind, Except.bind, Except.map, Pure.pure]
        cases peerList names before (a+AllowedipsMutationLayout.allowedips_list)
          (names.trie.nodes.length+1) first (a+AllowedipsMutationLayout.allowedips_list) [] <;> rfl
  unfold reconstruct
  rw [ns,ps,same.table _ (by simp) "table.root4",same.table _ (by simp) "table.root6",
    same.table _ (by simp) "table.seq"]
  cases validate names o with
  | error e => rfl
  | ok v =>
    cases word before "table.root4" (names.table+AllowedipsMutationLayout.root4) 8 with
    | error e => rfl
    | ok r4 =>
      dsimp only [Bind.bind, Except.bind, Except.map, Pure.pure]
      cases Trie.pointer names.trie.nodes "table.root4" r4 with
      | error e => rfl
      | ok root4 =>
        cases word before "table.root6" (names.table+AllowedipsMutationLayout.root6) 8 with
        | error e => rfl
        | ok r6 =>
          dsimp only [Bind.bind, Except.bind, Except.map, Pure.pure]
          cases Trie.pointer names.trie.nodes "table.root6" r6 with
          | error e => rfl
          | ok root6 =>
            cases word before "table.seq" (names.table+AllowedipsMutationLayout.seq) 8 with
            | error e => rfl
            | ok seq =>
              cases names.trie.nodes.mapM (fun (id,a) => decodeNode names o before id a) with
              | error e => rfl
              | ok nodes =>
                cases names.trie.peers.mapM (fun (id,a) => decodePeer names o before id a) <;> rfl

#print axioms reconstruct_mapCounts
end Binary.Pair.Allowedips
