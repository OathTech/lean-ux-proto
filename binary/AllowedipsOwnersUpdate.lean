import AllowedipsHeapChecks

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

private theorem occurrences_filter (xs : List Nat) (focus query pid : Nat) :
    (xs.filter (· != focus)).filterMap (fun x => if x=query then some pid else none)=
      if query=focus then [] else xs.filterMap (fun x => if x=query then some pid else none) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases same : query=focus <;> by_cases hit : x=query <;> by_cases removed : x=focus <;>
      simp_all

theorem owners_reassign_other (s : State) (focus pid query : Nat) (different : query≠focus) :
    owners (reassign focus pid s) query=owners s query := by
  simp only [owners,reassign,List.flatMap_map]
  apply congrArg (fun f => s.peers.flatMap f)
  funext entry
  rcases entry with ⟨current,count,entries⟩
  by_cases destination : current=pid <;>
    simp [reassignPeer,destination,occurrences_filter,different,Ne.symm different]

theorem owners_reassign_focus (s : State) (focus pid : Nat) :
    owners (reassign focus pid s) focus=
      s.peers.filterMap (fun p => if p.1=pid then some pid else none) := by
  simp only [owners,reassign,List.flatMap_map]
  induction s.peers with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨current,count,xs⟩
    simp only [reassignPeer,beq_iff_eq] at ih
    by_cases destination : current=pid <;>
      simp [reassignPeer,destination,occurrences_filter,ih]

private theorem filter_key (xs : List Nat) (pid : Nat) (unique : xs.Nodup) (present : pid ∈ xs) :
    xs.filterMap (fun current => if current=pid then some pid else none)=[pid] := by
  induction xs with
  | nil => cases present
  | cons current xs ih =>
    obtain ⟨absent,unique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with same|present
    · subst current
      have tail : xs.filterMap (fun current => if current=pid then some pid else none)=[] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro value member
        have different : value≠pid := by intro equal; exact absent (equal ▸ member)
        simp [different]
      simp [tail]
    · have different : current≠pid := by intro equal; exact absent (equal ▸ present)
      simp [different,ih unique present]

theorem target_peer_unique (d : Device) : ((target d).peers.map Prod.fst).Nodup := by
  simp only [target,List.map_map]
  change (d.peers.toList.map Prod.fst).Nodup
  rw [Std.TreeMap.map_fst_toList_eq_keys]
  exact d.peers.nodup_keys

theorem owners_reassign_target_focus (d : Device) (focus pid : Nat) (peer : Peer)
    (present : d.peers.get? pid=some peer) : owners (reassign focus pid (target d)) focus=[pid] := by
  rw [owners_reassign_focus]
  have member : pid ∈ (target d).peers.map Prod.fst := by
    apply List.mem_map.mpr
    refine ⟨(pid,peer.refcount,peer.allowedipsList),?_,rfl⟩
    exact List.mem_map.mpr ⟨(pid,peer),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
  simpa only [List.filterMap_map,Function.comp_def] using
    filter_key ((target d).peers.map Prod.fst) pid (target_peer_unique d) member

#print axioms owners_reassign_target_focus
end Binary.Pair.Allowedips
