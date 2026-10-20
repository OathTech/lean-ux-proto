import AllowedipsRootIncoming

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Binary.Pair.Allowedips.Model

theorem owners_installed_other (s : State) (v4 : Bool) (key cidr pid id : Nat)
    (different : id≠s.nextNode) :
    owners (installedRoot v4 key cidr pid s) id=owners s id := by
  simp only [owners,installedRoot,List.flatMap_map]
  apply congrArg (fun f => s.peers.flatMap f)
  funext entry
  rcases entry with ⟨current,count,entries⟩
  by_cases same : current=pid <;> simp [appendOwner,same,Ne.symm different]

theorem installed_peers_reassign (s : State) (v4 : Bool) (key cidr pid : Nat)
    (fresh : ∀ entry ∈ s.peers, s.nextNode ∉ entry.2.2) :
    (installedRoot v4 key cidr pid s).peers=(reassign s.nextNode pid s).peers := by
  apply List.map_congr_left
  intro entry member
  rcases entry with ⟨current,count,entries⟩
  have absent : s.nextNode ∉ entries := fresh _ member
  have filtered : entries.filter (· != s.nextNode)=entries := by
    apply List.filter_eq_self.mpr
    intro id present
    have different : id≠s.nextNode := by intro same; exact absent (same ▸ present)
    simpa using different
  by_cases same : current=pid <;> simp [appendOwner,reassignPeer,same,filtered]

theorem fresh_not_owned {names o m d} (related : Corresponds names o m d) :
    ∀ entry ∈ (target d).peers, d.nextNode ∉ entry.2.2 := by
  have fields := reconstruct_fields related
  have bounded := ids_below_counter fields.valid
  rintro ⟨pid,count,entries⟩ member
  obtain ⟨address,_,_,decoded⟩ := fields.peer member
  obtain ⟨first,_,decoded⟩ := bind_ok decoded
  have absent := Ring.peerList_fresh decoded bounded
  have counter : d.nextNode=names.nextNode := fields.nextNode
  simpa only [counter] using absent

theorem owners_installed_new {names o m d} (related : Corresponds names o m d)
    (v4 : Bool) (key cidr pid : Nat) (owner : Peer) (hasPeer : d.peers.get? pid=some owner) :
    owners (installedRoot v4 key cidr pid (target d)) d.nextNode=[pid] := by
  have peers := installed_peers_reassign (target d) v4 key cidr pid (fresh_not_owned related)
  unfold owners
  rw [peers]
  exact owners_reassign_target_focus d d.nextNode pid owner hasPeer

#print axioms owners_installed_new
end Binary.Pair.Allowedips
