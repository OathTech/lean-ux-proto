import AllowedipsChildSource
import AllowedipsRootOwners

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Root

theorem owners_installedChild_other (s : State) (parentId direction key cidr width pid id : Nat)
    (different : id≠s.nextNode) :
    owners (installedChild parentId direction key cidr width pid s) id=owners s id := by
  exact owners_installed_other s true key cidr pid id different

theorem owners_installedChild_new {names o memory d} (related : Corresponds names o memory d)
    (parentId direction key cidr width pid : Nat) (owner : Peer) (hasPeer : d.peers.get? pid=some owner) :
    owners (installedChild parentId direction key cidr width pid (target d)) d.nextNode=[pid] := by
  exact owners_installed_new related true key cidr pid owner hasPeer

/-- Node connection changes child/parent metadata, so the already proved
owner-list append suffices for every ownership clause in the heap assertion. -/
theorem ownership_installedChild {names newNames o before after d}
    (parentId direction key cidr width pid : Nat) (owner : Peer)
    (related : Corresponds names o before d) (shape : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    ∀ id node, (id,node) ∈ (installedChild parentId direction key cidr width pid (target d)).nodes →
      ownershipCheck newNames (installedChild parentId direction key cidr width pid (target d)) after id node=.ok () := by
  intro id node member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨⟨current,original⟩,present,equal⟩ := List.mem_map.mp old
    have identity : current=id := congrArg Prod.fst equal
    subst current
    have peerSame : node.peer=original.peer := by
      have actual := congrArg (fun pair : NodeId×AipNode => pair.2.peer) equal
      by_cases same : id=parentId <;> simpa [installChild,same] using actual.symm
    apply ownershipCheck_of
    · rw [owners_installedChild_other _ _ _ _ _ _ _ _ (Nat.ne_of_lt (target_nodes_below related (id,original) present)),peerSame]
      exact (heap_ownership shape id original present).1
    · rw [peerSame]
      exact internal id original present
  · obtain equal := List.mem_singleton.mp new
    cases equal
    apply ownershipCheck_of
    · exact owners_installedChild_new related parentId direction key cidr width pid owner hasPeer
    · simp [newNode]

theorem pending_internal_connected {names : Names} {before : MachineData} {d : Device}
    {key cidr pid base parentId parentBase direction packed : Nat} {memory : DataMem}
    (pending : NodeInit.Pending names before d key cidr pid base memory)
    (g : Geometry (names.allocated base) nodeOffsets)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes) (bit : direction<2) :
    ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck (names.allocated base)
        (connectMemory memory base (parentBase+8+direction*8) packed) current=.ok () := by
  intro current node member internal
  have frame := connect_frame memory base (parentBase+8+direction*8) packed
  have apart := connect_lists_apart g (allocated_node names base) (List.mem_append_left _ parentNamed) bit
  exact (internal_list_frame (names.allocated base) frame apart current) ▸ pending.internal current node member internal

#print axioms ownership_installedChild
end Binary.Pair.Allowedips
