import AllowedipsRootInternal

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG Leanux.Proofs.WG.AllowedIps

/-- The logical heap update requires no restriction on the other root. Only
the internal nodes' unchanged self-links depend on physical memory. -/
theorem heap_installed {names newNames o before after d} (v4 : Bool) (key cidr pid : Nat) (owner : Peer)
    (related : Corresponds names o before d) (shape : heap names (target d) before=.ok ())
    (hasPeer : d.peers.get? pid=some owner)
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)=none)
    (internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck newNames after current=.ok ()) :
    heap newNames (installedRoot v4 key cidr pid (target d)) after=.ok () := by
  have below := target_nodes_below related
  have checks := (heap_checks names (target d) before).mp shape
  apply (heap_checks newNames _ after).mpr
  constructor
  · exact trie_heap_installed v4 key cidr pid shape below empty
  · intro id node member
    rcases List.mem_append.mp member with old | new
    · have different : id≠d.nextNode := Nat.ne_of_lt (below (id,node) old)
      constructor
      · exact (structureCheck_installed_old (target d) v4 key cidr pid id node empty different).trans
          (checks.2 id node old).1
      · apply ownershipCheck_of
        · rw [owners_installed_other _ _ _ _ _ _ different]
          exact (heap_ownership shape id node old).1
        · exact internal id node old
    · have equal := List.mem_singleton.mp new
      cases equal
      constructor
      · exact structureCheck_installed_new v4 key cidr pid shape below empty
      · apply ownershipCheck_of
        · exact owners_installed_new related v4 key cidr pid owner hasPeer
        · simp [newNode]

theorem heap_phases {names s attached withHeader copied after d pid owner cidr key v4}
    (related : Corresponds names nodeOffsets s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (positive : 0<s.regs.rbx.toNat) (aligned : s.regs.rbx.toNat%8=0)
    (extent : s.regs.rbx.toNat+72<2^64)
    (freshAllocation : ∀ span ∈ allocations names nodeOffsets,
      disjointRanges s.regs.rbx.toNat 72 span.1 span.2=true)
    (tableApart : disjointRanges s.regs.rbx.toNat 72 names.table 24=true)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)=none)
    (attachment : attach s=.ok (attached,cidr))
    (header : store attached (s.regs.rbx.toNat+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok withHeader)
    (copy : Root.copy s withHeader=.ok copied)
    (saved : word copied "root.slot" (s.regs.rsp.toNat+8) 8=
      .ok (names.table+(if v4 then 0 else 8)))
    (publish : Root.publish s copied=.ok after) :
    heap (names.allocated s.regs.rbx.toNat) (target (emptyInstalled d v4 key cidr pid owner)) after=.ok () := by
  let n := names.allocated s.regs.rbx.toNat
  let slotOffset := if v4 then 0 else 8
  have rootWithin : slotOffset+8≤24 := by cases v4 <;> decide
  have g := (geometry related).allocate (Nat.le_of_lt extent) freshAllocation
  have valid := validate_allocate related positive aligned extent freshAllocation tableApart
  have fresh : ∀ pair ∈ names.trie.nodes, pair.2≠s.regs.rbx.toNat := by
    intro pair member same
    have separated := freshAllocation (pair.2,72) (node_allocation member)
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,same] at separated
    omega
  obtain ⟨slot,slotRead,frame⟩ := initialization_frame header copy publish
  have slotEq : slot=names.table+slotOffset :=
    Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt slotRead).symm.trans (word_loadInt _ _ _ _ _ saved)))
  subst slot
  rw [target_emptyInstalled d v4 key cidr pid owner hasPeer (target_nodes_below related)]
  apply heap_installed v4 key cidr pid owner related heapOk hasPeer empty
  intro current node member internal
  have attachedCheck := attach_internal related heapOk g fresh peerNamed hasPeer attachment member internal
  have same := internal_list_frame n frame
    (initialization_lists_apart valid g rfl (allocated_node names _) rootWithin) current
  exact same ▸ attachedCheck

#print axioms heap_installed
#print axioms heap_phases
end Binary.Pair.Allowedips.Root
