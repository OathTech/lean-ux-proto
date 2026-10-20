import AllowedipsRootFrame

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG
open Leanux.Proofs.WG.AllowedIps

/-- Initialize and reconstruct the fresh record from the actual attachment,
header/copy and publication phases. Query and saved-slot facts are phase-local
resources, to be framed from the wrapper stack in complete call composition. -/
theorem fresh_node {names s attached withHeader copied after d pid owner cidr key v4}
    (related : Corresponds names nodeOffsets s.dmem d)
    (g : Geometry (names.allocated s.regs.rbx.toNat) nodeOffsets)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (width : s.regs.rbp.toNat=rootWidth v4)
    (prefixBound : cidr≤s.regs.rbp.toNat)
    (left : word s.dmem "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (attachment : attach s=.ok (attached,cidr))
    (header : store attached (s.regs.rbx.toNat+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok withHeader)
    (query : if s.regs.rbp.toNat=32 then word withHeader "query" s.regs.r13.toNat 4=.ok key else
      ∃ hi lo,word withHeader "query.high" s.regs.r13.toNat 8=.ok hi ∧
        word withHeader "query.low" (s.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo)
    (queryApart : ∀ a, InRange s.regs.r13.toBitVec 8 a →
      ¬InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 16 a)
    (copy : Root.copy s withHeader=.ok copied)
    (saved : word copied "root.slot" (s.regs.rsp.toNat+8) 8=
      .ok (names.table+(if v4 then 0 else 8)))
    (tableApart : disjointRanges s.regs.rbx.toNat 72 names.table 24=true)
    (publish : Root.publish s copied=.ok after) :
    decodeNode (names.allocated s.regs.rbx.toNat) nodeOffsets after names.nextNode s.regs.rbx.toNat=
      .ok (names.nextNode,{newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4}) ∧
    word after "table.root" (names.table+(if v4 then 0 else 8)) 8=.ok s.regs.rbx.toNat := by
  let n := names.allocated s.regs.rbx.toNat
  have named := allocated_node names s.regs.rbx.toNat
  have core := Trie.reconstruct_fields related.trie
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  obtain ⟨first,firstRead,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
  have decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=.ok owner.allowedipsList := by
    rw [firstRead]; exact Ring.peerList_allocate run
  obtain ⟨ownerRead,leftRead,rightRead,_⟩ := attach_record_fields g rfl named peerNamed decoded left right attachment
  have pointer := pointer_named (name_addresses related).2 peerNamed (core.peerRange _ _ peerNamed).1 "node.peer"
  have extent := g.bounded _ (node_allocation named)
  change s.regs.rbx.toNat+72≤2^64 at extent
  have family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128 := by
    rw [width]; cases v4 <;> simp [rootWidth]
  have headerEq := (store_facts header).2
  have initialized := header_copy_core (names:=n) family prefixBound extent ownerRead pointer leftRead rightRead
    (by simpa only [←headerEq] using query) queryApart (by simpa only [←headerEq] using copy)
  have valid := (reconstruct_fields related).valid
  unfold validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨table,_⟩ := check_ok _ _ _ _ valid
  have tableOriginal : (0<names.table ∧ names.table%8=0) ∧
      names.table+AllowedipsMutationLayout.tableSize<2^64 := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using table
  have tableFacts : (0<names.table ∧ names.table%8=0) ∧ names.table+24<2^64 := tableOriginal
  have root : parent n ((names.table+(if v4 then 0 else 8)) ||| 2)=.ok (rootSlot v4) := by
    cases v4
    · exact parent_root6 n tableFacts.1.2
    · exact parent_root4 n tableFacts.1.2
  have slotBound : names.table+(if v4 then 0 else 8)+8≤2^64 := by
    cases v4 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  have apart : ∀ a, InRange s.regs.rbx.toBitVec 56 a →
      ¬InRange (.ofNat 64 (names.table+(if v4 then 0 else 8))) 8 a := by
    have separated : s.regs.rbx.toNat+72≤names.table ∨ names.table+24≤s.regs.rbx.toNat := by
      simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using tableApart
    intro a first second
    have firstNat : InRange (.ofNat 64 s.regs.rbx.toNat) 56 a := by
      simpa only [ofNat_uint64] using first
    have firstRange := Span.location (span:=(s.regs.rbx.toNat,56)) (by omega) firstNat
    have secondRange := Span.location (span:=(names.table+(if v4 then 0 else 8),8)) slotBound second
    cases v4 <;> simp only [Bool.false_eq_true,ite_false,ite_true] at secondRange <;>
      rcases separated with l|r <;> omega
  have result := publish_node (id:=names.nextNode) (by omega) slotBound initialized saved root apart publish
  simpa only [Trie.targetNode,newNode,width] using result

#print axioms fresh_node
end Binary.Pair.Allowedips.Root
