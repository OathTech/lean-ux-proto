import AllowedipsRootTotalMemory
import AllowedipsRootLists

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Old reconstruction supplies the owner ring and its actual tail. The new
allocation and one saved stack read supply the remaining readable bytes. -/
theorem attach_total {names o s d pid owner cidr}
    (related : Corresponds names o s.dmem d)
    (g : Geometry (names.allocated s.regs.rbx.toNat) o)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128)
    (cidrBound : cidr≤s.regs.rbp.toNat)
    (allocation : ∀ offset size, offset+size≤72 →
      (s.dmem.loadInt (.ofNat 64 (s.regs.rbx.toNat+offset)) size).isSome=true)
    (requested : readNat ⟨{s with dmem:=write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat},0⟩
      (s.regs.rsp.toNat+16) 4=.ok cidr) :
    ∃ attached, attach s=.ok (attached,cidr) ∧ MappedLe s.dmem attached := by
  let n := names.allocated s.regs.rbx.toNat
  let first := write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat
  change readNat ⟨{s with dmem:=first},0⟩ (s.regs.rsp.toNat+16) 4=.ok cidr at requested
  have core := Trie.reconstruct_fields related.trie
  have named : (names.nextNode,s.regs.rbx.toNat) ∈ n.trie.nodes := allocated_node names _
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have oldList : (do
      let head ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) head (s.regs.r14.toNat+1096) [])=
      .ok owner.allowedipsList := by
    obtain ⟨head,read,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
    rw [read]; exact Ring.peerList_allocate run
  have ownerList := Ring.owner_decodes g core.layout.1 (.peer peerNamed) named oldList (value:=s.regs.r14.toNat)
  obtain ⟨head,headRead,run⟩ := bind_ok ownerList
  obtain ⟨nodes,_,headEq,chain,_,_,_⟩ := Ring.peerList_shape run
  obtain ⟨last,tailRead⟩ := chain.tail_exists
  have lastForward := chain.last_forward (Binary.Pair.word_path (headEq ▸ headRead) _) tailRead
  have ownerStore : store s.dmem s.regs.rbx.toNat 8 s.regs.r14.toNat=.ok first := by
    rw [store_total (by simpa only [Nat.add_zero] using allocation 0 8 (by decide)),store_nat64]
    rfl
  have preserved := store_mapped ownerStore
  have readTail : readNat ⟨{s with dmem:=first},0⟩ (s.regs.r14.toNat+1104) 8=.ok last := by
    simpa only [readNat,Nat.add_assoc,Nat.reduceAdd] using readNat_of_word tailRead
  let second := first.storeInt (.ofNat 64 (s.regs.r14.toNat+1104)) 8 (s.regs.rbx.toNat+56 : Nat)
  have headStore : store first (s.regs.r14.toNat+1104) 8 (s.regs.rbx.toNat+56)=.ok second := by
    apply store_total
    simpa only [Nat.add_assoc,Nat.reduceAdd] using (MappedLe.refl first).of_word tailRead
  have secondMapped := preserved.trans (store_mapped headStore)
  let third := second.storeInt (.ofNat 64 (s.regs.rbx.toNat+56)) 8 (s.regs.r14.toNat+1096 : Nat)
  have forwardStore : store second (s.regs.rbx.toNat+56) 8 (s.regs.r14.toNat+1096)=.ok third :=
    store_total (secondMapped _ _ (allocation 56 8 (by decide)))
  have thirdMapped := secondMapped.trans (store_mapped forwardStore)
  let fourth := third.storeInt (.ofNat 64 (s.regs.rbx.toNat+64)) 8 last
  have backStore : store third (s.regs.rbx.toNat+64) 8 last=.ok fourth :=
    store_total (thirdMapped _ _ (allocation 64 8 (by decide)))
  have firstToFourth := (store_mapped headStore).trans ((store_mapped forwardStore).trans (store_mapped backStore))
  let fifth := fourth.storeInt (.ofNat 64 last) 8 (s.regs.rbx.toNat+56 : Nat)
  have tailStore : store fourth last 8 (s.regs.rbx.toNat+56)=.ok fifth :=
    store_total (firstToFourth.of_word lastForward)
  refine ⟨fifth,?_,thirdMapped.trans ((store_mapped backStore).trans (store_mapped tailStore))⟩
  have familyCheck : (s.regs.rbp.toNat==32 || s.regs.rbp.toNat==128)=true := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using family
  simp only [attach,familyCheck,require,ite_true,ownerStore,requested,cidrBound,decide_true,
    readTail,headStore,forwardStore,backStore,tailStore,ok_bind]
  rfl

#print axioms attach_total
end Binary.Pair.Allowedips.Root
