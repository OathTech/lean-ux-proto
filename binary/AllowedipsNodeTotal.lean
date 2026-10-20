import AllowedipsNodeBoundaryFields
import AllowedipsRootTotalMemory
import AllowedipsRootLists

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Leanux.WG Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- The old relation supplies the real owner-list tail. All remaining
readability comes from the allocated bytes and the two saved input words. -/
theorem attach_total {names o s d pid owner base cidr}
    (related : Corresponds names o s.dmem d)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128)
    (cidrBound : cidr≤s.regs.rbp.toNat)
    (original : s.regs.r12.toNat=cidr) (bits : s.regs.r15.toNat=s.regs.rbp.toNat)
    (allocation : ∀ offset size, offset+size≤72 →
      (s.dmem.loadInt (.ofNat 64 (base+offset)) size).isSome=true)
    (baseRead : readNat ⟨s,0⟩ s.regs.rsp.toNat 8=.ok base)
    (requested : readNat ⟨s,0⟩ (s.regs.rsp.toNat+16) 4=.ok cidr) :
    ∃ attached, attach s=.ok (attached,base,cidr) ∧ MappedLe s.dmem attached := by
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  obtain ⟨head,headRead,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
  obtain ⟨nodes,_,headEq,chain,_,_,_⟩ := Ring.peerList_shape run
  obtain ⟨last,tailRead⟩ := chain.tail_exists
  have lastForward := chain.last_forward (Binary.Pair.word_path (headEq ▸ headRead) _) tailRead
  have readTail : readNat ⟨s,0⟩ (s.regs.r14.toNat+1104) 8=.ok last := by
    simpa only [readNat,Nat.add_assoc,Nat.reduceAdd] using readNat_of_word tailRead
  let first := s.dmem.storeInt (.ofNat 64 base) 8 s.regs.r14.toNat
  have ownerStore : store s.dmem base 8 s.regs.r14.toNat=.ok first :=
    store_total (by simpa only [Nat.add_zero] using allocation 0 8 (by decide))
  have firstMapped := store_mapped ownerStore
  let second := first.storeInt (.ofNat 64 (s.regs.r14.toNat+1104)) 8 (base+56 : Nat)
  have headStore : store first (s.regs.r14.toNat+1104) 8 (base+56)=.ok second := by
    apply store_total
    simpa only [Nat.add_assoc,Nat.reduceAdd] using firstMapped.of_word tailRead
  have secondMapped := firstMapped.trans (store_mapped headStore)
  let third := second.storeInt (.ofNat 64 (base+64)) 8 last
  have backStore : store second (base+64) 8 last=.ok third :=
    store_total (secondMapped _ _ (allocation 64 8 (by decide)))
  have thirdMapped := secondMapped.trans (store_mapped backStore)
  let fourth := third.storeInt (.ofNat 64 (base+56)) 8 (s.regs.r14.toNat+1096 : Nat)
  have forwardStore : store third (base+56) 8 (s.regs.r14.toNat+1096)=.ok fourth :=
    store_total (thirdMapped _ _ (allocation 56 8 (by decide)))
  have fourthMapped := thirdMapped.trans (store_mapped forwardStore)
  let fifth := fourth.storeInt (.ofNat 64 last) 8 (base+56 : Nat)
  have tailStore : store fourth last 8 (base+56)=.ok fifth :=
    store_total (fourthMapped.of_word lastForward)
  refine ⟨fifth,?_,fourthMapped.trans (store_mapped tailStore)⟩
  have familyCheck : (s.regs.rbp.toNat==32 || s.regs.rbp.toNat==128)=true := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using family
  simp only [attach,baseRead,requested,readTail,familyCheck,require,ite_true,
    cidrBound,decide_true,original,bits,beq_self_eq_true,Bool.true_and,
    ownerStore,headStore,backStore,forwardStore,tailStore,ok_bind]
  rfl

theorem header_total {s : MachineData} {memory : DataMem} {base cidr : Nat}
    (stack : ∀ offset ∈ [36,43,44],
      (memory.loadInt (.ofNat 64 (s.regs.rsp.toNat+offset)) 1).isSome=true)
    (mapped : (memory.loadInt (.ofNat 64 (base+24)) 4).isSome=true) :
    ∃ after, header s.regs.rsp.toNat s.regs.rbp.toNat base cidr memory=.ok after ∧ MappedLe memory after := by
  let mask := (s.regs.rbp.toNat/8-1)%8
  let m1 := memory.storeInt (.ofNat 64 (s.regs.rsp.toNat+36)) 1 mask
  have first : store memory (s.regs.rsp.toNat+36) 1 mask=.ok m1 := store_total (stack 36 (by simp))
  have mapped1 := store_mapped first
  let m2 := m1.storeInt (.ofNat 64 (s.regs.rsp.toNat+43)) 1 ((cidr/8) ^^^ mask : Nat)
  have second : store m1 (s.regs.rsp.toNat+43) 1 ((cidr/8) ^^^ mask)=.ok m2 :=
    store_total (mapped1 _ _ (stack 43 (by simp)))
  have mapped2 := mapped1.trans (store_mapped second)
  let m3 := m2.storeInt (.ofNat 64 (s.regs.rsp.toNat+44)) 1 (7-cidr%8 : Nat)
  have third : store m2 (s.regs.rsp.toNat+44) 1 (7-cidr%8)=.ok m3 :=
    store_total (mapped2 _ _ (stack 44 (by simp)))
  have mapped3 := mapped2.trans (store_mapped third)
  let after := m3.storeInt (.ofNat 64 (base+24)) 4 (headerWord s.regs.rbp.toNat cidr : Nat)
  have last : store m3 (base+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok after :=
    store_total (mapped3 _ _ mapped)
  refine ⟨after,?_,mapped3.trans (store_mapped last)⟩
  dsimp only [mask] at first second
  simp only [header,first,second,third,last,ok_bind]

#print axioms attach_total
#print axioms header_total
end Binary.Pair.Allowedips.NodeInit
