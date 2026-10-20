import AllowedipsExactChecked

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

theorem Ring.Chain.tail_exists {names m head previous nodes} (shape : Ring.Chain names m head previous nodes) :
    ∃ last, word m "peer.list.prev" (head+8) 8=.ok last := by
  induction shape with
  | nil back => exact ⟨_,back⟩
  | cons _ _ ih => exact ih

namespace Exact

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem mapped_of_word {m path address value}
    (decoded : word m path address 8=.ok value) : mapped m (.ofNat 64 address)=.ok () := by
  have loaded := word_loadInt _ _ _ _ _ decoded
  simp only [mapped,loaded,Option.isSome_some,require,ite_true]

theorem mapped_store {m read address size value} (before : mapped m read=.ok ()) :
    mapped (m.storeInt address size value) read=.ok () := by
  have checked := storeInt_defined m read address 8 size value (require_ok before)
  simp only [mapped,checked,require,ite_true]

/-- The same executable effect used by the runner succeeds from R and the
heap assertion. No future execution, mutation result or extra mapped-byte
premise is required for this segment. -/
theorem effect_total {names o s d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer) :
    ∃ memory regs, effect s=.ok (memory,regs) := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  have bx : s.regs.rbx.toBitVec=.ofNat 64 base := Trie.u64_of_nat nodeAt
  have r14 : s.regs.r14.toBitVec=.ofNat 64 peer := Trie.u64_of_nat peerAt
  obtain ⟨previous,next,focus,previousSlot,nextSlot,pred,succ⟩ := focus_of_heap related shape named present peerNamed
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers := by
    exact List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have removedDecoded := Ring.owner_unlink_decodes g layout (.peer peerNamed) previousSlot nextSlot core.nodeIds focus
    pred succ (Reconstructed.peer_at related peerNamed ownerMember) (value:=peer)
  simp only [Nat.add_sub_cancel] at removedDecoded
  let middle := removedMemory s (.ofNat 64 previous) (.ofNat 64 next)
  have memoryEq : middle=Ring.unlinkMemory (write64 s.dmem base peer) previous next := by
    simp only [middle,removed_as_ring,nodeAt,peerAt]
  rw [←memoryEq] at removedDecoded
  obtain ⟨first,firstRead,run⟩ := bind_ok removedDecoded
  obtain ⟨nodes,_,firstEq,chain,_,_,_⟩ := Ring.peerList_shape run
  obtain ⟨last,tailRead⟩ := chain.tail_exists
  have lastForward := chain.last_forward (Binary.Pair.word_path (firstEq ▸ firstRead) _) tailRead
  have focusAfter := (focus.owner_frame g layout named (value:=peer)).unlink_focus g layout previousSlot nextSlot
  rw [←memoryEq] at focusAfter
  have readBack : readNat ⟨s,0⟩ (s.regs.rbx.toNat+64) 8=.ok previous := by
    simpa only [readNat,nodeAt,Nat.add_assoc,Nat.reduceAdd] using readNat_of_word focus.back
  have readNext : readNat ⟨s,0⟩ (s.regs.rbx.toNat+56) 8=.ok next := by
    simpa only [readNat,nodeAt] using readNat_of_word focus.forward
  have readTail : readNat ⟨{s with dmem:=middle},0⟩ (s.regs.r14.toNat+1104) 8=.ok last := by
    simpa only [readNat,peerAt,Nat.add_assoc,Nat.reduceAdd] using readNat_of_word tailRead
  have ownerMapped : mapped s.dmem s.regs.rbx.toBitVec=.ok () := by
    obtain ⟨⟨actual,n⟩,_,_,decoded⟩ := core.nodes.left (id,base) named
    obtain ⟨raw,read,_⟩ := (Trie.decodeNode_fields decoded).peer
    have po : o.peer=0 := core.layout.2.1
    rw [po,Nat.add_zero] at read
    rw [bx]
    exact mapped_of_word read
  have nextMapped : mapped (ownerMemory s) (.ofNat 64 next+8)=.ok () := by
    apply mapped_store
    simpa only [BitVec.ofNat_add,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl] using mapped_of_word succ
  have previousMapped : mapped (nextMemory s (.ofNat 64 previous) (.ofNat 64 next)) (.ofNat 64 previous)=.ok () := by
    apply mapped_store
    apply mapped_store
    exact mapped_of_word pred
  let registers : Reg64s := {s.regs with
    rax := .ofNat last,rcx := .ofNat next,
    rdx := .ofBitVec (s.regs.rbx.toBitVec+56),r14 := .ofBitVec (s.regs.r14.toBitVec+1096)}
  have removed : removeEffect s=.ok (middle,registers) := by
    dsimp only [middle] at readTail
    simp only [removeEffect,readBack,readNext,ok_bind,ownerMapped,nextMapped,previousMapped,readTail]
    rfl
  let nextState := {s with dmem:=middle,regs:=registers}
  have atHead : nextState.regs.r14.toBitVec+8=.ofNat 64 (peer+1104) := by
    change (s.regs.r14.toBitVec+1096)+8=_
    rw [r14,BitVec.add_assoc,BitVec.ofNat_add]
    rfl
  have atFocus : nextState.regs.rbx.toBitVec+56=.ofNat 64 (base+56) := by
    change s.regs.rbx.toBitVec+56=_
    rw [bx,BitVec.ofNat_add]
    rfl
  have atBack : nextState.regs.rbx.toBitVec+64=.ofNat 64 (base+64) := by
    change s.regs.rbx.toBitVec+64=_
    rw [bx,BitVec.ofNat_add]
    rfl
  have headMapped : mapped nextState.dmem (nextState.regs.r14.toBitVec+8)=.ok () := by
    rw [atHead]
    simpa only [Nat.add_assoc,Nat.reduceAdd] using mapped_of_word tailRead
  have forwardMapped : mapped (headMemory nextState) (nextState.regs.rbx.toBitVec+56)=.ok () := by
    apply mapped_store
    rw [atFocus]
    exact mapped_of_word focusAfter.forward
  have backMapped : mapped (forwardMemory nextState) (nextState.regs.rbx.toBitVec+64)=.ok () := by
    apply mapped_store
    apply mapped_store
    rw [atBack]
    simpa only [Nat.add_assoc,Nat.reduceAdd] using mapped_of_word focusAfter.back
  have lastMapped : mapped (backwardMemory nextState) nextState.regs.rax.toBitVec=.ok () := by
    apply mapped_store
    apply mapped_store
    apply mapped_store
    exact mapped_of_word lastForward
  refine ⟨addedMemory nextState,{registers with rbx:=0},?_⟩
  simp only [effect,removed,ok_bind]
  change appendEffect nextState=_
  simp only [appendEffect,headMapped,forwardMapped,backMapped,lastMapped,ok_bind]
  rfl

#print axioms effect_total

local instance : Labels := Image.linkedLabels

/-- Segment refinement directly from entry correspondence. The executable
effect's successful result is derived and returned, not assumed. -/
theorem assignment_from_relation (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names o s k d ambient id base node pid peer owner}
    (hasDevice : k.dev=some d)
    (related : Corresponds names o s.dmem d) (shape : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer) :
    ∃ memory regs finalWG finalAmbient, effect s=.ok (memory,regs) ∧
      ((assignment id pid).run k).run ambient=.ok (((),finalWG),finalAmbient) ∧
      Eventually (instructionStep fetch) (fun t =>
        t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ t.data.regs=regs ∧ t.data.dmem=memory ∧
        EqualOutside (Writes names base) s.dmem t.data.dmem ∧
        ∃ finalDevice, finalWG.dev=some finalDevice ∧ Corresponds names o t.data.dmem finalDevice ∧
          heap names (target finalDevice) t.data.dmem=.ok ())
        ⟨s,AllowedipsMutationImage.Add.entry+0x3e5⟩ := by
  obtain ⟨memory,regs,checked⟩ := effect_total related shape named present peerNamed hasPeer nodeAt peerAt
  obtain ⟨finalWG,finalAmbient,source,execution⟩ :=
    assignment_checked fetch decoder hasDevice related shape named present peerNamed hasPeer nodeAt peerAt checked
  exact ⟨memory,regs,finalWG,finalAmbient,checked,source,execution⟩

#print axioms assignment_from_relation
end Exact
end Binary.Pair.Allowedips
