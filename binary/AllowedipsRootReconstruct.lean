import AllowedipsRootFreshNode
import AllowedipsRootMetadata
import AllowedipsRootEffect

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG
open Leanux.Proofs.WG.AllowedIps
local instance : Labels := Image.linkedLabels

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Whole projection after the actual empty-root initialization phases.
Physical resources and phase reads remain explicit: complete wrapper
composition must establish them from entry and the generic allocation return. -/
theorem reconstruct_phases {names s attached withHeader copied after d pid owner cidr key v4}
    (related : Corresponds names nodeOffsets s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (positive : 0<s.regs.rbx.toNat) (aligned : s.regs.rbx.toNat%8=0)
    (extent : s.regs.rbx.toNat+72<2^64)
    (freshAllocation : ∀ span ∈ allocations names nodeOffsets,
      disjointRanges s.regs.rbx.toNat 72 span.1 span.2=true)
    (tableApart : disjointRanges s.regs.rbx.toNat 72 names.table 24=true)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (width : s.regs.rbp.toNat=rootWidth v4) (prefixBound : cidr≤s.regs.rbp.toNat)
    (left : word s.dmem "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
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
    (publish : Root.publish s copied=.ok after) :
    Corresponds (names.allocated s.regs.rbx.toNat) nodeOffsets after
      (emptyInstalled d v4 key cidr pid owner) ∧
    EqualOutside (Writes (names.allocated s.regs.rbx.toNat) s.regs.rbx.toNat
      (names.table+(if v4 then 0 else 8))) s.dmem after := by
  let n := names.allocated s.regs.rbx.toNat
  let slotOffset := if v4 then 0 else 8
  have rootWithin : slotOffset+8≤24 := by cases v4 <;> decide
  have g := (geometry related).allocate (Nat.le_of_lt extent) freshAllocation
  have valid := validate_allocate related positive aligned extent freshAllocation tableApart
  have full := reconstruct_fields related
  have core := Trie.reconstruct_fields related.trie
  have counter := ids_below_counter full.valid
  have fresh : ∀ pair ∈ names.trie.nodes, pair.2≠s.regs.rbx.toNat := by
    intro pair member same
    have separated := freshAllocation (pair.2,72) (node_allocation member)
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,same] at separated
    omega
  have named := allocated_node names s.regs.rbx.toNat
  obtain ⟨slot,slotRead,initFrame⟩ := initialization_frame header copy publish
  have slotEq : slot=names.table+slotOffset :=
    Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt slotRead).symm.trans (word_loadInt _ _ _ _ _ saved)))
  subst slot
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  obtain ⟨first,firstRead,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
  have decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=.ok owner.allowedipsList := by
    rw [firstRead]; exact Ring.peerList_allocate run
  have listFrame := (attach_record_fields g rfl named peerNamed decoded left right attachment).2.2.2
  have frame : EqualOutside (Writes n s.regs.rbx.toNat (names.table+slotOffset)) s.dmem after := by
    intro a outside
    have ownerOutside : ¬InRange (.ofNat 64 s.regs.rbx.toNat) 8 a := by
      rintro ⟨i,small,equal⟩
      exact outside (.inr (.inl ⟨i,by omega,equal⟩))
    exact (write64_frame _ _ _ a ownerOutside).trans
      ((listFrame a (fun inside => outside (.inl inside))).trans
        (initFrame a (fun inside => outside (.inr inside))))
  have freshRead := fresh_node related g peerNamed hasPeer width prefixBound left right
    attachment header query queryApart copy saved tableApart publish
  have lists := attach_lists related heapOk g (Nat.ne_of_gt positive) fresh peerNamed hasPeer zeroNext zeroPrev attachment
  have nodeBound : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode := by
    rintro ⟨current,node⟩ member
    obtain ⟨⟨id,base⟩,named,read⟩ := full.nodes.right (current,node) member
    have equal := (decodeNode_fields read).1
    have less := counter (id,base) named
    dsimp only at equal less
    rw [equal] at less
    simpa only [←full.nextNode,target] using less
  refine ⟨?_,frame⟩
  rw [show Corresponds n nodeOffsets after (emptyInstalled d v4 key cidr pid owner) ↔
    reconstruct n nodeOffsets after=.ok (installedRoot v4 key cidr pid (target d)) from by
      rw [Corresponds,target_emptyInstalled d v4 key cidr pid owner hasPeer nodeBound]]
  let table : AllowedIps := if v4 then {d.peerAllowedips with root4:=some names.nextNode}
    else {d.peerAllowedips with root6:=some names.nextNode}
  have keepTable (offset) (different : offset+8≤slotOffset ∨ slotOffset+8≤offset)
      (within : offset+8≤24) (path) :
      word after path (names.table+offset) 8=word s.dmem path (names.table+offset) 8 :=
    (Trie.word_frame frame path _ _ (table_field_apart valid g rfl named within rootWithin different)).symm
  have root4 : ∃ raw, word after "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
      Trie.pointer n.trie.nodes "table.root4" raw=.ok table.root4 := by
    cases v4
    · obtain ⟨raw,read,pointer⟩ := full.root4
      refine ⟨raw,?_,pointer_suffix pointer⟩
      change word after "table.root4" (names.table+0) 8=.ok raw
      rw [keepTable 0 (.inl (by decide)) (by decide) "table.root4"]
      exact read
    · refine ⟨s.regs.rbx.toNat,word_path "table.root4" freshRead.2,?_⟩
      exact pointer_allocated "table.root4" (Nat.ne_of_gt positive) fresh
  have root6 : ∃ raw, word after "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
      Trie.pointer n.trie.nodes "table.root6" raw=.ok table.root6 := by
    cases v4
    · refine ⟨s.regs.rbx.toNat,word_path "table.root6" freshRead.2,?_⟩
      exact pointer_allocated "table.root6" (Nat.ne_of_gt positive) fresh
    · obtain ⟨raw,read,pointer⟩ := full.root6
      refine ⟨raw,?_,pointer_suffix pointer⟩
      change word after "table.root6" (names.table+8) 8=.ok raw
      rw [keepTable 8 (.inr (by decide)) (by decide) "table.root6"]
      exact read
  have seqRead : word after "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok table.seq.toNat := by
    change word after "table.seq" (names.table+16) 8=.ok table.seq.toNat
    rw [keepTable 16 (.inr (by cases v4 <;> decide)) (by decide) "table.seq"]
    cases v4 <;> exact full.seq
  have result := reconstruct_allocated (fun x => x) (appendOwner names.nextNode pid) related valid root4 root6 seqRead
    (fun pair member value read => old_node_frame related g fresh member
      (by cases v4 <;> simp [slotOffset]) frame read) freshRead.1 (by
        rintro ⟨current,address⟩ currentNamed ⟨nextId,count,entries⟩ read
        obtain ⟨identity,countRead,_⟩ := decodePeer_fields read
        dsimp only at identity
        subst nextId
        have member : (current,count,entries) ∈ (target d).peers := by
          obtain ⟨value,member,valueRead⟩ := full.peers.left (current,address) currentNamed
          exact Except.ok.inj (valueRead.symm.trans read) ▸ member
        have listAttached := lists current address count entries currentNamed member
        have currentNew : (current,address) ∈ n.trie.peers := currentNamed
        have listAfter := (list_read_frame (names:=n) initFrame
          (initialization_lists_apart valid g rfl named rootWithin) (.peer currentNew)).symm.trans listAttached
        have countAfter : word after "peer.refcount" (address+nodeOffsets.peerRefcount) 4=.ok count := by
          change word after "peer.refcount" (address+Layouts.peer_refcount) 4=.ok count
          rw [←Trie.word_frame frame "peer.refcount" _ _ (peer_count_apart valid g rfl currentNew named rootWithin)]
          exact countRead
        unfold decodePeer
        rw [countAfter]
        obtain ⟨first,headRead,run⟩ := bind_ok listAfter
        change word after "peer.list.head" (address+AllowedipsMutationLayout.allowedips_list) 8=.ok first at headRead
        change peerList (names.allocated s.regs.rbx.toNat) after (address+AllowedipsMutationLayout.allowedips_list)
          ((names.allocated s.regs.rbx.toNat).trie.nodes.length+1) first (address+AllowedipsMutationLayout.allowedips_list) []=_ at run
        simp only [ok_bind,headRead,run,appendOwner]
        rfl)
  simpa [←full.nextNode,installedRoot,target,table] using result

#print axioms reconstruct_phases

/-- Actual Kraken execution of the successful initialization tail restores the
full allowed-IPs projection. The phase/resource hypotheses above are still
local obligations; this is not an entry-to-return insertion theorem. -/
theorem initialization_segment (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch) {names s attached withHeader copied after d pid owner cidr key v4}
    (related : Corresponds names nodeOffsets s.dmem d)
    (heapOk : heap names (target d) s.dmem=.ok ())
    (positive : 0<s.regs.rbx.toNat) (aligned : s.regs.rbx.toNat%8=0)
    (extent : s.regs.rbx.toNat+72<2^64)
    (freshAllocation : ∀ span ∈ allocations names nodeOffsets,
      disjointRanges s.regs.rbx.toNat 72 span.1 span.2=true)
    (tableApart : disjointRanges s.regs.rbx.toNat 72 names.table 24=true)
    (peerNamed : (pid,s.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner)
    (width : s.regs.rbp.toNat=rootWidth v4) (prefixBound : cidr≤s.regs.rbp.toNat)
    (left : word s.dmem "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word s.dmem "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (zeroNext : word s.dmem "peer.list.next" (s.regs.rbx.toNat+56) 8=.ok 0)
    (zeroPrev : word s.dmem "peer.list.prev" (s.regs.rbx.toNat+64) 8=.ok 0)
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
    (publish : Root.publish s copied=.ok after) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ OutputRegisters s.regs t.data.regs ∧
      EqualOutside (Writes (names.allocated s.regs.rbx.toNat) s.regs.rbx.toNat
        (names.table+(if v4 then 0 else 8))) s.dmem t.data.dmem ∧
      Corresponds (names.allocated s.regs.rbx.toNat) nodeOffsets t.data.dmem
        (emptyInstalled d v4 key cidr pid owner))
      ⟨s,AllowedipsMutationImage.Add.entry+0x443⟩ := by
  have relation := reconstruct_phases related heapOk positive aligned extent freshAllocation tableApart
    peerNamed hasPeer width prefixBound left right zeroNext zeroPrev attachment header query queryApart copy saved publish
  have checked : effect s=.ok after := by
    simp only [effect,attachment,header,copy,publish,ok_bind]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (effect_segment fetch decoder checked)
  rintro final ⟨pc,memory,registers⟩
  exact ⟨pc,registers,by simpa only [memory] using relation.2,by simpa only [memory] using relation.1⟩

#print axioms initialization_segment
end Binary.Pair.Allowedips.Root
