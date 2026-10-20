import AllowedipsRootLocalFrame

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

structure Phases (names : Names) (s : MachineData) (key cidr : Nat) where
  attached : DataMem
  withHeader : DataMem
  copied : DataMem
  after : DataMem
  attachment : attach s=.ok (attached,cidr)
  header : store attached (s.regs.rbx.toNat+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok withHeader
  query : if s.regs.rbp.toNat=32 then word withHeader "query" s.regs.r13.toNat 4=.ok key else
    ∃ hi lo,word withHeader "query.high" s.regs.r13.toNat 8=.ok hi ∧
      word withHeader "query.low" (s.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo
  copy : Root.copy s withHeader=.ok copied
  saved : word copied "root.slot" (s.regs.rsp.toNat+8) 8=
    .ok (names.table+(if s.regs.rbp.toNat=32 then 0 else 8))
  publish : Root.publish s copied=.ok after

private theorem record_inside {s : MachineData} {a : BitVec 64}
    (read : InRange (.ofNat 64 s.regs.rbx.toNat) 56 a) :
    InRange (.ofNat 64 s.regs.rbx.toNat) 72 a := by
  obtain ⟨i,bound,equal⟩ := read
  exact ⟨i,by omega,equal⟩

/-- Every phase executes from the tested boundary's current state. No future
phase result or intermediate read is a hypothesis. -/
theorem phases_of_boundary {names world machine key cidr pid d owner}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (peerNamed : (pid,machine.data.regs.r14.toNat) ∈ names.trie.peers)
    (hasPeer : d.peers.get? pid=some owner) :
    Nonempty (Phases names machine.data key cidr) := by
  let s := machine.data
  let n := names.allocated s.regs.rbx.toNat
  obtain ⟨_,_,extent,freshAllocation,_⟩ := allocated_facts fields.allocated
  have extent : s.regs.rbx.toNat+72≤2^64 := Nat.le_of_lt extent
  have g := (geometry related).allocate extent freshAllocation
  have named : (names.nextNode,s.regs.rbx.toNat) ∈ n.trie.nodes := allocated_node names _
  have allocation (offset size) (within : offset+size≤72) :
      (s.dmem.loadInt (.ofNat 64 (s.regs.rbx.toNat+offset)) size).isSome=true :=
    (MappedLe.refl s.dmem).of_word (fields.zero_word extent "fresh" offset size within)
  have ownerFrame : EqualOutside (EntryWrites names s) s.dmem
      (write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat) := by
    intro a outside
    apply write64_frame _ _ _ a
    rintro ⟨i,bound,equal⟩
    exact outside (.inl ⟨i,by omega,equal⟩)
  have requested : readNat ⟨{s with dmem:=write64 s.dmem s.regs.rbx.toNat s.regs.r14.toNat},0⟩
      (s.regs.rsp.toNat+16) 4=.ok cidr := by
    simpa only [readNat] using readNat_of_word (fields.cidr_word ownerFrame)
  obtain ⟨attached,attachment,attachedMapped⟩ := attach_total related g peerNamed hasPeer
    fields.family fields.cidrBound allocation requested
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have oldList : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=
      .ok owner.allowedipsList := by
    obtain ⟨first,read,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
    rw [read]; exact Ring.peerList_allocate run
  have listFrame := (attach_record_fields g rfl named peerNamed oldList
    (fields.zero_word extent _ 8 8 (by decide)) (fields.zero_word extent _ 16 8 (by decide)) attachment).2.2.2
  have attachedFrame : EqualOutside (EntryWrites names s) s.dmem attached := by
    intro a outside
    exact (ownerFrame a outside).trans (listFrame a (fun inside => outside (.inr (.inl inside))))
  let withHeader := attached.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4 (headerWord s.regs.rbp.toNat cidr)
  have header : store attached (s.regs.rbx.toNat+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok withHeader :=
    store_total (attachedMapped _ _ (allocation 24 4 (by decide)))
  have headerFrame : EqualOutside (EntryWrites names s) s.dmem withHeader := by
    intro a outside
    exact (attachedFrame a outside).trans
      (store_record_frame (by decide) header a (fun inside => outside (.inl (record_inside inside))))
  have headerMapped := attachedMapped.trans (store_mapped header)
  have query := fields.query_words headerFrame
  have queryMapped : if s.regs.rbp.toNat=32 then
      (withHeader.loadInt (.ofNat 64 s.regs.r13.toNat) 4).isSome=true else
      (withHeader.loadInt (.ofNat 64 s.regs.r13.toNat) 8).isSome=true ∧
      (withHeader.loadInt (.ofNat 64 (s.regs.r13.toNat+8)) 8).isSome=true := by
    by_cases four : s.regs.rbp.toNat=32
    · rw [ite_eq_left four] at query ⊢
      exact (MappedLe.refl withHeader).of_word query
    · rw [ite_eq_right four] at query ⊢
      obtain ⟨hi,lo,high,low,_⟩ := query
      exact ⟨(MappedLe.refl withHeader).of_word high,(MappedLe.refl withHeader).of_word low⟩
  obtain ⟨copied,copy,copiedMapped⟩ := copy_total (s:=s) queryMapped (by
    intro offset size within
    have mapped := headerMapped _ _ (allocation (32+offset) size (by omega))
    simpa only [Nat.add_assoc] using mapped)
  have copiedFrame : EqualOutside (EntryWrites names s) s.dmem copied := by
    intro a outside
    exact (headerFrame a outside).trans ((copy_frame copy) a (fun inside => outside (.inl (record_inside inside))))
  have saved := fields.saved_word copiedFrame
  let slot := names.table+(if s.regs.rbp.toNat=32 then 0 else 8)
  have rootMapped : (s.dmem.loadInt (.ofNat 64 slot) 8).isSome=true := by
    have full := reconstruct_fields related
    by_cases four : s.regs.rbp.toNat=32
    · obtain ⟨value,read,_⟩ := full.root4
      simpa only [slot,four,ite_true,AllowedipsMutationLayout.root4] using (MappedLe.refl s.dmem).of_word read
    · obtain ⟨value,read,_⟩ := full.root6
      simpa only [slot,four,ite_false,AllowedipsMutationLayout.root6] using (MappedLe.refl s.dmem).of_word read
  have allMapped := headerMapped.trans copiedMapped
  have savedRead : readNat ⟨{s with dmem:=copied},0⟩ (s.regs.rsp.toNat+8) 8=.ok slot := by
    simpa only [readNat] using readNat_of_word saved
  obtain ⟨after,publish,_⟩ := publish_total savedRead (allMapped _ _ (allocation 48 8 (by decide)))
    (allMapped _ _ rootMapped)
  exact ⟨⟨attached,withHeader,copied,after,attachment,header,fields.query_words headerFrame,copy,saved,publish⟩⟩

#print axioms phases_of_boundary
end Binary.Pair.Allowedips.Root
