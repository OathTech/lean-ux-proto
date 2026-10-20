import AllowedipsNodeLocalFrame
import AllowedipsNodeRecordFields
import AllowedipsRootRecord
import AllowedipsRootBoundaryResources
import AllowedipsNodeBoundaryExec

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

/-- Reconstruct the initialized core from the tested boundary and actual
summary evaluation. The three stack writes are framed before using the same
packed-header/key decoder as the empty-root path. Publication is still pending. -/
theorem core_of_effect {names world machine key cidr pid base memory}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (checked : effect machine.data=.ok (memory,base)) :
    Trie.decodeNode (names.allocated base).trie nodeOffsets memory base=
      .ok (Trie.targetNode (newNode key cidr machine.data.regs.rbp.toNat (some pid))) ∧
      EqualOutside (EntryWrites names machine.data base) machine.data.dmem memory := by
  obtain ⟨attached,initialized,attachment,headerCheck,copyCheck⟩ := effect_parts fields.original checked
  let s := machine.data
  let n := names.allocated base
  obtain ⟨d,_,related,_⟩ := assertAt_ok fields.asserted
  obtain ⟨owner,peerNamed,hasPeer⟩ := peer_of_address fields.owner related
  obtain ⟨_,_,extent,freshAllocation,_⟩ := allocated_facts fields.allocated
  have extent : base+72≤2^64 := Nat.le_of_lt extent
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt (by omega)
  have g := (geometry related).allocate extent freshAllocation
  have named := allocated_node names base
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  obtain ⟨first,firstRead,run⟩ := bind_ok (Reconstructed.peer_at related peerNamed ownerMember)
  have decoded : (do
      let first ← word s.dmem "peer.list.head" (s.regs.r14.toNat+1096) 8
      peerList n s.dmem (s.regs.r14.toNat+1096) (n.trie.nodes.length+1) first (s.regs.r14.toNat+1096) [])=
      .ok owner.allowedipsList := by
    rw [firstRead]; exact Ring.peerList_allocate run
  obtain ⟨ownerRead,leftRead,rightRead,listFrame⟩ := attach_record_fields g rfl named peerNamed decoded
    (fields.zero_word _ 8 8 (by decide)) (fields.zero_word _ 16 8 (by decide)) attachment
  have attachedFrame : EqualOutside (EntryWrites names s base) s.dmem attached := by
    intro a outside
    have initial := write64_frame s.dmem base s.regs.r14.toNat a (fun inside => by
      obtain ⟨i,bound,equal⟩ := inside
      exact outside (.inl ⟨i,by omega,equal⟩))
    exact initial.trans (listFrame a (fun inside => outside (.inr (.inl inside))))
  have initializedFrame : EqualOutside (EntryWrites names s base) s.dmem initialized := by
    intro a outside
    exact (attachedFrame a outside).trans (header_frame headerCheck a outside)
  obtain ⟨saved,stackFrame,stored⟩ := header_parts headerCheck
  have keep (offset size : Nat) (within : offset+size≤72) (path : String) :
      word saved path (base+offset) size=word attached path (base+offset) size := by
    apply (Trie.word_frame stackFrame path _ _ _).symm
    intro a inside
    apply fields.stack_node_apart a
    obtain ⟨i,bound,equal⟩ := inside
    refine ⟨offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
  have ownerSaved : word saved "node.peer" base 8=.ok s.regs.r14.toNat := by
    have kept := keep 0 8 (by decide) "node.peer"
    simpa only [Nat.add_zero] using kept.trans ownerRead
  have leftSaved : word saved "node.child[0]" (base+8) 8=.ok 0 := by
    rw [keep 8 8 (by decide)]; exact leftRead
  have rightSaved : word saved "node.child[1]" (base+16) 8=.ok 0 := by
    rw [keep 16 8 (by decide)]; exact rightRead
  have core := Trie.reconstruct_fields related.trie
  have pointer := pointer_named (name_addresses related).2 peerNamed (core.peerRange _ _ peerNamed).1 "node.peer"
  have storedEq := (store_facts stored).2
  have query := fields.query_words initializedFrame
  have queryApart : ∀ a, InRange s.regs.r13.toBitVec (if s.regs.rbp.toNat=32 then 4 else 8) a →
      ¬InRange (.ofNat 64 (base+32)) 16 a := by
    intro a read written
    apply fields.query_separated a
    · obtain ⟨i,bound,equal⟩ := read
      refine ⟨i,?_,equal⟩
      rcases fields.family with four|six
      · simp only [s,four,ite_true,Nat.reduceDiv] at bound ⊢; exact bound
      · simp only [s,six,show ¬(128=32) from by decide,ite_false,Nat.reduceDiv] at bound ⊢
        omega
    · obtain ⟨i,bound,equal⟩ := written
      apply Or.inl
      refine ⟨32+i,by omega,?_⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
  have result := header_copy_core (s:=rootView s base) (names:=n) (key:=key) (pid:=pid) (before:=saved) (after:=memory)
    fields.family fields.cidrBound (by simpa only [rootView,baseNat] using extent)
    (by simpa only [rootView,baseNat] using ownerSaved) pointer
    (by simpa only [rootView,baseNat] using leftSaved)
    (by simpa only [rootView,baseNat] using rightSaved)
    (by simpa only [rootView,s,baseNat,←storedEq] using query)
    (by
      intro a read written
      apply queryApart a read
      simpa only [rootView,baseNat] using written)
    (by simpa only [rootView,s,baseNat,←storedEq] using copyCheck)
  refine ⟨by simpa only [rootView,baseNat] using result,?_⟩
  have copiedFrame := copy_frame copyCheck
  simp only [baseNat] at copiedFrame
  intro a outside
  exact (initializedFrame a outside).trans (copiedFrame a (fun inside => by
    obtain ⟨i,bound,equal⟩ := inside
    exact outside (.inl ⟨i,by omega,equal⟩)))

#print axioms core_of_effect

/-- The tested entry assertion establishes the initialized core and byte
frame through actual Kraken execution. The unpublished parent word is not
decoded at this boundary; its value belongs to the following segment. -/
theorem initialization_core_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names world machine key cidr pid base}
    (checked : boundary names nodeOffsets world machine key cidr pid=.ok base) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsMutationImage.Add.entry+0x1ff ∧ registers machine.data.regs t.data.regs base=true ∧
      MappedLe machine.data.dmem t.data.dmem ∧
      Trie.decodeNode (names.allocated base).trie nodeOffsets t.data.dmem base=
        .ok (Trie.targetNode (newNode key cidr machine.data.regs.rbp.toNat (some pid))) ∧
      EqualOutside (EntryWrites names machine.data base) machine.data.dmem t.data.dmem) machine := by
  obtain ⟨memory,summary,execution⟩ := initialization_executes fetch decoder checked
  have result := core_of_effect (boundary_fields checked) summary
  apply eventually_weaken (instructionStep fetch) _ _ _ _ execution
  rintro t ⟨pc,mem,regs,mapped⟩
  exact ⟨pc,regs,mapped,mem ▸ result.1,mem ▸ result.2⟩

#print axioms initialization_core_checked
end Binary.Pair.Allowedips.NodeInit
