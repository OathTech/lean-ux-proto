import PairRemoveFirstBody
import PairRemoveSource
import PairIndexKinds

namespace Binary.Pair.Remove.First
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]
set_option maxRecDepth 2048

/-- Complete sequential removal under Kraken's permission-granting effect
judgment, from the executable entry check. Services and ELF interpretation
are named hypotheses; physical shape is derived from reconstruction. -/
theorem remove_checked (fetch : Int64 → Option Decoded) (decoder : IndexRemoveDecoderAgreement fetch)
    (trace : GuardedPc fetch) (bh : GuardedBh fetch)
    {n o c initial w owner ra final} (checked : Pre n o c initial w owner ra)
    (accepted : (WG.indexRemove owner).run w=.ok ((),final)) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (Post n o c initial ra final) initial := by
  obtain ⟨d,base,device,related,storage,owners,named,pc,arg⟩ := pre_facts checked
  obtain ⟨argument,facts⟩ := arg
  obtain ⟨layout,unique,_⟩ := validate_basic (reconstruct_components related).1
  have finalEq := source_effect device accepted
  obtain ⟨previous,read,flag⟩ := ownership_flag owners named
  have previousBound := word_bound read
  have wordRead := word_loadInt _ _ _ _ _ read
  rw [layout.hash,layout.pprev] at wordRead
  have physicalRead : initial.data.dmem.loadInt (.ofNat 64 (base+16)) 8=some ((BitVec.ofNat 64 previous).toNat : Int) := by
    simpa only [Nat.add_assoc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using wordRead
  have entryPc : initial.pc=codeEntry := by
    apply Int64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    exact pc
  have entered := start fetch decoder trace facts entryPc
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ entered
  rintro started ⟨pc,core⟩
  have guard := disable fetch decoder facts core layout named argument (.ofNat 64 previous) physicalRead
  apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc guard)
  rintro guarded ⟨pc,core,bp⟩
  by_cases zero : previous=0
  · have unhashed : d.indexTable.any (·.owner==owner)=false := by simpa [zero] using flag.symm
    have filter : d.indexTable.filter (fun e => !(e.owner==owner))=d.indexTable := by
      apply List.filter_eq_self.mpr
      intro e member
      have absent := List.any_eq_false.mp unhashed e member
      simp only [absent,Bool.not_false]
    have updated : ({d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))} : Device)=d := by
      rw [filter]
    have atTail : guarded.pc=codeEntry+0x48 := by simpa [zero] using pc
    have tail := finish fetch decoder trace bh facts core
    apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ (Callback.at_pc atTail tail)
    rintro t ⟨returned,ready,frame⟩
    have heapFrame := external_storage facts.geometry frame
    refine ⟨returned,ready,⟨d,?_,heapFrame.reconstruct related,?_⟩,?_,heapFrame.kinds layout⟩
    · rw [finalEq]
      change some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}=some d
      rw [updated]
    · rw [←heapFrame.ownership layout]
      exact owners
    · intro a outside
      exact frame a (fun h => outside (.inr h))
  · have different : (previous != 0 : Bool)=true := by simpa only [bne_iff_ne] using zero
    have hashed : d.indexTable.any (·.owner==owner)=true := flag.symm.trans different
    obtain ⟨entry,member,ownerCheck⟩ := List.any_eq_true.mp hashed
    have ownerEq : entry.owner=owner := eq_of_beq ownerCheck
    obtain ⟨f,entryEq⟩ := reconstruct_focus related member
    have focusOwner : f.entry.owner=owner := by rw [entryEq]; exact ownerEq
    have focusNamed : (owner,f.removed-o.hash) ∈ n.owners := by rw [←focusOwner]; exact f.fields.named
    have baseEq := unique_first unique named focusNamed
    have removed : f.removed=base+8 := by have valid := f.fields.valid; rw [layout.hash] at baseEq valid; omega
    have prevEq : previous=f.previous := by
      have focusRead := f.fields.back
      rw [removed] at focusRead
      rw [layout.hash] at read
      exact word_values read focusRead
    have initialArg : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 base := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,←argument,Nat.mod_eq_of_lt initial.data.regs.rsi.toNat_lt_size]
    have cursor : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 f.removed := by
      rw [initialArg,removed,BitVec.ofNat_add]
      rfl
    have nonzero : BitVec.ofNat 64 previous≠0 := by
      intro equal
      apply zero
      have values := congrArg BitVec.toNat equal
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using values
    rw [ite_eq_right nonzero] at pc
    have splice := body fetch decoder trace facts core layout f cursor (by rw [bp,prevEq])
    apply eventually_trans (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ (Callback.at_pc pc splice)
    rintro unlinked ⟨pc,core⟩
    have tail := finish fetch decoder trace bh facts core
    apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ (Callback.at_pc pc tail)
    rintro t ⟨returned,ready,frame⟩
    have heapFrame := external_storage facts.geometry frame
    have reconstructed := heapFrame.reconstruct (f.reconstruct related storage)
    have ownership := (heapFrame.ownership layout).symm.trans (f.ownership (reconstruct_components related).1 storage owners)
    refine ⟨returned,ready,⟨_,?_,reconstructed,ownership⟩,(unlink_heap_frame layout f).trans frame,?_⟩
    · rw [finalEq]
      change some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}=
        some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==f.entry.owner))}
      rw [focusOwner]
    · apply KindFrame.trans _ (heapFrame.kinds layout)
      intro owner base named path
      rw [layout.kind]
      exact f.read_data layout storage path (.entry owner base 24 4 named (.inr (.inl rfl)))

#print axioms remove_checked
end Binary.Pair.Remove.First
