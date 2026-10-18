import PairReplaceEnvironment
import PairReplaceWitnessState
import PairRemoveWitness

namespace Binary.Pair.Replace.Witness
open Leanux Leanux.WG TrustBase Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Remove.Witness (cells_read table_read mapM_values)

theorem memory_load (linked : Bool) (a : BitVec 64) (size : Nat) :
    (memory linked).loadBytes a size=
      ((List.range size).map fun i =>
        (((cells linked).find? (·.1==a+.ofNat 64 i)).map Prod.snd).or
          (if ((a+.ofNat 64 i)-0x100000).toNat<65536 then some 0 else none)).allSome := by
  simp only [Mem.loadBytes,memory,Std.ExtHashMap.get?_eq_getElem?,cells_read,
    table_read]

private instance [DecidableEq α] (x : Except ε α) (v : α) : Decidable (x=.ok v) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok actual => decidable_of_iff (actual=v) (by simp)

theorem cells_outside (linked : Bool) : ∀ c ∈ cells linked,
    c.1.toNat<0x100008 ∨ 0x110000≤c.1.toNat := by
  have checked : (cells linked).all (fun c => c.1.toNat<0x100008 || 0x110000≤c.1.toNat)=true := by
    cases linked <;> decide +kernel
  intro c member
  simpa only [Bool.or_eq_true,decide_eq_true_eq] using List.all_eq_true.mp checked c member

theorem empty_byte (linked : Bool) (a : BitVec 64)
    (within : 0x100008≤a.toNat ∧ a.toNat<0x110000) : (memory linked)[a]?=some 0 := by
  have absent : (cells linked).find? (·.1==a)=none := by
    apply List.find?_eq_none.mpr
    intro c member
    have outside := cells_outside linked c member
    have different : c.1≠a := by intro equal; rw [equal] at outside; omega
    simpa only [beq_iff_eq] using different
  simp only [memory,cells_read,absent,Option.map_none,Option.none_or,table_read]
  have lower : (0x100000 : BitVec 64)≤a := by change 0x100000≤a.toNat; omega
  rw [BitVec.toNat_sub_of_le lower]
  simp only [show (0x100000 : BitVec 64).toNat=0x100000 from rfl]
  rw [ite_eq_left (by omega)]

theorem empty_head (linked : Bool) (b : Nat) (positive : 0<b) (valid : b<8192) :
    word (memory linked) s!"bucket[{b}].head" (tableHead names offsets b) 8=.ok 0 := by
  have address : tableHead names offsets b=0x100000+b*8 := rfl
  rw [address]
  apply Trie.word_of_loadInt _ (by omega)
  have bytes : (memory linked).loadBytes (.ofNat 64 (0x100000+b*8)) 8=some (List.replicate 8 0) := by
    apply (MemoryBytes.loadBytes_iff _ _ _ _).mpr
    refine ⟨by simp,?_⟩
    intro i bound
    have small : i<8 := by simpa using bound
    have pos : (BitVec.ofNat 64 (0x100000+b*8)+BitVec.ofNat 64 i).toNat=0x100000+b*8+i := by
      rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    simpa only [List.getElem_replicate,Std.ExtHashMap.get?_eq_getElem?] using empty_byte linked
      (BitVec.ofNat 64 (0x100000+b*8)+BitVec.ofNat 64 i) (by rw [pos]; omega)
  rw [Mem.loadInt,bytes]
  rfl

theorem bucket_zero_checked (linked : Bool) :
    decodeBucket names offsets (memory linked) 0=.ok ((device linked).indexTable) := by
  simp only [decodeBucket,bucket,word,memory_load]
  cases linked <;> decide +kernel

theorem bucket_checked (linked : Bool) (b : Nat) (valid : b<8192) :
    decodeBucket names offsets (memory linked) b=
      .ok ((device linked).indexTable.filter (fun e => e.index%8192==b)) := by
  by_cases zero : b=0
  · subst b
    rw [bucket_zero_checked]
    cases linked <;> rfl
  · unfold decodeBucket
    rw [empty_head linked b (by omega) valid]
    change bucket names offsets (memory linked) b _ 0 _ [] = _
    rw [bucket_zero]
    cases linked <;> simp [device,Ne.symm zero]

theorem related (linked : Bool) : Corresponds names offsets (memory linked) (device linked) := by
  have validation : names.validate offsets=.ok () := by decide +kernel
  have owners : decodeOwners names offsets (memory linked)=.ok ((target (device linked)).ownerWords) := by
    simp only [decodeOwners,word,memory_load]
    cases linked <;> decide +kernel
  have counts : decodeCounts names offsets (memory linked)=.ok ((target (device linked)).refcounts) := by
    simp only [decodeCounts,word,memory_load]
    cases linked <;> decide +kernel
  have buckets := mapM_values (xs := List.range 8192)
    (fun b member => bucket_checked linked b (List.mem_range.mp member))
  apply reconstruct_of_components validation _ owners counts
  simpa only [target,Id.run,Pure.pure,Array.toList_map,List.toList_toArray] using buckets

theorem owned (linked : Bool) : Remove.ownership names offsets (memory linked)=.ok (Remove.targetOwnership (device linked)) := by
  simp only [Remove.ownership,word,memory_load]
  cases linked <;> decide +kernel

theorem asserted (linked : Bool) : Remove.assertAt names offsets (memory linked) (world linked)=.ok () :=
  remove_assert_of_parts (n := names) (o := offsets) (m := memory linked)
    (w := world linked) (d := device linked) rfl (by decide +kernel) (related linked) (owned linked)

theorem frame_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=
      ((List.range size).map fun i =>
        (((cells linked).find? (·.1==a+.ofNat 64 i)).map Prod.snd).or
          (if ((a+.ofNat 64 i)-0x100000).toNat<65536 then some 0 else none)).allSome) :
    Index.callFrameCheck names offsets context (frameState m) (.ofNat stopAddr) 5=.ok () := by
  apply Index.callFrameCheck_intro
  · simp only [frameState,Mem.loadInt,reads]
    cases linked <;> decide +kernel
  · simp only [frameState,Mem.loadInt,reads]
    cases linked <;> decide +kernel
  · simp only [Trie.coverageCheck,Trie.coverageDataCheck,frameState,load64,load32,Mem.loadInt,reads]
    cases linked <;> decide +kernel
  · decide +kernel
  · simp only [frameState,Mem.loadInt,reads]
    cases linked <;> decide +kernel
  · simp only [Index.callStack,frameState]
    decide +kernel
  · simp only [Index.callStack,frameState]
    decide +kernel
  · simp only [Index.callStack,frameState]
    decide +kernel
  · simp only [Index.callStack,frameState]
    decide +kernel

theorem frameState_memory (m : DataMem) : (frameState m).data.dmem=m := rfl

theorem pre_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=
      ((List.range size).map fun i =>
        (((cells linked).find? (·.1==a+.ofNat 64 i)).map Prod.snd).or
          (if ((a+.ofNat 64 i)-0x100000).toNat<65536 then some 0 else none)).allSome)
    (related : Corresponds names offsets m (device linked))
    (owned : Remove.ownership names offsets m=.ok (Remove.targetOwnership (device linked))) :
    Pre names offsets context (frameState m) (world linked) 0 0 (.ofNat stopAddr) := by
  apply @pre_of_parts names offsets context (frameState m) (world linked) 0 0 (.ofNat stopAddr)
    (device linked) 0x6000e0 0x700000
  · rw [frameState_memory]
    exact remove_assert_of_parts (n := names) (o := offsets) (m := m) (w := world linked)
      (d := device linked) rfl (by decide +kernel) related owned
  · decide +kernel
  · decide +kernel
  · simp only [frameState]
    decide +kernel
  · rfl
  · intro _
    refine ⟨?_,?_,⟨0,?_⟩,⟨0,?_⟩⟩
    · cases linked <;> decide +kernel
    all_goals simp only [frameState,word,reads]; cases linked <;> decide +kernel
  · exact frame_for_memory linked m reads

theorem check (linked : Bool) : Pre names offsets context (state linked) (world linked) 0 0 (.ofNat stopAddr) :=
  pre_for_memory linked (memory linked) (memory_load linked) (related linked) (owned linked)

theorem check_unhashed : Pre names offsets context (state false) (world false) 0 0 (.ofNat stopAddr) := check false

theorem check_linked : Pre names offsets context (state true) (world true) 0 0 (.ofNat stopAddr) := check true

theorem executes (linked : Bool) (fetch : Int64 → Option Decoded)
    (decoder : IndexReplaceDecoderAgreement fetch) (trace : TracePcContract fetch)
    (bh : BhEnableContract fetch) :
    Eventually (instructionStep fetch)
      (Post names offsets context (state linked) (.ofNat stopAddr) (sourceAnswer (device linked) 0)
        (sourceFinal (world linked) (device linked) 0 0)) (state linked) :=
  replace_checked fetch decoder trace bh (check linked)
    (source_run (world linked) (device linked) 0 0 rfl)

#print axioms check_unhashed
#print axioms check_linked
#print axioms executes
end Binary.Pair.Replace.Witness
