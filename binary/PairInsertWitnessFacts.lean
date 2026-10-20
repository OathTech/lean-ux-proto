import PairInsertAdequacy
import PairInsertCheckComplete
import PairInsertWitnessState
import PairRemoveWitness

namespace Binary.Pair.Insert.Witness
open Leanux Leanux.WG TrustBase Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private instance [DecidableEq α] (x : Except ε α) (v : α) : Decidable (x=.ok v) :=
  match x with
  | .error e => .isFalse (by intro h; cases h)
  | .ok actual => decidable_of_iff (actual=v) (by simp)

theorem cells_absent (cells : List (BitVec 64 × UInt8)) (base : DataMem) (a : BitVec 64)
    (absent : cells.find? (·.1==a)=none) :
    base.get? a=(cells.foldr (fun (a,b) m => m.insert a b) base).get? a := by
  simp only [Std.ExtHashMap.get?_eq_getElem?,Remove.Witness.cells_read,absent,
    Option.map_none,Option.none_or]

theorem cells_present (cells : List (BitVec 64 × UInt8)) (base : DataMem) (a : BitVec 64)
    (b : UInt8) (present : (a,b) ∈ cells) :
    ((cells.foldr (fun (a,b) m => m.insert a b) base).get? a).isSome=true := by
  cases found : cells.find? (·.1==a) with
  | none => exact False.elim ((List.find?_eq_none.mp found) (a,b) present (by simp))
  | some cell => simp only [Std.ExtHashMap.get?_eq_getElem?,Remove.Witness.cells_read,
      found,Option.map_some,Option.some_or,Option.isSome_some]

theorem stack_mapped (linked : Bool) (i : Nat) (bound : i<135) :
    ((memory linked).loadInt (.ofNat 64 stackAddr-.ofNat 64 ((i+1)*8)) 8).isSome=true := by
  apply (loadInt_defined _ _ _).mpr
  intro j hj
  let offset := 1080-(i+1)*8+j
  have small : offset<1080 := by dsimp only [offset]; omega
  have equal : BitVec.ofNat 64 (stackAddr-1080+offset)=
      BitVec.ofNat 64 stackAddr-BitVec.ofNat 64 ((i+1)*8)+BitVec.ofNat 64 j := by
    rw [BitVec.ofNat_sub_ofNat_of_le stackAddr ((i+1)*8) (by omega) (by change (i+1)*8≤0x400800; omega),
      ←BitVec.ofNat_add]
    congr 1
    change 0x400800-1080+(1080-(i+1)*8+j)=0x400800-(i+1)*8+j
    omega
  apply cells_present extraCells (Remove.Witness.memory linked) _ 0
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨(stackAddr-1080,1080),List.mem_append_right _ List.mem_cons_self,?_⟩
  exact List.mem_map.mpr ⟨offset,List.mem_range.mpr small,Prod.ext equal rfl⟩

theorem extra_outside : ∀ cell ∈ extraCells,
    (cell.1.toNat<0x100000 ∨ 0x110000≤cell.1.toNat) ∧
    (cell.1.toNat<0x700000 ∨ 0x700020≤cell.1.toNat) := by
  intro cell member
  have explicit : extraWords.all (fun (a,size,_) => a+size≤2^64 &&
      (a+size≤0x100000 || 0x110000≤a) && (a+size≤0x700000 || 0x700020≤a))=true := by decide +kernel
  have zeroes : (config.blocks++[(stackAddr-1080,1080)]).all (fun (a,size) => a+size≤2^64 &&
      (a+size≤0x100000 || 0x110000≤a) && (a+size≤0x700000 || 0x700020≤a))=true := by decide +kernel
  have bound (base size i : Nat) (hi : i<size)
      (checked : ((base+size≤2^64 ∧ (base+size≤0x100000 ∨ 0x110000≤base)) ∧
        (base+size≤0x700000 ∨ 0x700020≤base))) :
      ((BitVec.ofNat 64 (base+i)).toNat<0x100000 ∨ 0x110000≤(BitVec.ofNat 64 (base+i)).toNat) ∧
      ((BitVec.ofNat 64 (base+i)).toNat<0x700000 ∨ 0x700020≤(BitVec.ofNat 64 (base+i)).toNat) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  rcases List.mem_append.mp member with member | member
  · obtain ⟨⟨base,size,value⟩,named,member⟩ := List.mem_flatMap.mp member
    obtain ⟨i,hi,equal⟩ := List.mem_mapIdx.mp member
    have checked := List.all_eq_true.mp explicit (base,size,value) named
    rw [←equal]
    exact bound base size i (by simpa only [Int.toBytes_length] using hi)
      (by simpa only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] using checked)
  · obtain ⟨⟨base,size⟩,named,member⟩ := List.mem_flatMap.mp member
    obtain ⟨i,hi,equal⟩ := List.mem_map.mp member
    have checked := List.all_eq_true.mp zeroes (base,size) named
    rw [←equal]
    exact bound base size i (List.mem_range.mp hi)
      (by simpa only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] using checked)

theorem storage_frame (linked : Bool) :
    StorageFrame names offsets (Remove.Witness.memory linked) (memory linked) := by
  intro span member a inside
  have bounds := Span.location (storage_bounds (by decide : storageCheck names offsets=true) member).2 inside
  have possible : span=(0x100000,65536) ∨ span=(0x700000,32) := by
    simpa only [names,offsets,Remove.Witness.names,Remove.Witness.offsets,storageSpans,
      List.map_cons,List.map_nil,List.append_nil,List.mem_cons,List.not_mem_nil,or_false] using member
  have absent : extraCells.find? (·.1==a)=none := by
    apply List.find?_eq_none.mpr
    intro cell member
    have outside := extra_outside cell member
    have different : cell.1≠a := by
      intro equal
      rw [equal] at outside
      rcases possible with equal | equal <;> rw [equal] at bounds <;> dsimp only at bounds <;> omega
    simpa only [beq_iff_eq] using different
  exact cells_absent extraCells (Remove.Witness.memory linked) a absent

def byteList (linked : Bool) (a : BitVec 64) (size : Nat) : Option (List UInt8) :=
  ((List.range size).map fun i =>
    (((extraCells.find? (·.1==a+.ofNat 64 i)).map Prod.snd).or
      ((((Remove.Witness.cells linked).find? (·.1==a+.ofNat 64 i)).map Prod.snd).or
        (if ((a+.ofNat 64 i)-0x100000).toNat<65536 then some 0 else none)))).allSome

theorem memory_load (linked : Bool) (a : BitVec 64) (size : Nat) :
    (memory linked).loadBytes a size=byteList linked a size := by
  simp only [byteList,Mem.loadBytes,memory,Remove.Witness.memory,Std.ExtHashMap.get?_eq_getElem?,
    Remove.Witness.cells_read,Remove.Witness.table_read]

theorem asserted (linked : Bool) : Remove.assertAt names offsets (memory linked) (world linked)=.ok () := by
  have frame := storage_frame linked
  apply remove_assert_of_parts (n := names) (o := offsets) (m := memory linked)
    (w := world linked) (d := device linked) rfl (by decide)
    (frame.reconstruct (Remove.Witness.related linked))
  rw [←frame.ownership (validate_basic (by decide : names.validate offsets=.ok ())).1]
  exact Remove.Witness.owned linked

theorem call_frame_for_memory (linked wide : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size) :
    Index.callFrameCheck names offsets context (frameState m) (.ofNat stopAddr) (if wide then 135 else 7)=.ok () := by
  apply Index.callFrameCheck_intro
  · simp only [frameState,Remove.Witness.frameState,Mem.loadInt,reads,byteList]
    cases linked <;> decide +kernel
  · apply List.all_eq_true.mpr
    intro i member
    have bound : i<135 := by
      have := List.mem_range.mp member
      cases wide <;> simp only [Bool.false_eq_true,↓reduceIte] at this <;> omega
    change (m.loadInt (.ofNat 64 stackAddr-.ofNat 64 ((i+1)*8)) 8).isSome=true
    simpa only [Mem.loadInt,reads,memory_load] using stack_mapped linked i bound
  · simp only [Trie.coverageCheck,Trie.coverageDataCheck,frameState,Remove.Witness.frameState,
      load64,load32,Mem.loadInt,reads,byteList]
    cases linked <;> decide +kernel
  · decide +kernel
  · simp only [frameState,Remove.Witness.frameState,Mem.loadInt,reads,byteList]
    cases linked <;> decide +kernel
  all_goals
    simp only [Index.callStack,frameState,Remove.Witness.frameState]
    cases wide <;> decide +kernel

theorem call_frame (linked wide : Bool) :
    Index.callFrameCheck names offsets context (state linked) (.ofNat stopAddr) (if wide then 135 else 7)=.ok () :=
  call_frame_for_memory linked wide (memory linked) (memory_load linked)

theorem resident_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size) :
    Resident names offsets m (.keypair 0) 0x700000 := by
  refine ⟨List.mem_cons_self,?_,⟨0,?_⟩,⟨0,?_⟩⟩
  all_goals
    simp only [word,reads,byteList]
    cases linked <;> decide +kernel

theorem nested_for_memory (linked : Bool) (m : DataMem)
    (reads : ∀ a size, m.loadBytes a size=byteList linked a size) :
    (CommonBitsCoverage.Context.mk context.coverage (context.preempt+1024)).CoverageAt m := by
  apply Trie.coverageDataCheck_sound
  simp only [Trie.coverageDataCheck,load64,load32,Mem.loadInt,reads,byteList]
  cases linked <;> decide +kernel

end Binary.Pair.Insert.Witness
