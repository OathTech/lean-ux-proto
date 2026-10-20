import PairWordStore

namespace Binary.Pair

/-- Ordered effects can be reordered only after proving byte disjointness.
This also covers modular addresses; it does not presume non-wrapping bases. -/
theorem storeInt_commute (memory : DataMem) (first second : BitVec 64)
    (firstSize secondSize : Nat) (firstValue secondValue : Int)
    (apart : ∀ a, InRange first firstSize a → ¬InRange second secondSize a) :
    (memory.storeInt first firstSize firstValue).storeInt second secondSize secondValue=
      (memory.storeInt second secondSize secondValue).storeInt first firstSize firstValue := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  by_cases present : address ∈ (Int.toBytes firstSize firstValue).At first
  · have absent : address ∉ (Int.toBytes secondSize secondValue).At second := by
      intro other
      apply apart address
      · simpa only [Int.toBytes_length,InRange] using (mem_At_iff _ _ _).mp present
      · simpa only [Int.toBytes_length,InRange] using (mem_At_iff _ _ _).mp other
    simp only [Mem.storeInt,Mem.storeBytes,Std.ExtHashMap.union_eq,Std.ExtHashMap.getElem?_union,
      Std.ExtHashMap.getElem?_eq_none absent,Option.none_or]
  · simp only [Mem.storeInt,Mem.storeBytes,Std.ExtHashMap.union_eq,Std.ExtHashMap.getElem?_union,
      Std.ExtHashMap.getElem?_eq_none present,Option.none_or]

theorem write64_offsets_commute (memory : DataMem) (base first second firstValue secondValue : Nat)
    (firstBound : first+8≤2^64) (secondBound : second+8≤2^64)
    (apart : first+8≤second ∨ second+8≤first) :
    write64 (write64 memory (base+first) firstValue) (base+second) secondValue=
      write64 (write64 memory (base+second) secondValue) (base+first) firstValue := by
  apply storeInt_commute
  simpa only [BitVec.ofNat_add] using
    InRange.offset_disjoint (.ofNat 64 base) first 8 second 8 firstBound secondBound apart

#print axioms storeInt_commute
#print axioms write64_offsets_commute
end Binary.Pair
