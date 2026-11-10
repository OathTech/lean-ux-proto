import C1ServiceStubContract

/-! Result C1, work package 4: the stub's `Idle` holds of actual memories.
`install base stream` writes the allocator's bytes over any memory whose two
bytes beside the state byte are unmapped; the stub is then idle with nothing
handed out and `stream` pending. (A piece of `Witness`: its starting state
needs `Idle … [] (five outcomes)`.) -/
namespace Binary.Statements.C1.Stub
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

def outcomeByte (record : HiddenRecord) : UInt8 := if record.bytes.head? = some 1 then 1 else 0

/-- The allocator's bytes: the count 0, the outcome bytes, and the objects' pages zeroed. -/
def install (base : Mem 64) (stream : List HiddenRecord) : Mem 64 :=
  ((base.storeBytes (.ofNat 64 state) [0]).storeBytes (.ofNat 64 table) (stream.map outcomeByte)).storeBytes
    (.ofNat 64 objects) (List.replicate (128*slots) 0)

theorem storeBytes_frame (m : Mem 64) (base : BitVec 64) (bytes : List UInt8) :
    EqualOutside (InRange base bytes.length) m (m.storeBytes base bytes) := by
  intro address outside
  have absent : address ∉ bytes.At base := by
    intro present
    rw [mem_At_iff] at present
    exact outside present
  have missing := Std.ExtHashMap.getElem?_eq_none absent
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, missing, Option.none_or]

/-- A natural-number address outside a stored range. -/
theorem outside_range (start length x : Nat) (apart : x < start ∨ start + length ≤ x)
    (small : start + length < 2^64) (bound : x < 2^64) :
    ¬InRange (.ofNat 64 start) length (.ofNat 64 x) := by
  rintro ⟨j,inside,equal⟩
  have numbers := congrArg BitVec.toNat equal
  simp only [← BitVec.ofNat_add, BitVec.toNat_ofNat] at numbers
  omega

theorem idle_initial (base : Mem 64) (stream : List HiddenRecord) (fits : stream.length ≤ slots)
    (before : base.get? (.ofNat 64 (state-1)) = none) (after : base.get? (.ofNat 64 (state+1)) = none) :
    Idle (install base stream) [] stream := by
  simp only [slots] at fits
  have length : (stream.map outcomeByte).length = stream.length := List.length_map _
  have objectsFrame := storeBytes_frame
    ((base.storeBytes (.ofNat 64 state) [0]).storeBytes (.ofNat 64 table) (stream.map outcomeByte))
    (.ofNat 64 objects) (List.replicate (128*slots) 0)
  have tableFrame := storeBytes_frame (base.storeBytes (.ofNat 64 state) [0]) (.ofNat 64 table)
    (stream.map outcomeByte)
  have stateFrame := storeBytes_frame base (.ofNat 64 state) [0]
  simp only [List.length_replicate, length] at objectsFrame tableFrame
  have beside (x : Nat) (place : x = state-1 ∨ x = state+1) :
      (install base stream).get? (.ofNat 64 x) = base.get? (.ofNat 64 x) := by
    unfold install
    rw [← objectsFrame _ (outside_range _ _ x (by simp only [state, objects, slots] at *; omega) (by decide)
        (by simp only [state] at *; omega)),
      ← tableFrame _ (outside_range _ _ x (by simp only [state, table] at *; omega)
        (by simp only [table]; omega) (by simp only [state] at *; omega)),
      ← stateFrame _ (outside_range _ _ x (by simp only [state, List.length] at *; omega) (by decide)
        (by simp only [state] at *; omega))]
  refine ⟨0,?_,by simp only [slots]; omega,?_,?_,?_,?_,fun _ member => nomatch member⟩
  · have self : (base.storeBytes (.ofNat 64 state) [0]).loadBytes (.ofNat 64 state) 1 = some [0] :=
      loadBytes_store_self base (.ofNat 64 state) [0] (by decide)
    unfold install Mem.loadInt
    rw [← objectsFrame.loadBytes _ 1 (fun i small => by
        rw [← BitVec.ofNat_add]
        exact outside_range _ _ _ (by simp only [state, objects, slots]; omega) (by decide)
          (by simp only [state]; omega)),
      ← tableFrame.loadBytes _ 1 (fun i small => by
        rw [← BitVec.ofNat_add]
        exact outside_range _ _ _ (by simp only [state, table]; omega) (by simp only [table]; omega)
          (by simp only [state]; omega)),
      self]
    rfl
  · rw [beside _ (.inl rfl)]
    exact before
  · rw [beside _ (.inr rfl)]
    exact after
  · intro i bound
    unfold install Mem.loadInt
    rw [← objectsFrame.loadBytes _ 1 (fun j small => by
        rw [← BitVec.ofNat_add]
        exact outside_range _ _ _ (by simp only [table, objects, slots]; omega) (by decide)
          (by simp only [table]; omega))]
    have slice := MemoryBytes.loadBytes_store_slice (base.storeBytes (.ofNat 64 state) [0])
      (.ofNat 64 table) (stream.map outcomeByte) (by rw [length]; omega) i 1 (by rw [length]; omega)
    rw [← BitVec.ofNat_add] at slice
    rw [show table + (0 + i) = table + i by omega, slice]
    have one : ((stream.map outcomeByte).drop i).take 1 = [outcomeByte stream[i]] := by
      rw [List.drop_eq_getElem_cons (by rw [length]; exact bound)]
      simp
    rw [one]
    unfold outcomeByte outcome
    split <;> rfl
  · intro i bound _
    simp only [readNat]
    have slice := MemoryBytes.loadBytes_store_slice
      ((base.storeBytes (.ofNat 64 state) [0]).storeBytes (.ofNat 64 table) (stream.map outcomeByte))
      (.ofNat 64 objects) (List.replicate (128*slots) 0)
      (by simp only [List.length_replicate, slots]; omega) (128*i) nodeSize
      (by simp only [List.length_replicate, slots, nodeSize]; omega)
    rw [← BitVec.ofNat_add] at slice
    unfold install
    rw [show slot (0 + i) = objects + 128 * i by simp only [slot]; omega, slice]
    have zeros : ((List.replicate (128*slots) (0 : UInt8)).drop (128*i)).take nodeSize =
        List.replicate nodeSize 0 := by
      rw [List.drop_replicate, List.take_replicate]
      congr 1
      simp only [slots, nodeSize]
      omega
    rw [zeros]
    rfl

#print axioms idle_initial
end Binary.Statements.C1.Stub
