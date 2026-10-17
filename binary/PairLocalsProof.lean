import PairHeapProof
import AllowedipsChild

namespace Binary.Pair.Trie
open Leanux Leanux.WG
set_option maxRecDepth 2048

private theorem byte_sum (bytes : List UInt8) (start : Nat) :
    ((bytes.zipIdx start).map fun (b,i) => b.toNat * 256^i).sum = Nat.ofBytes bytes * 256^start := by
  induction bytes generalizing start with
  | nil => simp [Nat.ofBytes]
  | cons b bs ih =>
    simp only [List.zipIdx_cons,List.map_cons,List.sum_cons,ih,Nat.ofBytes_cons,Nat.pow_succ,Nat.add_mul,Nat.mul_assoc]
    ac_rfl

private theorem bytes_cast (bytes : List UInt8) : Int.ofBytes bytes = (Nat.ofBytes bytes : Int) := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => simp only [Int.ofBytes_cons,Nat.ofBytes_cons,ih,Int.natCast_add,Int.natCast_mul]; rfl

theorem readNat_loadInt {s : MachineState} {a size value : Nat}
    (ok : readNat s a size = .ok value) : s.data.dmem.loadInt (.ofNat 64 a) size = some (value : Int) := by
  unfold readNat at ok
  cases read : s.data.dmem.loadBytes (.ofNat 64 a) size with
  | none => rw [read] at ok; cases ok
  | some bytes =>
    rw [read] at ok
    have equal := Except.ok.inj ok
    rw [byte_sum] at equal
    simp only [Nat.pow_zero,Nat.mul_one] at equal
    simp only [Mem.loadInt,read,Option.map_some,bytes_cast,equal]

structure LocalFields (names : Names) (s : MachineState) (bits query : Nat)
    (current found : Option NodeId) : Prop where
  cursor : s.data.regs.rbx.toBitVec = AllowedipsRelation.pointer (interpretation names.nodes) current
  previous : s.data.regs.rbp.toBitVec = AllowedipsRelation.pointer (interpretation names.nodes) found
  stack : s.data.regs.rsp.toNat = stackAddr-80
  width : (s.data.regs.get (.low .r12 .W8)).toNat = bits
  family : s.data.regs.get (.low .r13 .W8) = .ofNat 8 bits
  query : AllowedipsChild.QueryWords s.data.dmem (s.data.regs.rsp.toBitVec+16) bits query

theorem u64_of_nat {r : UInt64} {n : Nat} (eq : r.toNat = n) : r.toBitVec = .ofNat 64 n := by
  rw [←eq]
  change r.toBitVec = .ofNat 64 r.toBitVec.toNat
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem locals_fields {names : Names} {input : AllowedipsProbe.Input} {s : MachineState}
    {root current found : Option NodeId} {bits query : Nat} (family : bits = 32 ∨ bits = 128)
    (ok : locals names input s root bits query current found = .ok ()) :
    LocalFields names s bits query current found := by
  unfold locals at ok
  obtain ⟨cur,curOk,ok⟩ := bind_ok ok
  obtain ⟨cursor,ok⟩ := check_ok _ _ _ _ ok
  obtain ⟨prev,prevOk,ok⟩ := bind_ok ok
  obtain ⟨previous,ok⟩ := check_ok _ _ _ _ ok
  obtain ⟨registers,ok⟩ := check_ok _ _ _ _ ok
  obtain ⟨savedRoot,_,ok⟩ := bind_ok ok
  obtain ⟨rootAddress,_,ok⟩ := bind_ok ok
  obtain ⟨rootEqual,ok⟩ := check_ok _ _ _ _ ok
  have regs : (s.data.regs.rsp.toNat = stackAddr-80 ∧ s.data.regs.r12.toNat = bits) ∧
      s.data.regs.r13.toNat = bits := by simpa only [Bool.and_eq_true,beq_iff_eq] using registers
  have stack := u64_of_nat regs.1.1
  have queryAddr : s.data.regs.rsp.toBitVec+16 = .ofNat 64 (stackAddr-64) := by rw [stack]; rfl
  refine ⟨(u64_of_nat (eq_of_beq cursor)).trans (address_value curOk).symm,
    (u64_of_nat (eq_of_beq previous)).trans (address_value prevOk).symm,regs.1.1,?_,?_,?_⟩
  · rcases family with rfl | rfl <;> simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take,regs.1.2]
  · apply BitVec.eq_of_toNat_eq
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take,regs.2]
  · rw [queryAddr]
    by_cases width : bits = 32
    · simp only [width,beq_self_eq_true,↓reduceIte] at ok
      obtain ⟨actual,queryRead,ok⟩ := bind_ok ok
      obtain ⟨queryEqual,ok⟩ := check_ok _ _ _ _ ok
      have equal : actual = query := eq_of_beq queryEqual
      subst actual
      simp only [AllowedipsChild.QueryWords,width,↓reduceIte]
      exact readNat_loadInt queryRead
    · simp only [show (bits == 32) = false from by simp [width],pure_bind] at ok
      obtain ⟨hi,hiRead,ok⟩ := bind_ok ok
      obtain ⟨lo,loRead,ok⟩ := bind_ok ok
      obtain ⟨queryEqual,ok⟩ := check_ok _ _ _ _ ok
      have equal : hi*2^64+lo = query := eq_of_beq queryEqual
      have lowBound := (loadInt_range _ _ _ _ (readNat_loadInt loRead)).2
      have lowBound' : lo < 2^64 := by exact_mod_cast lowBound
      have high : query / 2^64 = hi := by omega
      have low : query % 2^64 = lo := by omega
      simp only [AllowedipsChild.QueryWords,width,↓reduceIte,high,low]
      exact ⟨readNat_loadInt hiRead,readNat_loadInt loRead⟩

#print axioms locals_fields
end Binary.Pair.Trie
