import AllowedipsLoopCommonCall
import AllowedipsSourceBody

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- Concrete helper input assembled from the current ABI registers and the
source key values. No saved-memory or future execution is supplied. -/
def input (s : MachineData) (bits stored query : Nat) : CommonBits.Input := {
  node := s.regs.rdi, key := s.regs.rsi, stack := s.regs.rsp-40
  family := .ofNat 8 bits
  stored32 := .ofNat stored, query32 := .ofNat query
  storedHigh := .ofNat (stored/2^64), queryHigh := .ofNat (query/2^64)
  storedLow := .ofNat (stored%2^64), queryLow := .ofNat (query%2^64)
  savedBx := s.regs.rbx, savedBp := s.regs.rbp, savedR12 := s.regs.r12, savedR13 := s.regs.r13
  returnAddress := (AllowedipsImage.Lookup.entry+0xea).toUInt64 }

theorem xor_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have equal := congrArg (fun n => a ^^^ n) h
    simpa only [←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor,Nat.xor_zero] using equal.symm
  · intro h
    rw [h,Nat.xor_self]

theorem high_bound (n : Nat) (bound : n < 2^128) : n/2^64 < 2^64 := by omega

theorem input_high_eq (s : MachineData) (stored query : Nat)
    (storedBound : stored < 2^128) (queryBound : query < 2^128) :
    (input s 128 stored query).storedHigh = (input s 128 stored query).queryHigh ↔
      stored/2^64 = query/2^64 := by
  rw [←UInt64.toNat_inj]
  simp only [input,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (high_bound stored storedBound),
    Nat.mod_eq_of_lt (high_bound query queryBound)]

/-- The helper's AL result is exactly the source natural result. Higher EAX
bits deliberately play no part: the IPv6 binary returns a signed seed there. -/
theorem input_result (s : MachineData) (bits stored query : Nat)
    (family : bits = 32 ∨ bits = 128) (storedBound : stored < 2^bits) (queryBound : query < 2^bits) :
    (input s bits stored query).result = common bits stored query := by
  rcases family with rfl | rfl
  · simp [CommonBits.Input.result,input,common,UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt storedBound,Nat.mod_eq_of_lt queryBound]
  · have highEq := input_high_eq s stored query storedBound queryBound
    simp only [CommonBits.Input.result,show (input s 128 stored query).family = 128 from rfl,
      ↓reduceIte]
    simp only [highEq]
    simp only [input,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (high_bound stored storedBound),
      Nat.mod_eq_of_lt (high_bound query queryBound),Nat.mod_mod,
      common,show ¬(128=32) by decide,↓reduceIte,Nat.xor_div_two_pow,Nat.xor_mod_two_pow]
    by_cases equal : stored/2^64 = query/2^64
    · simp [equal]
    · have nonzero : stored/2^64 ^^^ query/2^64 ≠ 0 := fun h => equal ((xor_zero_iff _ _).mp h)
      simp [equal,nonzero]

theorem input_keyWords32 (s : MachineData) (stored query : Nat)
    (storedBound : stored < 2^32) (queryBound : query < 2^32) :
    (input s 32 stored query).keyWords =
      [⟨s.regs.rdi.toBitVec+32,4,stored⟩,⟨s.regs.rsi.toBitVec,4,query⟩] := by
  simp [CommonBits.Input.keyWords,CommonBits.Input.words,input,UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt storedBound,Nat.mod_eq_of_lt queryBound]

theorem input_keyWords128 (s : MachineData) (stored query : Nat)
    (storedBound : stored < 2^128) (queryBound : query < 2^128) :
    (input s 128 stored query).keyWords =
      [⟨s.regs.rdi.toBitVec+32,8,((stored/2^64 : Nat) : Int)⟩,⟨s.regs.rsi.toBitVec,8,((query/2^64 : Nat) : Int)⟩] ++
      if stored/2^64 = query/2^64 then
        [⟨s.regs.rdi.toBitVec+40,8,((stored%2^64 : Nat) : Int)⟩,⟨s.regs.rsi.toBitVec+8,8,((query%2^64 : Nat) : Int)⟩]
      else [] := by
  have highEq := input_high_eq s stored query storedBound queryBound
  change (UInt64.ofNat (stored/2^64) = UInt64.ofNat (query/2^64)) ↔ _ at highEq
  simp [CommonBits.Input.keyWords,CommonBits.Input.words,input,highEq,UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (high_bound stored storedBound),Nat.mod_eq_of_lt (high_bound query queryBound)]

theorem input_keys (s : MachineData) (bits stored query : Nat)
    (family : bits = 32 ∨ bits = 128)
    (keyFields : KeyFields s.dmem (s.regs.rdi.toBitVec+32) bits stored query)
    (queryWords : AllowedipsChild.QueryWords s.dmem s.regs.rsi.toBitVec bits query) :
    CommonBits.ReadsAt (input s bits stored query).keyWords s.dmem := by
  obtain ⟨storedBound,queryBound,loaded⟩ := keyFields
  rcases family with rfl | rfl
  · rw [input_keyWords32 s stored query storedBound queryBound]
    intro word member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact loaded
    · exact queryWords
  · rw [input_keyWords128 s stored query storedBound queryBound]
    change s.dmem.loadInt (s.regs.rdi.toBitVec+32) 8 = some ((stored/2^64 : Nat) : Int) ∧
      (stored/2^64 = query/2^64 → s.dmem.loadInt (s.regs.rdi.toBitVec+32+8) 8 = some ((stored%2^64 : Nat) : Int)) at loaded
    intro word member
    rcases List.mem_append.mp member with high | low
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at high
      rcases high with rfl | rfl
      · exact loaded.1
      · exact queryWords.1
    · split at low
      next equal =>
        simp only [List.mem_cons,List.not_mem_nil,or_false] at low
        rcases low with rfl | rfl
        · simpa only [BitVec.add_assoc,show (32+8 : BitVec 64)=40 from rfl] using loaded.2 equal
        · exact queryWords.2
      next different => cases low

#print axioms input_result
#print axioms input_keys
end Binary.AllowedipsLoop
