import AllowedipsImage
import TrieChoice
import MemoryBytes
import Kraken.X64.OmniSemantics

namespace Binary.AllowedipsChild
open AllowedipsRelation
local instance : Labels := Image.linkedLabels

def run (s : MachineData) : Effects :=
  Directives.interp (AllowedipsImage.Lookup.rb9.take 6) s
    (AllowedipsImage.Lookup.entry + 0xb9) (fun p d => .done ⟨d, p⟩)

def selected (byte shift : Nat) : Nat := byte / 2^shift % 2

private theorem sar_mask (byte shift : Nat) (small : byte < 256) :
    ((BitVec.ofNat 32 byte).sshiftRight shift &&& 1) =
      BitVec.ofNat 32 (selected byte shift) := by
  have msb : (BitVec.ofNat 32 byte).msb = false := by
    simp [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : byte < 2^32)]
    omega
  rw [BitVec.sshiftRight_eq_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : byte < 2^32)]
  rw [Nat.shiftRight_eq_div_pow]
  change (byte / 2^shift) &&& 1 = (selected byte shift) % 2^32
  rw [show (1 : Nat) = 2^1-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp [selected, Nat.mod_eq_of_lt (by omega : byte / 2^shift % 2 < 2^32)]

private theorem ofInt_bmod (w : Nat) (v : Int) :
    BitVec.ofInt w (v.bmod (2^w)) = BitVec.ofInt w v := by
  rw [← BitVec.toInt_ofInt, BitVec.ofInt_toInt]

private theorem ofInt_bmod64 (v : Int) :
    BitVec.ofInt 64 (v.bmod 18446744073709551616) = BitVec.ofInt 64 v :=
  ofInt_bmod 64 v

private theorem uint_mask (v : BitVec 64) :
    (UInt64.ofBitVec v &&& 1) = UInt64.ofBitVec (v &&& 1) := rfl

private theorem extend_mask (v : BitVec 32) :
    (v.setWidth 64 &&& 1#64) = (v &&& 1#32).setWidth 64 := by
  rw [BitVec.setWidth_and]
  rfl

private theorem castmod64 (n : Nat) : BitVec.ofInt 64 ((n : Int) % 2) = BitVec.ofNat 64 (n % 2) := rfl

private theorem shift_mod (byte shift : Nat) (h : byte < 256) :
    ((BitVec.ofNat 32 byte).sshiftRight shift).toNat % 2 = selected byte shift := by
  have he := congrArg BitVec.toNat (sar_mask byte shift h)
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at he
  change ((BitVec.ofNat 32 byte).sshiftRight shift).toNat &&& 1 = selected byte shift % 2^32 at he
  rw [show (1 : Nat) = 2^1-1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at he
  simpa [selected, Nat.mod_eq_of_lt (by omega : byte / 2^shift % 2 < 2^32)] using he

private theorem extend8 (n : Nat) (h : n < 256) :
    (BitVec.ofInt 8 (n : Int)).setWidth 64 = BitVec.ofNat 64 n := by
  change (BitVec.ofNat 8 n).setWidth 64 = _
  exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) h

private theorem extract32 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem low32 (n : Nat) :
    (BitVec.ofNat 64 n).extractLsb' 0 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', Nat.mod_mod_of_dvd, show (2^32 : Nat) ∣ 2^64 by decide]

theorem execute (s : MachineData) (byteIndex shift byte : Nat) (next : BitVec 64)
    (indexBound : byteIndex < 16) (shiftBound : shift < 8) (byteBound : byte < 256)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some byteIndex)
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some shift)
    (byteRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 16 + .ofNat 64 byteIndex) 1 = some byte)
    (childRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 8 + .ofNat 64 (8 * selected byte shift)) 8 = some next.toNat) :
    (run s).All (fun t => t.pc = AllowedipsImage.Lookup.entry + 0xd0 ∧
      t.data.dmem = s.dmem ∧ t.data.zmms = s.zmms ∧ t.data.regs = {s.regs with
        rax := UInt64.ofNat (selected byte shift), rcx := UInt64.ofNat shift,
        rbx := UInt64.ofBitVec next}) := by
  simp at indexRead shiftRead byteRead childRead
  have ix := extend8 byteIndex (by omega)
  have sh := extend8 shift (by omega)
  have by8 := extend8 byte byteBound
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  change (BitVec.ofNat 8 shift).setWidth 64 = BitVec.ofNat 64 shift at sh
  change (BitVec.ofNat 8 byte).setWidth 64 = BitVec.ofNat 64 byte at by8
  have shiftMask : shift % 256 &&& 31 = shift := by
    rw [Nat.mod_eq_of_lt (by omega), show (31 : Nat) = 2^5-1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have byteAddr : s.regs.rsp.toBitVec + BitVec.ofNat 64 byteIndex + 16 =
      s.regs.rsp.toBitVec + 16 + BitVec.ofNat 64 byteIndex := by ac_rfl
  simp at byteAddr
  have shifted := sar_mask byte shift byteBound
  simp [run, AllowedipsImage.Lookup.rb9, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
     ConstExpr.interp,  AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    ix, sh, by8, extract32, low32, BitVec.ofInt_natCast, shiftMask,
    byteAddr,
    indexRead, shiftRead, byteRead,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp]
  have byteMod : (byte : Int) % 256 = byte := Int.emod_eq_of_lt (by omega) (by omega)
  have selBound : selected byte shift < 2^32 := by unfold selected; omega
  have selExt := BitVec.setWidth_ofNat_of_le_of_lt (by decide : 32 ≤ 64) selBound
  have childAddr : s.regs.rbx.toBitVec + BitVec.ofNat 64 (selected byte shift) * 8 + 8 =
      s.regs.rbx.toBitVec + 8 + BitVec.ofNat 64 (8 * selected byte shift) := by
    rw [BitVec.ofNat_mul]
    have comm : BitVec.ofNat 64 (selected byte shift) * 8 = 8 * BitVec.ofNat 64 (selected byte shift) := BitVec.mul_comm _ _
    rw [comm]
    ac_rfl
  simp at childAddr
  by_cases zero : shift = 0
  all_goals simp [zero] at childRead childAddr shifted selExt
  all_goals simp [-UInt64.ofBitVec_and, Effects.All,   ofInt_bmod64,
      uint_mask, extend_mask,
    shifted, selExt,    zero, ]
  all_goals simp only [castmod64, shift_mod byte shift byteBound,  ]
  · have eq0 : byte % 2 = selected byte 0 := by simp [selected]
    simp only [eq0, childAddr, childRead]
    simp [Effects.All, AllowedipsImage.Lookup.entry]
    exact ⟨rfl, by subst shift; rfl⟩
  · simp only [childAddr, childRead]
    split <;> simp [Effects.All, AllowedipsImage.Lookup.entry] <;> exact ⟨rfl, rfl⟩


/-- The endian-swapped stack query used by lookup: IPv4 is one host-order
word, IPv6 is its high host-order word followed by its low host-order word. -/
def QueryWords (memory : Mem 64) (base : BitVec 64) (bits query : Nat) : Prop :=
  if bits = 32 then memory.loadInt base 4 = some (query : Int)
  else memory.loadInt base 8 = some ((query / 2^64 : Nat) : Int) ∧
    memory.loadInt (base+8) 8 = some ((query % 2^64 : Nat) : Int)

def queryByte (bits query offset : Nat) : Nat :=
  if bits = 32 then query / 256^offset % 256
  else if offset < 8 then (query / 2^64) / 256^offset % 256
  else (query % 2^64) / 256^(offset-8) % 256

theorem queryByte_bound (bits query offset : Nat) : queryByte bits query offset < 256 := by
  unfold queryByte
  split
  · omega
  · split <;> omega

/-- The selected byte is derived from full-word stack reads, rather than
being supplied as another relation clause. -/
theorem queryByte_read (memory : Mem 64) (base : BitVec 64) (bits query offset : Nat)
    (family : bits = 32 ∨ bits = 128) (within : offset < bits/8)
    (words : QueryWords memory base bits query) :
    memory.loadInt (base + .ofNat 64 offset) 1 = some (queryByte bits query offset : Int) := by
  rcases family with rfl | rfl
  · simp only [QueryWords, ↓reduceIte] at words
    have h := MemoryBytes.loadInt_byte memory base 4 query words offset (by omega)
    simpa [queryByte, Int.natCast_pow] using h
  · simp only [QueryWords, ↓reduceIte, Nat.reduceEqDiff] at words
    by_cases high : offset < 8
    · have h := MemoryBytes.loadInt_byte memory base 8 (query / 2^64 : Nat) words.1 offset high
      simpa [queryByte, high, Int.natCast_pow] using h
    · have h := MemoryBytes.loadInt_byte memory (base+8) 8 (query % 2^64 : Nat) words.2
        (offset-8) (by omega)
      have address : base+8+BitVec.ofNat 64 (offset-8) = base+BitVec.ofNat 64 offset := by
        rw [show (8 : BitVec 64) = .ofNat 64 8 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      simp at address
      simpa [queryByte, high, address, Int.natCast_pow] using h

private theorem power256 (n : Nat) : 256^n = 2^(8*n) := by
  rw [show (256 : Nat) = 2^8 from rfl, Nat.pow_mul]

theorem queryByte_select (bits query cidr : Nat) (family : bits = 32 ∨ bits = 128)
    (short : cidr < bits) :
    selected (queryByte bits query (byteSelector bits cidr)) (7-cidr%8) =
      query / 2^(bits-1-cidr) % 2 := by
  have position := selector_position bits cidr family short
  have bitBound : 7-cidr%8 < 8 := by omega
  have observed : (queryByte bits query (byteSelector bits cidr)).testBit (7-cidr%8) =
      query.testBit (bits-1-cidr) := by
    rcases family with rfl | rfl
    · simpa only [queryByte, ↓reduceIte, power256, byteShift] using selected_bit 32 cidr query (.inl rfl) short
    · simp only [queryByte, Nat.reduceEqDiff, ↓reduceIte]
      split
      · simp only [power256]
        simp only [show (256 : Nat) = 2^8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
          bitBound, decide_true, Bool.true_and]
        simp only [byteShift, Nat.reduceEqDiff, ↓reduceIte] at position
        split at position <;> try omega
        congr 1 <;> omega
      · simp only [power256]
        simp only [show (256 : Nat) = 2^8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
          bitBound, decide_true, Bool.true_and]
        simp only [byteShift, Nat.reduceEqDiff, ↓reduceIte] at position
        split at position <;> try omega
        have low : 7-cidr%8 + 8*(byteSelector 128 cidr-8) < 64 := by omega
        simp only [low, decide_true, Bool.true_and]
        congr 1 <;> omega
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] at observed
  unfold selected
  omega

/-- Actual six-instruction child step from the trie relation. The only
extra physical query facts are full stack words, which are established by
lookup's endian-swap regions. Selector bytes, the selected query byte and
the chosen child pointer all follow from those words and NodeFields. -/
theorem node_step (s : MachineData) (nodes peers : Nat → BitVec 64)
    (bits query id : Nat) (node : Leanux.WG.AipNode) (next : Option Nat)
    (family : bits = 32 ∨ bits = 128)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : NodeFields s.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query) (short : node.cidr < bits)
    (atChild : node.bit[childIndex node query]? = some next)
    (words : QueryWords s.dmem (s.regs.rsp.toBitVec+16) bits query) :
    (run s).All (fun t => t.pc = AllowedipsImage.Lookup.entry + 0xd0 ∧
      t.data.dmem = s.dmem ∧ t.data.zmms = s.zmms ∧ t.data.regs = {s.regs with
        rax := UInt64.ofNat (childIndex node query),
        rcx := UInt64.ofNat (7-node.cidr%8),
        rbx := UInt64.ofBitVec (pointer nodes next)}) := by
  obtain ⟨_, _, _, _, matched⟩ := fields
  obtain ⟨_, _, children⟩ := matched matching
  obtain ⟨width, _, indexRead, shiftRead, links⟩ := children short
  have position := selector_position bits node.cidr family short
  have bound : byteSelector bits node.cidr < 16 := by
    rcases family with h | h <;> omega
  have byteRead := queryByte_read s.dmem (s.regs.rsp.toBitVec+16) bits query
    (byteSelector bits node.cidr) family position.2 words
  have select : selected (queryByte bits query (byteSelector bits node.cidr)) (7-node.cidr%8) =
      childIndex node query := by
    rw [queryByte_select bits query node.cidr family short]
    simp only [childIndex, width]
  have childRead := (links next atChild).1
  have result := execute s (byteSelector bits node.cidr) (7-node.cidr%8)
    (queryByte bits query (byteSelector bits node.cidr)) (pointer nodes next)
    bound (by omega) (queryByte_bound _ _ _) ?_ ?_ byteRead ?_
  · simpa only [select] using result
  · simpa [atNode, byteSelector, AllowedipsLayout.bit_at_a] using indexRead
  · simpa [atNode, AllowedipsLayout.bit_at_b] using shiftRead
  · simpa [atNode, select, AllowedipsLayout.bit, BitVec.ofNat_add, BitVec.add_assoc] using childRead

#print axioms execute
#print axioms queryByte_read
#print axioms queryByte_select
#print axioms node_step

end Binary.AllowedipsChild
