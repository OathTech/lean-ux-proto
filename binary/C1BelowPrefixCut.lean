import C1BelowExit
import AllowedipsChildChecked
import AllowedipsPlacementCommon

/-! Result C1, work package 3, prefix: what the prefix needs at the cut.

`CutExtra` is the list of facts about the cut state that `NodeCut` does not
give and the instructions from `add+0x156` to `add+0x267` consume. `Zone` is
the part of the stack those instructions touch: the six words below the
cut's stack pointer (callback return words, `common_bits`' frame) and
`add`'s 48 bytes of locals. `Res` is the form in which the machine lemmas
take the separations. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- WHAT `NodeCut` DOES NOT GIVE and the instructions from `add+0x156` to
`add+0x267` consume. None of these follows from `NodeCut`'s fields: its
`boundary` reads the stack only at `rsp+0` (8 bytes), `rsp+16` (4 bytes) and
the bytes `rsp+36/43/44`, relates `rbp` to nothing but `{32,128}`, and
separates the key bytes only from the first initialization's writes; its
`flight` bounds the stack pointer by `s.rsp - insertWindow ≤ e.rsp ≤ s.rsp`. -/
structure CutExtra (L : Layout) (s e : MachineState) (family : Nat) : Prop where
  /-- G1 (upper). `add`'s 48 bytes of locals lie below the caller's return
  word: needed for them to be mapped, to be scratch (`InsertWrites`) and to be
  apart from the heap and the coverage state. Consumed first by
  `mov %r8,0x18(%rsp)` at `add+0x1ff`. -/
  frameHigh : e.data.regs.rsp.toNat+48≤s.data.regs.rsp.toNat
  /-- G1 (lower). 48 bytes below the cut's stack pointer are still inside
  `insertWindow`: the callbacks' return words (`call` at `add+0x20d`, `+0x246`,
  `+0x262`) and `common_bits`' frame (`call` at `add+0x255`). `InFlight.low`
  allows `e.rsp = s.rsp - insertWindow`, which leaves no room when `A.depth = 0`. -/
  frameLow : s.data.regs.rsp.toNat+48≤e.data.regs.rsp.toNat+insertWindow
  /-- G4. `ebp` at the cut is the family's width (`boundary` only says 32 or
  128): the mirror's facts (`walk`, `ordered`) speak of `widthOf family`, the
  machine of `ebp`/`r15d`. Consumed by the selector (`add+0x212`) and by
  `common_bits`' third argument (`mov %r15d,%edx` at `add+0x252`). -/
  width : e.data.regs.rbp.toNat=widthOf family
  /-- G3. The key bytes at `r13` (host order, written by the wrapper into its
  own frame) lie inside the window above `add`'s locals: needed for their
  separation from the locals, the callbacks' return words, `common_bits`'
  frame and the coverage buffer. Consumed by `movzbl (%r13,%rax,1)` at
  `add+0x21f` and by `common_bits` (`mov %r13,%rsi` at `add+0x24f`). -/
  keyLow : e.data.regs.rsp.toNat+48≤e.data.regs.r13.toNat
  keyHigh : e.data.regs.r13.toNat+e.data.regs.rbp.toNat/8≤s.data.regs.rsp.toNat
  /-- G2 (root sub-case only). The stack word at `rsp+8` is the address of
  the family's root slot. Consumed by `mov 0x8(%rsp),%rax; mov (%rax),%rax`
  at `add+0x606` (and later by the root publications at `add+0x6c5`, `+0x722`). -/
  slot : e.data.dmem.loadInt (e.data.regs.rsp.toBitVec+8) 8=
    some ((L.table+(if family = 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) : Nat) : Int)

/-- The stack bytes the prefix reads or writes: `[rsp-48, rsp+48)`. -/
def Zone (stack : UInt64) (a : BitVec 64) : Prop := InRange (stack.toBitVec-48) 96 a

theorem zone_locals {stack : UInt64} {n : Nat} {a : BitVec 64} (within : n≤48)
    (inside : InRange stack.toBitVec n a) : Zone stack a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨48+i,by omega,?_⟩
  rw [equal]
  bv_omega

theorem zone_local {stack : UInt64} {offset n : Nat} {a : BitVec 64} (within : offset+n≤48)
    (inside : InRange (stack.toBitVec+.ofNat 64 offset) n a) : Zone stack a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨48+offset+i,by omega,?_⟩
  rw [equal]
  bv_omega

theorem zone_word {stack : UInt64} {a : BitVec 64}
    (inside : InRange (stack.toBitVec-8) 8 a) : Zone stack a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨40+i,by omega,?_⟩
  rw [equal]
  bv_omega

theorem zone_scratch {stack : UInt64} {n : Nat} {a : BitVec 64} (within : n≤96)
    (inside : InRange (stack.toBitVec-48) n a) : Zone stack a := by
  obtain ⟨i,bound,equal⟩ := inside
  exact ⟨i,by omega,equal⟩

/-- The separations and mapped stack the machine lemmas of the prefix take,
as facts about the cut state `e` alone. `resources` (in `C1BelowPrefixRes`)
derives them from `NodeCut`, `CutExtra` and the caller's conditions. -/
structure Res (names : Allowedips.Names) (c : Context) (e : MachineData) (base : Nat) : Prop where
  /-- The zone is mapped. -/
  mapped : (e.dmem.loadInt (e.regs.rsp.toBitVec-48) 96).isSome=true
  /-- No wrap above the locals. -/
  extent : e.regs.rsp.toNat+48≤2^64
  /-- The coverage state is outside the zone. -/
  context : ∀ a, c.bytes a → ¬Zone e.regs.rsp a
  /-- The coverage state is outside the first initialization's writes. -/
  contextInit : ∀ a, c.bytes a → ¬NodeInit.EntryWrites names e base a
  /-- The heap bytes the first initialization writes (the fresh node, the
  list words of the owner and its neighbours) are outside the zone. -/
  heapZone : ∀ a, (InRange (.ofNat 64 base) 72 a ∨ ListWrites (names.allocated base) a) →
    ¬Zone e.regs.rsp a
  /-- Everything reconstruction reads is outside the zone and the coverage buffer. -/
  projection : ∀ span ∈ readSpans (names.allocated base) Root.nodeOffsets,
    ∀ a, span.contains a → ¬(Zone e.regs.rsp a ∨ c.writes a)
  table : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬(Zone e.regs.rsp a ∨ c.writes a)
  /-- The key bytes are outside the zone and the coverage buffer. -/
  query : ∀ a, InRange e.regs.r13.toBitVec (e.regs.rbp.toNat/8) a → ¬(Zone e.regs.rsp a ∨ c.writes a)

theorem Res.local_mapped {names c e base} (res : Res names c e base) (offset size : Nat)
    (within : offset+size≤48) :
    (e.dmem.loadInt (e.regs.rsp.toBitVec+.ofNat 64 offset) size).isSome=true := by
  obtain ⟨value,read⟩ := Option.isSome_iff_exists.mp res.mapped
  have part := MemoryBytes.loadInt_subword _ _ _ _ read (48+offset) size (by omega)
  have address : e.regs.rsp.toBitVec-48+.ofNat 64 (48+offset)=e.regs.rsp.toBitVec+.ofNat 64 offset := by
    bv_omega
  rw [address] at part
  exact Option.isSome_of_eq_some part

theorem Res.local_mapped_nat {names c e base} (res : Res names c e base) (offset size : Nat)
    (within : offset+size≤48) :
    (e.dmem.loadInt (.ofNat 64 (e.regs.rsp.toNat+offset)) size).isSome=true := by
  have mapped := res.local_mapped offset size within
  rwa [BitVec.ofNat_add,Root.ofNat_uint64]

theorem Res.below_mapped {names c e base} (res : Res names c e base) (n : Nat) (bound : n<6) :
    (e.dmem.loadInt (e.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true := by
  obtain ⟨value,read⟩ := Option.isSome_iff_exists.mp res.mapped
  have part := MemoryBytes.loadInt_subword _ _ _ _ read (48-(n+1)*8) 8 (by omega)
  have address : e.regs.rsp.toBitVec-48+.ofNat 64 (48-(n+1)*8)=e.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8) := by
    bv_omega
  rw [address] at part
  exact Option.isSome_of_eq_some part

/-- Inside the zone the first initialization writes only its three selector bytes. -/
theorem Res.init_zone {names c e base} (res : Res names c e base) {a : BitVec 64}
    (zone : Zone e.regs.rsp a) (written : NodeInit.EntryWrites names e base a) :
    ∃ offset ∈ [36,43,44], a=e.regs.rsp.toBitVec+.ofNat 64 offset := by
  rcases written with fresh|list|⟨offset,member,i,bound,location⟩
  · exact absurd zone (res.heapZone a (.inl fresh))
  · exact absurd zone (res.heapZone a (.inr list))
  · refine ⟨offset,member,?_⟩
    have zero : i=0 := by omega
    subst zero
    rw [location,BitVec.ofNat_add,Root.ofNat_uint64]
    simp

/-- A stack local the first initialization does not write keeps its value. -/
theorem Res.init_local {names c e base} (res : Res names c e base) {memory : DataMem}
    (frame : EqualOutside (NodeInit.EntryWrites names e base) e.dmem memory)
    (offset size : Nat) (within : offset+size≤48)
    (clear : ∀ k ∈ [36,43,44], k<offset ∨ offset+size≤k) :
    memory.loadInt (e.regs.rsp.toBitVec+.ofNat 64 offset) size=
      e.dmem.loadInt (e.regs.rsp.toBitVec+.ofNat 64 offset) size := by
  symm
  apply frame.loadInt
  intro i bound written
  obtain ⟨k,member,location⟩ := res.init_zone (zone_local within ⟨i,bound,rfl⟩) written
  have apart := clear k member
  have small : k<48 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  bv_omega

end Binary.Statements.C1.Proof
