import C1BelowWholeWorld
import C1BelowSplitSelect

/-! Result C1, work package 3, the split path: from the state after the
second allocation through the internal node's initialization and the choice
against the node below, to `add+0x338`. The hypotheses of
`C1Internal.internal_chosen` are discharged from the bundle. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
include x

/-- `min(cidr, common)` for this run: the common prefix, since it is the shorter. -/
theorem least : min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key) =
    AllowedipsRelation.common (widthOf family) downNode.bits key := Nat.min_eq_right (Nat.le_of_lt x.shorter)

theorem proper : min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key) < widthOf family := by
  have := x.shorter
  have := x.fits
  omega

/-- The node below, decoded in the memory after the second allocation. -/
theorem downDecoded : Trie.decodeNode (names.allocated base).trie nodeOffsets t.data.dmem child =
    .ok (Trie.targetNode downNode) :=
  x.pendingT.old_node x.cut.related.1 x.named x.hasDown

/-- The key byte of the node below that `choose(node, down->bits)` reads. -/
theorem downByte : t.data.dmem.loadInt (.ofNat 64 (child+32) +
      .ofNat 64 (byteSelector (widthOf family) (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)))) 1 =
    some (queryByte (widthOf family) downNode.bits
      (byteSelector (widthOf family) (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key))) : Int) := by
  have words := key_words x.downDecoded
  have width : (Trie.targetNode downNode).width = widthOf family := x.downWidth
  rw [width] at words
  exact queryByte_read _ _ _ _ _ x.wide (selector_position _ _ x.wide x.proper).2 words

theorem entry : C1Internal.Entry c t.data base base2 (widthOf family) cidr
    (AllowedipsRelation.common (widthOf family) downNode.bits key) key := by
  have position := x.frame
  have res := x.res
  have fields := x.fields
  have held := x.cmp.held
  have width := x.extra.width
  have cidrSmall : cidr < 256 := by
    have := x.fits
    rcases x.wide with h|h <;> omega
  have baseBound := x.liveBound baseLive
  have stackT := x.stackT
  have stackN : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [x.stackT]
  have rspE : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
  have nearOf {y : BitVec 64} {p n : Nat} (fits : p + n ≤ 2^64) (inside : InRange (.ofNat 64 p) n y)
      (low : e.data.regs.rsp.toNat ≤ p + 48) (high : p + n ≤ e.data.regs.rsp.toNat + 48) :
      e.data.regs.rsp.toNat ≤ y.toNat + 48 ∧ y.toNat < e.data.regs.rsp.toNat + 48 := by
    have := range_nat fits inside
    omega
  exact {
    family := x.wide
    cidrBound := x.fits
    commonBound := AllowedipsLoop.common_bound _ _ _ x.wide
    object := by rw [←x.grown.object]; exact (UInt64.ofNat_toNat ..).symm
    nonzero := x.grown.nonzero
    extent := Nat.le_of_lt x.top2
    zero := x.grown.zero
    stackLow := by rw [stackT]; omega
    stackHigh := by rw [stackT]; omega
    firstRead := x.localWord 24 8 base (by decide) _ (by
      have read := x.ac.baseWord
      rw [x.stackA,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at read
      exact read)
    firstExtent := baseBound
    cidrRead := x.localWord 16 1 cidr (by decide) _ (by
      have read := x.ac.cidrByte
      rw [x.stackA,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at read
      exact read)
    maskRead := x.localWord 36 1 _ (by decide) _ (by
      have kept := held.selector_byte res 36 (by decide) (by decide)
      rw [x.stackA] at kept
      rw [kept,←width]
      exact (init_bytes fields res x.summary).1)
    commonLow := by
      have reg : a.data.regs.get (.low .r13 .W8) = BitVec.extractLsb' 0 8 a.data.regs.r13.toBitVec := by
        simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take]
      have low := x.cmp.common
      rw [reg,←x.grown.r13] at low
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have small := AllowedipsLoop.common_bound (widthOf family) downNode.bits key x.wide
      rw [Nat.mod_eq_of_lt (by rcases x.wide with h|h <;> omega)]
      exact low
    bits := by
      rw [x.grown.r15,held.r15,←width,←fields.bits]
      exact (UInt64.ofNat_toNat ..).symm
    bytes := by rw [x.grown.rbp,held.bp,width]
    source := by rw [x.grown.r14,held.r14]
    firstKey := by
      have words := (Trie.decodeNode_fields x.pendingT.core).key
      have shape : (Trie.targetNode (newNode key cidr e.data.regs.rbp.toNat (some pid))).width =
          widthOf family := width
      rw [shape] at words
      exact words
    ready := x.grown.calls
    nodeStack := by
      intro y node stack
      exact (x.heapFar (nodeHeap x.grown.arena node)).1 (nearOf (by omega) stack (by omega) (by omega))
    nodeContext := fun y read node => (x.heapFar (nodeHeap x.grown.arena node)).2.1 read
    nodeCoverage := fun y written node => (x.heapFar (nodeHeap x.grown.arena node)).2.2 written
    nodeFirst := fun y node => objects_apart (Nat.le_of_lt x.top2) baseBound (x.freshApart baseLive) node
    stackContext := by
      intro y read stack
      exact x.contextFar read (nearOf (by omega) stack (by omega) (by omega))
    stackCoverage := by
      intro y written stack
      exact x.contextFar (writes_bytes written) (nearOf (by omega) stack (by omega) (by omega))
    firstStack := by
      intro y first stack
      exact (x.heapFar (arena_heap (offset := 32) x.cut.fresh (by decide) first)).1
        (nearOf (by omega) stack (by omega) (by omega))
    firstCoverage := fun y written first =>
      (x.heapFar (arena_heap (offset := 32) x.cut.fresh (by decide) first)).2.2 written }

end SplitCtx

#print axioms SplitCtx.entry
end Binary.Statements.C1.Proof
