import C1BelowWholeEntry

/-! Result C1, work package 3, the split path: the state at `add+0x338`
(internal node initialized, the bit for the node below chosen), reached from
the state after the second allocation by `C1Internal.internal_chosen`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- The state at `add+0x338`. -/
structure AtConnect (c : Context) (e t u : MachineState) (base base2 child width least key sel : Nat) : Prop where
  pc : u.pc = Add.entry + 0x338
  rsp : u.data.regs.rsp = e.data.regs.rsp
  rbx : u.data.regs.rbx = e.data.regs.rbx
  r12 : u.data.regs.r12 = .ofNat base2
  r8 : u.data.regs.r8 = .ofNat base
  rdi : u.data.regs.rdi = .ofNat child
  rax : u.data.regs.rax = .ofNat sel
  rdx : u.data.regs.rdx = .ofNat sel
  rcx : u.data.regs.rcx = .ofNat (sel+1)
  ready : CallsReady c u.data
  frame : EqualOutside (C1Internal.Writes c t.data.regs.rsp base2) t.data.dmem u.data.dmem
  record : ∀ names : Allowedips.Names, Trie.decodeNode names.trie nodeOffsets u.data.dmem base2 =
    .ok (Trie.targetNode (newNode key least width none))
  next : word u.data.dmem "node.list.next" (base2+56) 8 = .ok (base2+56)
  prev : word u.data.dmem "node.list.prev" (base2+64) 8 = .ok (base2+56)
  mapped : MappedLe t.data.dmem u.data.dmem
  flag : u.data.system.bits[10] = t.data.system.bits[10]

/-- The bit `choose(node, down->bits)` selects. -/
def SplitCtx.chosen (family key cidr : Nat) (downNode : AipNode) : Nat :=
  selected (queryByte (widthOf family) downNode.bits
    (byteSelector (widthOf family) (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key))))
    (7 - min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key) % 8)

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
    downNode rest base2)
include x

theorem connect (premises : Premises fetch L A) :
    Eventually (instructionStep fetch) (fun u => AtConnect c e t u base base2 child (widthOf family)
      (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key
      (chosen family key cidr downNode)) t := by
  have position := x.frame
  have childBound := x.liveBound (nodeLive (base := base) x.named)
  have stackN : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [x.stackT]
  have indexBound : byteSelector (widthOf family)
      (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) < 16 := by
    have within := (selector_position _ _ x.wide x.proper).2
    have small : widthOf family / 8 ≤ 16 := by rcases x.wide with h|h <;> rw [h] <;> decide
    omega
  have downRead : word t.data.dmem "saved.down" t.data.regs.rsp.toNat 8 = .ok child := by
    have read := x.localWord 0 8 child (by decide) "saved.down" (by simpa using x.cmp.held.down)
    simpa using read
  have byteRead : word t.data.dmem "down.key" (child+32+NodeInit.selector (widthOf family)
      (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key))) 1 =
      .ok (queryByte (widthOf family) downNode.bits (byteSelector (widthOf family)
        (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)))) := by
    apply Trie.word_of_loadInt _ (by change child+32+byteSelector _ _+1 ≤ 2^64; omega)
    rw [BitVec.ofNat_add]
    exact x.downByte
  have run := eventually_flight (C1Internal.internal_chosen fetch premises.insertion premises.tracePc c
    x.entry x.proper childBound downRead byteRead (by
      intro y down written
      have heap : L.Heap y := arena_heap (offset := 32) (x.cut.arena _ x.named) (by decide) down
      have far := x.heapFar heap
      have bounds := range_nat (by omega) down
      rcases written with node|saved|push|buffer
      · exact objects_apart (Nat.le_of_lt x.top2) (by omega : child+32+16 ≤ 2^64)
          (by have := x.freshApart (nodeLive (base := base) x.named); omega) node down
      · have near := range_nat (by omega) saved
        exact far.1 (by omega)
      · obtain ⟨i,small,location⟩ := push
        have rsp : t.data.regs.rsp.toBitVec.toNat = t.data.regs.rsp.toNat := rfl
        have value : y.toNat = t.data.regs.rsp.toNat - 8 + i := by rw [location]; bv_omega
        exact far.1 (by omega)
      · exact far.2.2 buffer))
  apply Rollback.start_at x.grown.pc
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro u ⟨⟨pc,v,exit,mem,regs⟩,mapped,flag⟩
  exact {
    pc := pc
    rsp := by rw [regs]; exact exit.stack.trans x.stackT
    rbx := by rw [regs]; exact exit.parent.trans (x.grown.rbx.trans x.cmp.held.bx)
    r12 := by rw [regs]; exact exit.node
    r8 := by rw [regs]; exact exit.first
    rdi := by rw [regs]
    rax := by rw [regs]; rfl
    rdx := by rw [regs]; rfl
    rcx := by rw [regs]; rfl
    ready := exit.ready.congr mem (by rw [regs])
    frame := mem ▸ exit.frame
    record := fun names => mem ▸ exit.record names
    next := mem ▸ exit.next
    prev := mem ▸ exit.prev
    mapped := mapped
    flag := flag }

end SplitCtx

#print axioms SplitCtx.connect
end Binary.Statements.C1.Proof
