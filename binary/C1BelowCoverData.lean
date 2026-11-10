import C1BelowCoverPath
import C1BelowCoverHeap
import PairAllowedipsHeapFrame
import PairAllowedipsFrame
import AllowedipsNodePendingFrame

/-! Result C1, work package 3, covering path below a parent: the machine's
final memory carries the reconstruction and the structural check of the data
side (the port of trial T2), which are stated on the four connection stores
applied to the memory after the first coverage call. -/
namespace Binary.Pair.Allowedips.C1Cover
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

theorem slot_ofNat (p b : Nat) : slot (.ofNat 64 p) b=.ofNat 64 (p+8+b*8) := by
  unfold slot
  rw [←BitVec.ofNat_add]
  congr 1
  omega

theorem packed_ofNat (p b : Nat) : packed (.ofNat 64 p) b=.ofNat 64 ((p+8+b*8) ||| b) := by
  unfold packed
  rw [slot_ofNat,←BitVec.ofNat_or]

theorem field_ofNat (p : Nat) : (BitVec.ofNat 64 p)+48=.ofNat 64 (p+48) := by
  rw [BitVec.ofNat_add]
  rfl

theorem link1_connect (m : DataMem) (down base b : Nat) :
    link1 m (.ofNat 64 down) (.ofNat 64 base) b=
      connectMemory m down (base+8+b*8) ((base+8+b*8) ||| b) := by
  simp only [link1,connectMemory,write64,slot_ofNat,packed_ofNat,field_ofNat]

/-- The machine's ideal memory below a parent is the data side's. -/
theorem coverParent_connect (m : DataMem) (down base parent b b2 : Nat) :
    coverParent m (.ofNat 64 down) (.ofNat 64 base) (.ofNat 64 parent) b b2=
      connectMemory (connectMemory m down (base+8+b*8) ((base+8+b*8) ||| b))
        base (parent+8+b2*8) ((parent+8+b2*8) ||| b2) := by
  simp only [coverParent,link1_connect]
  simp only [connectMemory,write64,slot_ofNat,packed_ofNat,field_ofNat]

#print axioms coverParent_connect

/-- Below a parent: at the common exit the memory corresponds, under the
names extended by the fresh node, to the mirror device after the two
connections, and passes the structural check. The ordering hypotheses are
those of the data side; `C1BelowCoverFacts` derives them from the plan's
`ordered` and `walk`. -/
theorem parent_data {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase parentId parentBase b direction : Nat} {d : Device}
    {parentNode downNode : AipNode} (owner : Peer) {c : Context} {s : MachineData}
    {other : BitVec 64 → Prop} {mid : DataMem} {t : MachineState}
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base s.dmem)
    (done : Done c s (.ofNat 64 downBase) (.ofNat 64 base) other mid
      (coverParent mid (.ofNat 64 downBase) (.ofNat 64 base) (.ofNat 64 parentBase) b direction) t)
    (readApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets, ∀ a, span.contains a →
      ¬(InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a))
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a →
      ¬(InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a))
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner)
    (bit : direction<2) (downBit : b<2)
    (occupied : parentNode.bit[direction]?=some (some downId))
    (sameWidth : machine.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (downMeasure : cidr<downNode.cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-cidr)=key/2^(machine.data.regs.rbp.toNat-cidr))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-cidr)%2=b) :
    Corresponds (names.allocated base) nodeOffsets t.data.dmem
      (coverInstalled d downId b parentId direction key cidr machine.data.regs.rbp.toNat pid
        downNode parentNode owner) ∧
    heap (names.allocated base)
      (target (coverInstalled d downId b parentId direction key cidr machine.data.regs.rbp.toNat pid
        downNode parentNode owner)) t.data.dmem=.ok () := by
  have different : downId≠parentId := by
    rintro rfl
    have same : downNode=parentNode := Option.some.inj (hasDown.symm.trans hasParent)
    rw [same] at downMeasure
    omega
  have pendingMid : NodeInit.Pending names machine.data d key cidr pid base mid :=
    pending.frame done.midFrame
      (fun span member a inside h => readApart span member a inside
        (h.elim (fun h => .inl (off_in _ 48 16 8 (by omega) a h)) .inr))
      (fun a inside h => tableApart a inside
        (h.elim (fun h => .inl (off_in _ 48 16 8 (by omega) a h)) .inr))
  have ideal := done.ideal
  rw [coverParent_connect] at ideal
  have final : ∀ a, (InRange s.regs.rsp.toBitVec 8 a ∨ CallWrites s.regs.rsp c a) →
      (InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a) :=
    fun a h => h.elim (fun h => .inl (zero_in _ 48 8 (by omega) a h)) .inr
  have corresponds := cover_connect_corresponds fields related pendingMid downNamed parentNamed downBit bit
    hasDown hasParent hasPeer different
  have shape := cover_connect_heap owner fields related checked pendingMid downNamed parentNamed hasPeer
    (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
    (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown) bit downBit occupied sameWidth measure
    prefixEq side downMeasure downPrefix downSide
  rw [←target_coverInstalled d downId b parentId direction key cidr machine.data.regs.rbp.toNat pid
    downNode parentNode owner hasDown hasParent hasPeer different (target_nodes_below related)] at shape
  constructor
  · unfold Corresponds at corresponds ⊢
    rw [←reconstruct_frame (names.allocated base) nodeOffsets ideal
      (fun span member a inside h => readApart span member a inside (final a h))]
    exact corresponds
  · rw [←heap_frame (names.allocated base) nodeOffsets _ ideal
      (fun span member a inside h => readApart span (Placement.metadata_read member) a inside (final a h))]
    exact shape

#print axioms parent_data
end Binary.Pair.Allowedips.C1Cover
