import C1BelowCoverData
import C1BelowCoverRootSource

/-! Result C1, work package 3, covering path at the root: the machine's
final memory carries the reconstruction and the structural check. -/
namespace Binary.Pair.Allowedips.C1Cover
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

/-- The machine's ideal memory at the root is the data side's. -/
theorem coverRoot_connect (m : DataMem) (down base slot b : Nat) :
    coverRoot m (.ofNat 64 down) (.ofNat 64 base) (.ofNat 64 slot) b=
      connectMemory (connectMemory m down (base+8+b*8) ((base+8+b*8) ||| b)) base slot (slot ||| 2) := by
  simp only [coverRoot,link1_connect]
  have tagged : (BitVec.ofNat 64 slot ||| 2#64)=BitVec.ofNat 64 (slot ||| 2) := by
    rw [BitVec.ofNat_or]
  simp only [connectMemory,write64,field_ofNat,tagged]

/-- The root publication leaves every old internal node's list head intact. -/
theorem pending_internal_root {names : Names} {before : MachineData} {d : Device}
    {key cidr pid base downId downBase b packed packedRoot : Nat} {memory : DataMem} (v4 : Bool)
    (pending : NodeInit.Pending names before d key cidr pid base memory)
    (valid : validate (names.allocated base) nodeOffsets=.ok ())
    (g : Geometry (names.allocated base) nodeOffsets)
    (downNamed : (downId,downBase) ∈ names.trie.nodes) (downBit : b<2) :
    ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
      internalListCheck (names.allocated base)
        (connectMemory (connectMemory memory downBase (base+8+b*8) packed)
          base (names.table+C1Split.rootOffset v4) packedRoot) current=.ok () := by
  intro current node member internal
  have arena : C1Split.Arena (names.allocated base) := C1Split.arena_of_valid valid
  have named := allocated_node names base
  have first := connect_frame memory downBase (base+8+b*8) packed
  have firstApart := connect_lists_apart g (List.mem_append_left _ downNamed) named downBit
  have second := connect_frame (connectMemory memory downBase (base+8+b*8) packed)
    base (names.table+C1Split.rootOffset v4) packedRoot
  have secondApart : ∀ a, ListWrites (names.allocated base) a →
      ¬ConnectWrites base (names.table+C1Split.rootOffset v4) a := by
    intro a list written
    rcases written with fresh|slot
    · exact node_before_list_apart g rfl named (offset:=48) (size:=8) (by decide) a fresh list
    · obtain ⟨span,inSpans,inSpan⟩ := C1Split.listWrites_allocation list
      exact C1Split.span_root_apart arena inSpans v4 a inSpan slot
  exact (internal_list_frame (names.allocated base) second secondApart current) ▸
    (internal_list_frame (names.allocated base) first firstApart current) ▸
    pending.internal current node member internal

/-- At the root: at the common exit the memory corresponds, under the names
extended by the fresh node, to the mirror device with the fresh node as the
family's root above `down`, and passes the structural check. -/
theorem root_data {names : Names} {world : World} {machine : MachineState}
    {key cidr pid base downId downBase b : Nat} {d : Device} {downNode : AipNode} (owner : Peer)
    (v4 : Bool) {c : Context} {s : MachineData} {other : BitVec 64 → Prop} {mid : DataMem} {t : MachineState}
    (fields : NodeInit.BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base s.dmem)
    (done : Done c s (.ofNat 64 downBase) (.ofNat 64 base) other mid
      (coverRoot mid (.ofNat 64 downBase) (.ofNat 64 base)
        (.ofNat 64 (names.table+C1Split.rootOffset v4)) b) t)
    (readApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets, ∀ a, span.contains a →
      ¬(InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a))
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a →
      ¬(InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a))
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner)
    (downBit : b<2)
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : machine.data.regs.rbp.toNat=if v4 then 32 else 128)
    (downWidth : downNode.bitlen=machine.data.regs.rbp.toNat)
    (downMeasure : cidr<downNode.cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-cidr)=key/2^(machine.data.regs.rbp.toNat-cidr))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-cidr)%2=b) :
    Corresponds (names.allocated base) nodeOffsets t.data.dmem
      (coverRootInstalled d v4 downId b key cidr machine.data.regs.rbp.toNat pid downNode owner) ∧
    heap (names.allocated base)
      (target (coverRootInstalled d v4 downId b key cidr machine.data.regs.rbp.toNat pid downNode owner))
      t.data.dmem=.ok () := by
  have pendingMid : NodeInit.Pending names machine.data d key cidr pid base mid :=
    pending.frame done.midFrame
      (fun span member a inside h => readApart span member a inside
        (h.elim (fun h => .inl (off_in _ 48 16 8 (by omega) a h)) .inr))
      (fun a inside h => tableApart a inside
        (h.elim (fun h => .inl (off_in _ 48 16 8 (by omega) a h)) .inr))
  have ideal := done.ideal
  rw [coverRoot_connect] at ideal
  have final : ∀ a, (InRange s.regs.rsp.toBitVec 8 a ∨ CallWrites s.regs.rsp c a) →
      (InRange s.regs.rsp.toBitVec 48 a ∨ CallWrites s.regs.rsp c a) :=
    fun a h => h.elim (fun h => .inl (zero_in _ 48 8 (by omega) a h)) .inr
  have targetEq := target_coverRootInstalled d v4 downId b key cidr machine.data.regs.rbp.toNat pid
    downNode owner hasDown hasPeer (target_nodes_below related)
  have corresponds := reconstruct_cover_root v4 fields related pendingMid downNamed downBit
  have shape := heap_installedCoverRoot (newNames:=names.allocated base)
    (after:=connectMemory (connectMemory mid downBase (base+8+b*8) ((base+8+b*8) ||| b)) base
      (names.table+C1Split.rootOffset v4) ((names.table+C1Split.rootOffset v4) ||| 2))
    v4 owner related checked hasPeer
    (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown) downBit rootHere otherRoot family downWidth
    downMeasure downPrefix downSide
    (pending_internal_root v4 pendingMid fields.allocated (fields.geometry related) downNamed downBit)
  rw [←targetEq] at shape corresponds
  constructor
  · unfold Corresponds
    rw [←reconstruct_frame (names.allocated base) nodeOffsets ideal
      (fun span member a inside h => readApart span member a inside (final a h))]
    exact corresponds
  · rw [←heap_frame (names.allocated base) nodeOffsets _ ideal
      (fun span member a inside h => readApart span (Placement.metadata_read member) a inside (final a h))]
    exact shape

#print axioms root_data
end Binary.Pair.Allowedips.C1Cover
