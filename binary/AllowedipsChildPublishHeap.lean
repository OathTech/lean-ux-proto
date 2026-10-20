import AllowedipsChildHeap
import AllowedipsChildPublishRecord

namespace Binary.Pair.Allowedips.ChildPublish
open Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

/-- The executed publication segment restores both the full reconstruction and
the tested heap invariant. The pending resource is derived by initialization;
selection must still supply the saved slot and its prefix/branch facts. -/
theorem publication_restores (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names : Names} {world : World} {entry : MachineState} {s : MachineData}
    {key cidr pid base parentId direction : Nat} {memory : DataMem} {registers : Reg64s}
    {d : Device} {parentNode : AipNode} {owner : Peer}
    (fields : NodeInit.BoundaryFields names nodeOffsets world entry key cidr pid base)
    (related : Corresponds names nodeOffsets entry.data.dmem d)
    (heapOk : heap names (target d) entry.data.dmem=.ok ())
    (pending : NodeInit.Pending names entry.data d key cidr pid base s.dmem)
    (parentNamed : (parentId,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (bit : direction<2) (empty : parentNode.bit[direction]?=some none)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (baseRead : readNat ⟨s,0⟩ s.regs.rsp.toNat 8=.ok base)
    (directionRead : readNat ⟨s,0⟩ (s.regs.rsp.toNat+8) 1=.ok direction)
    (indexRead : word s.dmem "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a)
    (checked : effect s=.ok (memory,registers)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=AllowedipsMutationImage.Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=registers ∧
      EqualOutside (Writes s.regs t.data.regs) s.dmem t.data.dmem ∧
      Corresponds (names.allocated base) nodeOffsets t.data.dmem
        (childInstalled d parentId direction key cidr entry.data.regs.rbp.toNat pid parentNode owner) ∧
      heap (names.allocated base)
        (target (childInstalled d parentId direction key cidr entry.data.regs.rbp.toNat pid parentNode owner))
        t.data.dmem=.ok ()) ⟨s,AllowedipsMutationImage.Add.entry+0x6f2⟩ := by
  have g := fields.geometry related
  have extent := g.bounded _ (node_allocation (List.mem_append_left _ parentNamed))
  change s.regs.rbx.toNat+72≤2^64 at extent
  have memoryEq := effect_connect bit (by change s.regs.rbx.toNat+24≤2^64; omega)
    baseRead directionRead indexRead indexApart checked
  have restored := child_connect_corresponds fields related pending parentNamed bit hasParent hasPeer
  have internal := pending_internal_connected (packed:=(s.regs.rbx.toNat+(direction+1)*8) ||| direction)
    pending g parentNamed bit
  have slotEq : s.regs.rbx.toNat+8+direction*8=s.regs.rbx.toNat+(direction+1)*8 := by omega
  rw [slotEq] at internal
  have shape := heap_installedChild owner related heapOk hasPeer
    (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent) bit empty sameWidth measure prefixEq side internal
  rw [←target_childInstalled d parentId direction key cidr entry.data.regs.rbp.toNat pid parentNode owner
    hasParent hasPeer (target_nodes_below related)] at shape
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (publication_checked fetch decoder checked)
  rintro t ⟨position,mem,regs,frame⟩
  exact ⟨position,mem,regs,frame,by simpa only [mem,memoryEq] using restored,
    by simpa only [mem,memoryEq] using shape⟩

#print axioms publication_restores
end Binary.Pair.Allowedips.ChildPublish
