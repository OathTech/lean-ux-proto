import AllowedipsChildResources

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Leanux.WG Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The continuous child branch from the same executable boundary and caller
resource assertions exercised by the paired runner. No intermediate execution,
decoder result, saved value or pending-node resource is assumed. -/
theorem initialization_child_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names : Names} {world : World} {entry : MachineState}
    {key cidr pid base parentId : Nat} {d : Device} {parentNode : AipNode} {owner : Peer} (c : Context)
    (checked : NodeInit.boundary names nodeOffsets world entry key cidr pid=.ok base)
    (device : world.wg.dev=some d)
    (parentNamed : (parentId,entry.data.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (empty : parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]?=some none)
    (resources : ChildResources.resources names nodeOffsets c entry.data base=.ok ()) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.regs.rbx=0 ∧ t.data.regs.rsp=entry.data.regs.rsp ∧ CallsReady c t.data ∧
      EqualOutside (fun a => NodeInit.EntryWrites names entry.data base a ∨
        SetupWrites entry.data.regs.rsp c a ∨
        PublishWrites entry.data.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
        entry.data.dmem t.data.dmem ∧
      Corresponds (names.allocated base) nodeOffsets t.data.dmem
        (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner) ∧
      heap (names.allocated base)
        (target (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner)) t.data.dmem=.ok ()) entry := by
  have ready := ChildResources.resources_ready resources
  have bit : key/2^(parentNode.bitlen-1-parentNode.cidr)%2<2 := Nat.mod_lt _ (by decide)
  exact initialization_child fetch decoder tracePc c checked device parentNamed hasParent hasPeer
    sameWidth measure prefixEq empty ready.extent ready.mapped ready.calls ready.initialContext
    ready.setupContext (ready.publishContext _ bit) ready.saved ready.projection ready.table
    (by rw [←sameWidth]; exact ready.query) (ready.destinations _ bit) ready.index

#print axioms initialization_child_checked
end Binary.Pair.Allowedips.ChildFinish
