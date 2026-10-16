import AllowedipsLoopIteration
import AllowedipsProjection

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation

/-- Invocation facts used by the loop. Each clause describes current bytes,
ABI values, or the named service contracts; none asserts future execution. -/
structure Setup (fetch : Int64 → Option Decoded) (base : MachineData)
    (coverage : CommonBitsCoverage.Context) (c : Config) (view : AllowedipsSource.NodeView) : Prop where
  decoder : AllowedipsDecoderAgreement fetch
  callbacks : CommonBits.Callbacks fetch
  cmp1 : AllowedipsTraceCmp1Contract fetch
  heap : TrieHeap base.dmem c.nodes c.peers view c.root c.bits c.key
  apart : ∀ a, TrieReads c.nodes view c.root c.bits c.key a → ¬writes base.regs.rsp coverage a
  width : (base.regs.get (.low .r12 .W8)).toNat = c.bits
  familyByte : base.regs.get (.low .r13 .W8) = .ofNat 8 c.bits
  words : AllowedipsChild.QueryWords base.dmem (base.regs.rsp.toBitVec+16) c.bits c.key
  queryApart : ∀ a, InRange (base.regs.rsp.toBitVec+16) (c.bits/8) a → ¬writes base.regs.rsp coverage a

def selectedNode (id : Nat) (node : Leanux.WG.AipNode) (previous : Option Nat) : Option Nat :=
  if node.peer.isSome then some id else previous

def stepSignature (rx bits query : Nat) (node : Leanux.WG.AipNode)
    (step : ForInStep AllowedipsSource.Acc) : List CommonBits.EventView :=
  commonSignature rx bits query node ++
    [CommonBits.decisionView rx .findNodePrefixMatches (decide (node.cidr ≤ common bits node.bits query))] ++
    if node.cidr ≤ common bits node.bits query then
      [CommonBits.decisionView rx .findNodeHasPeer node.peer.isSome,
        CommonBits.decisionView rx .findNodeFullLength (node.cidr == bits)] ++
      match step with
      | .done _ => []
      | .yield acc => [CommonBits.decisionView rx .findNodeNode acc.2.1.isSome]
    else []

def StepPost (nodes : Nat → BitVec 64) (step : ForInStep AllowedipsSource.Acc) (s : MachineState) : Prop :=
  match step with
  | .done acc => s.pc = AllowedipsImage.Lookup.entry+0x101 ∧ s.data.regs.rbp.toBitVec = pointer nodes acc.2.2
  | .yield acc => s.pc = (if acc.2.1.isSome then AllowedipsImage.Lookup.entry+0xd5 else AllowedipsImage.Lookup.entry+0x101) ∧
      s.data.regs.rbx.toBitVec = pointer nodes acc.2.1 ∧ s.data.regs.rbp.toBitVec = pointer nodes acc.2.2

theorem selected_pointer (nodes : Nat → BitVec 64) (id : Nat) (node : Leanux.WG.AipNode)
    (previous : Option Nat) (s : MachineData)
    (atNode : s.regs.rbx.toBitVec = nodes id) (atPrevious : s.regs.rbp.toBitVec = pointer nodes previous) :
    (if node.peer.isSome then s.regs.rbx else s.regs.rbp).toBitVec =
      pointer nodes (selectedNode id node previous) := by
  cases has : node.peer.isSome
  · simpa only [selectedNode,has,Bool.false_eq_true,ite_false] using atPrevious
  · simpa only [selectedNode,has,ite_true,pointer,Option.map_some,Option.getD_some] using atNode

theorem node_child {memory nodes peers bits query id node}
    (fields : NodeFields memory nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query) (short : node.cidr < bits) :
    ∃ next, node.bit[childIndex node query]? = some next := by
  have size := ((fields.2.2.2.2 matching).2.2 short).2.1
  have bound : childIndex node query < node.bit.size := by
    rw [size]
    exact Nat.mod_lt _ (by decide)
  exact ⟨node.bit[childIndex node query],Array.getElem?_eq_getElem bound⟩

#print axioms node_child
end Binary.AllowedipsLoop
