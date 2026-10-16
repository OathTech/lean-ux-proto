import AllowedipsLoopPrefix

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation LookupObservation
local instance : Labels := Image.linkedLabels

theorem node_prefix (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contracts : CommonBits.Callbacks fetch) (traceCmp : AllowedipsTraceCmp1Contract fetch) (base s : MachineData)
    (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode)
    (family : bits = 32 ∨ bits = 128)
    (familyByte : base.regs.get (.low .r13 .W8) = .ofNat 8 bits)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (words : AllowedipsChild.QueryWords base.dmem (base.regs.rsp.toBitVec+16) bits query)
    (queryApart : ∀ a, InRange (base.regs.rsp.toBitVec+16) (bits/8) a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xd5⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if decide (node.cidr ≤ common bits node.bits query) then AllowedipsImage.Lookup.entry+0x90 else AllowedipsImage.Lookup.entry+0x101) ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      (t.machine.data.regs.get (.low .r15 .W8)).toNat = node.cidr ∧
      ∃ delta, delta.map CommonBits.pointView = commonSignature rxSection bits query node ∧
        Trace base coverage rxSection history (events ++ delta ++
          [decision rxSection .findNodePrefixMatches (decide (node.cidr ≤ common bits node.bits query)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xd5⟩,history⟩ := by
  have first := node_common fetch agree contracts base s coverage nodes peers bits query id node family familyByte
    atNode fields apart words queryApart frame rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,answer,delta,signature,trace1⟩
  have second := after_common_prefix fetch agree traceCmp base t1.machine.data coverage nodes peers bits query id node
    (by rw [bx1]; exact atNode) fields apart answer trace1.frame rxSection t1.history (events++delta)
    trace1.observed (by rw [←pc1]; exact trace1.last)
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_weaken (historyStep fetch) _ _ _ _ second
  rintro t2 ⟨pc2,bx2,bp2,cidr2,trace2⟩
  exact ⟨pc2,bx2.trans bx1,bp2.trans bp1,cidr2,delta,signature,trace1.trans trace2⟩

#print axioms node_prefix
end Binary.AllowedipsLoop
