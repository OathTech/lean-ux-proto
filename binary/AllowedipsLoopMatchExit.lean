import AllowedipsLoopNext

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- Matching prefix through the physical full-length guard. Source widths
are compared only through the argument byte, as the C ABI requires. -/
theorem matched_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (tracePc : AllowedipsTracePcContract fetch) (traceCmp : AllowedipsTraceCmp1Contract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (width : (base.regs.get (.low .r12 .W8)).toNat = bits)
    (cidr : (s.regs.get (.low .r15 .W8)).toNat = node.cidr)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x90⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if node.cidr == bits then AllowedipsImage.Lookup.entry+0x101 else AllowedipsImage.Lookup.entry+0xb4) ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧
      t.machine.data.regs.rbp = (if node.peer.isSome then s.regs.rbx else s.regs.rbp) ∧
      ∃ peerPoint, peerPoint.pc = AllowedipsImage.Lookup.entry+0x9f ∧
        Trace base coverage rxSection history
          (events ++ [decision rxSection .findNodeHasPeer node.peer.isSome peerPoint,
            decision rxSection .findNodeFullLength (node.cidr == bits) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x90⟩,history⟩ := by
  have first := matched_to_full fetch agree tracePc traceCmp base s coverage nodes peers bits query id node
    atNode fields matching apart frame rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,r15_1,peerPoint,peerPC,trace1⟩
  have second := historySteps_eventually fetch 2 _ _
    (full_guard fetch agree base t1.machine.data coverage trace1.frame rxSection t1.history _
      trace1.observed (by rw [←pc1]; exact trace1.last))
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_weaken (historyStep fetch) _ _ _ _ second
  rintro t2 ⟨pc2,regs2,trace2⟩
  have widths : (t1.machine.data.regs.get (.low .r12 .W8)).toNat = bits := by
    simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      trace1.frame.width] using width
  have cidrs : (t1.machine.data.regs.get (.low .r15 .W8)).toNat = node.cidr := by
    simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,r15_1] using cidr
  have choice : (t1.machine.data.regs.get (.low .r12 .W8) == t1.machine.data.regs.get (.low .r15 .W8)) =
      (node.cidr == bits) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [←BitVec.toNat_inj,widths,cidrs]
    exact eq_comm
  rw [choice] at pc2 trace2
  refine ⟨pc2,?_,?_,peerPoint,peerPC,?_⟩
  · rw [regs2]; exact bx1
  · rw [regs2]; exact bp1
  simpa only [List.append_assoc,List.singleton_append] using trace1.trans trace2

/-- Non-full matching path rejoins the next loop guard, including the actual
next-node observation and retaining both preceding decision successors. -/
theorem matched_continue (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (tracePc : AllowedipsTracePcContract fetch) (traceCmp : AllowedipsTraceCmp1Contract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode) (next : Option Nat)
    (family : bits = 32 ∨ bits = 128)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (width : (base.regs.get (.low .r12 .W8)).toNat = bits)
    (cidr : (s.regs.get (.low .r15 .W8)).toNat = node.cidr)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query) (short : node.cidr < bits)
    (atChild : node.bit[childIndex node query]? = some next)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (words : AllowedipsChild.QueryWords base.dmem (base.regs.rsp.toBitVec+16) bits query)
    (queryApart : ∀ a, InRange (base.regs.rsp.toBitVec+16) (bits/8) a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x90⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if next.isSome then AllowedipsImage.Lookup.entry+0xd5 else AllowedipsImage.Lookup.entry+0x101) ∧
      t.machine.data.regs.rbx.toBitVec = pointer nodes next ∧
      t.machine.data.regs.rbp = (if node.peer.isSome then s.regs.rbx else s.regs.rbp) ∧
      ∃ peerPoint fullPoint,
        peerPoint.pc = AllowedipsImage.Lookup.entry+0x9f ∧ fullPoint.pc = AllowedipsImage.Lookup.entry+0xb4 ∧
        Trace base coverage rxSection history
          (events ++ [decision rxSection .findNodeHasPeer node.peer.isSome peerPoint,
            decision rxSection .findNodeFullLength false fullPoint,
            decision rxSection .findNodeNode next.isSome t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x90⟩,history⟩ := by
  have first := matched_guard fetch agree tracePc traceCmp base s coverage nodes peers bits query id node
    atNode width cidr fields matching apart frame rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,peerPoint,peerPC,trace1⟩
  have notFull : (node.cidr == bits) = false := by simp only [beq_eq_false_iff_ne]; omega
  rw [notFull] at pc1 trace1
  simp only [Bool.false_eq_true,ite_false] at pc1
  have second := short_to_next fetch agree tracePc base t1.machine.data coverage nodes peers bits query id node next
    family (by rw [bx1]; exact atNode) fields matching short atChild apart words queryApart trace1.frame rxSection
    t1.history _ trace1.observed (by rw [←pc1]; exact trace1.last)
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_weaken (historyStep fetch) _ _ _ _ second
  rintro t2 ⟨pc2,bx2,bp2,trace2⟩
  refine ⟨pc2,bx2,bp2.trans bp1,peerPoint,t1.machine,peerPC,pc1,?_⟩
  simpa only [List.append_assoc,List.cons_append,List.nil_append] using trace1.trans trace2

#print axioms matched_guard
#print axioms matched_continue
end Binary.AllowedipsLoop
