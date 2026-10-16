import AllowedipsLoopNodeCommon

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation LookupObservation
local instance : Labels := Image.linkedLabels

private theorem low8_low32 (word : BitVec 64) :
    ((word.extractLsb' 0 32).setWidth 64).extractLsb' 0 8 = word.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem low8_widen (word : BitVec 8) :
    (word.setWidth 64).extractLsb' 0 8 = word := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

/-- Real CIDR load, comparison callback and prefix branch after common_bits.
Only AL is used to justify the C comparison, despite noncanonical upper EAX. -/
theorem after_common_prefix (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (traceCmp : AllowedipsTraceCmp1Contract fetch) (base s : MachineData)
    (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (answer : (s.regs.get (.low .rax .W8)).toNat = common bits node.bits query)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xea⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if decide (node.cidr ≤ common bits node.bits query) then
        AllowedipsImage.Lookup.entry+0x90 else AllowedipsImage.Lookup.entry+0x101) ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      (t.machine.data.regs.get (.low .r15 .W8)).toNat = node.cidr ∧
      Trace base coverage rxSection history
        (events ++ [decision rxSection .findNodePrefixMatches (decide (node.cidr ≤ common bits node.bits query)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xea⟩,history⟩ := by
  have cidrRead := (fields.frame frame.memory apart).2.2.2.1
  have cidrValue := byte_value node.cidr fields.2.1
  have field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1 = some (BitVec.ofNat 8 node.cidr).toNat := by
    rw [atNode,cidrValue]
    exact cidrRead
  have first := prefix_arguments fetch agree base s coverage (.ofNat 8 node.cidr) field frame rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨⟨pc1,regs1⟩,trace1⟩
  have second := call fetch (AllowedipsImage.Lookup.entry+0xf7) "L_ffffffff810f3e40"
    (agree _ _ (by rfl)) .cmp1 traceCmp base t1.machine.data coverage trace1.frame rxSection
    t1.history events trace1.observed (by rw [←pc1]; exact trace1.last)
    (by unfold Quiet; decide) (by constructor <;> decide)
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_trans (historyStep fetch) _ _ _ second
  rintro t2 ⟨pc2,bx2,bp2,r14_2,r15_2,trace2⟩
  change t2.machine.pc = AllowedipsImage.Lookup.entry+0xfc at pc2
  have cidr : (t2.machine.data.regs.get (.low .r15 .W8)).toNat = node.cidr := by
    simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      r15_2,regs1,UInt64.toBitVec_ofBitVec,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self,low8_widen]
    exact cidrValue
  have commonValue : (t2.machine.data.regs.get (.low .r14 .W8)).toNat = common bits node.bits query := by
    simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      r14_2,regs1,UInt64.toBitVec_ofBitVec,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self,low8_low32] using answer
  have third := historySteps_eventually fetch 2 _ _
    (prefix_guard fetch agree base t2.machine.data coverage trace2.frame rxSection t2.history events
      trace2.observed (by rw [←pc2]; exact trace2.last))
  rw [cursor_eq t2 _ pc2] at third
  apply eventually_weaken (historyStep fetch) _ _ _ _ third
  rintro t3 ⟨pc3,regs3,trace3⟩
  rw [cidr,commonValue] at pc3 trace3
  refine ⟨pc3,?_,?_,?_,trace1.trans (trace2.trans trace3)⟩
  · rw [regs3,bx2,regs1]
  · rw [regs3,bp2,regs1]
  · rw [regs3]; exact cidr

#print axioms after_common_prefix
end Binary.AllowedipsLoop
