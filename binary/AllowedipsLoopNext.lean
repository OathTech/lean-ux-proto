import AllowedipsLoopMatched
import AllowedipsLoopGuards

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation AllowedipsRelation
local instance : Labels := Image.linkedLabels

/-- A non-full matching node executes the real callback, six-instruction
child selection and null test. The next-node event uses the actual branch. -/
theorem short_to_next (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (tracePc : AllowedipsTracePcContract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode) (next : Option Nat)
    (family : bits = 32 ∨ bits = 128)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query) (short : node.cidr < bits)
    (atChild : node.bit[childIndex node query]? = some next)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (words : AllowedipsChild.QueryWords base.dmem (base.regs.rsp.toBitVec+16) bits query)
    (queryApart : ∀ a, InRange (base.regs.rsp.toBitVec+16) (bits/8) a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xb4⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = (if next.isSome then AllowedipsImage.Lookup.entry+0xd5 else AllowedipsImage.Lookup.entry+0x101) ∧
      t.machine.data.regs.rbx.toBitVec = pointer nodes next ∧
      t.machine.data.regs.rbp = s.regs.rbp ∧
      Trace base coverage rxSection history
        (events ++ [decision rxSection .findNodeNode next.isSome t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xb4⟩,history⟩ := by
  have first := call fetch (AllowedipsImage.Lookup.entry+0xb4) "L_ffffffff810f31f0"
    (agree _ _ (by rfl)) .pc tracePc base s coverage frame rxSection history events observed last
    (by unfold Quiet; decide) (by constructor <;> decide)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,r14_1,r15_1,trace1⟩
  change t1.machine.pc = AllowedipsImage.Lookup.entry+0xb9 at pc1
  have currentFields := fields.frame trace1.frame.memory apart
  have currentWords := query_frame family words trace1.frame.memory queryApart
  rw [←trace1.frame.stack] at currentWords
  have second := child_step fetch agree base t1.machine.data coverage nodes peers bits query id node next
    family (by rw [bx1]; exact atNode) currentFields matching short atChild currentWords trace1.frame
    rxSection t1.history events trace1.observed (by rw [←pc1]; exact trace1.last)
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_trans (historyStep fetch) _ _ _ second
  rintro t2 ⟨⟨pc2,regs2⟩,trace2⟩
  have third := historySteps_eventually fetch 2 _ _
    (next_guard fetch agree base t2.machine.data coverage trace2.frame rxSection
      t2.history events trace2.observed (by rw [←pc2]; exact trace2.last))
  rw [cursor_eq t2 _ pc2] at third
  apply eventually_weaken (historyStep fetch) _ _ _ _ third
  rintro t3 ⟨pc3,regs3,trace3⟩
  have low : t2.machine.data.regs.get (.low .rbx .W64) = pointer nodes next := by
    rw [regs2]
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  obtain ⟨_,_,childFields⟩ := fields.2.2.2.2 matching
  have nonnull := ((childFields short).2.2.2.2 next atChild).2
  have choice := pointer_some nodes next nonnull
  change (!(pointer nodes next == 0)) = next.isSome at choice
  have jump : (if pointer nodes next == 0 then AllowedipsImage.Lookup.entry+0x101 else AllowedipsImage.Lookup.entry+0xd5) =
      (if next.isSome then AllowedipsImage.Lookup.entry+0xd5 else AllowedipsImage.Lookup.entry+0x101) := by
    cases has : next.isSome <;> cases zero : pointer nodes next == 0 <;> simp_all
  rw [low,jump] at pc3
  rw [low,choice] at trace3
  refine ⟨pc3,?_,?_,trace1.trans (trace2.trans trace3)⟩
  · rw [regs3,regs2]
  · rw [regs3,regs2]; exact bp1

#print axioms short_to_next
end Binary.AllowedipsLoop
