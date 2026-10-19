import AllowedipsLoopCaller
import AllowedipsLoopSignature

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation LookupObservation
local instance : Labels := Image.linkedLabels

private theorem low_byte (word : BitVec 64) :
    ((word.extractLsb' 0 32).setWidth 64).extractLsb' 0 8 = word.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- One nonempty trie node's actual instrumentation, common_bits arguments,
CALL and return. Conditional source fields supply every physical data read. -/
theorem node_common (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contracts : CommonBits.Callbacks fetch) (base s : MachineData)
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
      t.machine.pc = AllowedipsImage.Lookup.entry+0xea ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧ t.machine.data.regs.rbp = s.regs.rbp ∧
      (t.machine.data.regs.get (.low .rax .W8)).toNat = common bits node.bits query ∧
      ∃ delta, delta.map CommonBits.pointView = commonSignature rxSection bits query node ∧
        Trace base coverage rxSection history (events ++ delta) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xd5⟩,history⟩ := by
  have first := call fetch (AllowedipsImage.Lookup.entry+0xd5) "L_ffffffff810f31f0"
    (agree _ _ (by rfl)) .pc contracts.pc base s coverage frame rxSection history events observed last
    (by unfold Quiet; decide) (by constructor <;> decide)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,r14_1,r15_1,trace1⟩
  change t1.machine.pc = AllowedipsImage.Lookup.entry+0xda at pc1
  have second := common_arguments fetch agree base t1.machine.data coverage trace1.frame rxSection
    t1.history events trace1.observed (by rw [←pc1]; exact trace1.last)
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_trans (historyStep fetch) _ _ _ second
  rintro t2 ⟨⟨pc2,regs2⟩,trace2⟩
  have argNode : t2.machine.data.regs.rdi.toBitVec = nodes id := by
    rw [regs2]; exact congrArg UInt64.toBitVec bx1 |>.trans atNode
  have argQuery : t2.machine.data.regs.rsi.toBitVec = base.regs.rsp.toBitVec+16 := by
    rw [regs2,UInt64.toBitVec_add,trace1.frame.stack]; rfl
  have argFamily : t2.machine.data.regs.get (.low .rdx .W8) = .ofNat 8 bits := by
    rw [regs2]
    simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,
      UInt64.toBitVec_ofBitVec,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self,low_byte,trace1.frame.family] using familyByte
  have keyFields := (fields.frame trace2.frame.memory apart).2.2.1
  change KeyFields t2.machine.data.dmem (nodes id+32) bits node.bits query at keyFields
  rw [←argNode] at keyFields
  have queryWords := query_frame family words trace2.frame.memory queryApart
  rw [←argQuery] at queryWords
  have caller := input_caller base t2.machine.data coverage bits node.bits query family trace2.frame
    argFamily keyFields queryWords
    (by
      intro a read
      apply apart a
      left
      change KeyReads (nodes id+32) bits node.bits query a
      simpa only [argNode] using read)
    (by simpa only [argQuery] using queryApart)
  have third := common_call fetch agree contracts base t2.machine.data (input t2.machine.data bits node.bits query)
    coverage trace2.frame caller rxSection t2.history events trace2.observed (by rw [←pc2]; exact trace2.last)
  rw [cursor_eq t2 _ pc2] at third
  apply eventually_weaken (historyStep fetch) _ _ _ _ third
  rintro t3 ⟨pc3,bx3,bp3,r14_3,r15_3,result,delta,signature,trace3⟩
  have keyBounds := fields.2.2.1
  rw [input_result _ bits node.bits query family keyBounds.1 keyBounds.2.1] at result
  rw [input_signature _ bits query rxSection node family keyBounds.1 keyBounds.2.1] at signature
  refine ⟨pc3,?_,?_,result,delta,signature,trace1.trans (trace2.trans trace3)⟩
  · rw [bx3,regs2]; exact bx1
  · rw [bp3,regs2]; exact bp1

#print axioms node_common
end Binary.AllowedipsLoop
