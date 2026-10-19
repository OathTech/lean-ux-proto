import AllowedipsLoopCalls
import AllowedipsLoopScalar
import AllowedipsLoopPeer
import AllowedipsLoopValues

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation AllowedipsRelation
local instance : Labels := Image.linkedLabels

theorem cursor_eq (t : Executed) (pc : Int64) (atPC : t.machine.pc = pc) :
    (⟨⟨t.machine.data,pc⟩,t.history⟩ : Executed) = t := by
  rcases t with ⟨⟨data,address⟩,history⟩
  simp_all

/-- Matching-prefix path through the real peer-word load/CMOV and three
instrumentation calls, up to the full-length comparison. -/
theorem matched_to_full (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (tracePc : AllowedipsTracePcContract fetch) (traceCmp : AllowedipsTraceCmp1Contract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (nodes peers : Nat → BitVec 64) (bits query id : Nat) (node : Leanux.WG.AipNode)
    (atNode : s.regs.rbx.toBitVec = nodes id)
    (fields : NodeFields base.dmem nodes peers bits query id node)
    (matching : node.cidr ≤ common bits node.bits query)
    (apart : ∀ a, NodeReads nodes bits query id node a → ¬writes base.regs.rsp coverage a)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x90⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = AllowedipsImage.Lookup.entry+0xaf ∧
      t.machine.data.regs.rbx = s.regs.rbx ∧
      t.machine.data.regs.rbp = (if node.peer.isSome then s.regs.rbx else s.regs.rbp) ∧
      t.machine.data.regs.r15 = s.regs.r15 ∧
      ∃ peerPoint, peerPoint.pc = AllowedipsImage.Lookup.entry+0x9f ∧
        Trace base coverage rxSection history
          (events ++ [decision rxSection .findNodeHasPeer node.peer.isSome peerPoint]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x90⟩,history⟩ := by
  have first := call fetch (AllowedipsImage.Lookup.entry+0x90) "L_ffffffff810f31f0"
    (agree _ _ (by rfl)) .pc tracePc base s coverage frame rxSection history events observed last
    (by unfold Quiet; decide) (by constructor <;> decide)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,r14_1,r15_1,trace1⟩
  change t1.machine.pc = AllowedipsImage.Lookup.entry+0x95 at pc1
  have currentFields := fields.frame trace1.frame.memory apart
  obtain ⟨peerRead,nonnull,_⟩ := currentFields.2.2.2.2 matching
  have atNode1 : t1.machine.data.regs.rbx.toBitVec = nodes id := by rw [bx1]; exact atNode
  have loaded : t1.machine.data.dmem.loadInt t1.machine.data.regs.rbx.toBitVec 8 =
      some (pointer peers node.peer).toNat := by
    simpa [AllowedipsLayout.peer,←atNode1] using peerRead
  have peerChoice := pointer_some peers node.peer nonnull
  have selected : (if pointer peers node.peer == 0 then t1.machine.data.regs.rbp else t1.machine.data.regs.rbx) =
      (if node.peer.isSome then s.regs.rbx else s.regs.rbp) := by
    rw [bp1,bx1]
    cases has : node.peer.isSome <;> cases zero : pointer peers node.peer == 0 <;>
      simp_all only [bne,Bool.not_true,Bool.not_false,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  have second := historySteps_eventually fetch 3 _ _
    (has_peer fetch agree base t1.machine.data coverage (pointer peers node.peer) loaded trace1.frame rxSection
      t1.history events trace1.observed (by rw [←pc1]; exact trace1.last))
  rw [cursor_eq t1 _ pc1] at second
  apply eventually_trans (historyStep fetch) _ _ _ second
  rintro t2 ⟨pc2,regs2,trace2⟩
  rw [peerChoice] at trace2
  let nextEvents := events ++ [decision rxSection .findNodeHasPeer node.peer.isSome t2.machine]
  have trace2' : Trace base coverage rxSection t1.history nextEvents t2 := trace2
  have bx2 : t2.machine.data.regs.rbx = s.regs.rbx := by rw [regs2]; exact bx1
  have bp2 : t2.machine.data.regs.rbp = (if node.peer.isSome then s.regs.rbx else s.regs.rbp) := by
    rw [regs2]; exact selected
  have r15_2 : t2.machine.data.regs.r15 = s.regs.r15 := by rw [regs2]; exact r15_1
  have third := call fetch (AllowedipsImage.Lookup.entry+0x9f) "L_ffffffff810f31f0"
    (agree _ _ (by rfl)) .pc tracePc base t2.machine.data coverage trace2'.frame rxSection
    t2.history nextEvents trace2'.observed (by rw [←pc2]; exact trace2'.last)
    (by unfold Quiet; decide) (by constructor <;> decide)
  rw [cursor_eq t2 _ pc2] at third
  apply eventually_trans (historyStep fetch) _ _ _ third
  rintro t3 ⟨pc3,bx3,bp3,r14_3,r15_3,trace3⟩
  change t3.machine.pc = AllowedipsImage.Lookup.entry+0xa4 at pc3
  have fourth := full_arguments fetch agree base t3.machine.data coverage trace3.frame rxSection
    t3.history nextEvents trace3.observed (by rw [←pc3]; exact trace3.last)
  rw [cursor_eq t3 _ pc3] at fourth
  apply eventually_trans (historyStep fetch) _ _ _ fourth
  rintro t4 ⟨⟨pc4,regs4⟩,trace4⟩
  have fifth := call fetch (AllowedipsImage.Lookup.entry+0xaa) "L_ffffffff810f4040"
    (agree _ _ (by rfl)) .cmp1 traceCmp base t4.machine.data coverage trace4.frame rxSection
    t4.history nextEvents trace4.observed (by rw [←pc4]; exact trace4.last)
    (by unfold Quiet; decide) (by constructor <;> decide)
  rw [cursor_eq t4 _ pc4] at fifth
  apply eventually_weaken (historyStep fetch) _ _ _ _ fifth
  rintro t5 ⟨pc5,bx5,bp5,r14_5,r15_5,trace5⟩
  refine ⟨pc5,?_,?_,?_,t2.machine,pc2,trace1.trans (trace2'.trans (trace3.trans (trace4.trans trace5)))⟩
  · rw [bx5,regs4,bx3]; exact bx2
  · rw [bp5,regs4,bp3]; exact bp2
  · rw [r15_5,regs4,r15_3]; exact r15_2

#print axioms matched_to_full
end Binary.AllowedipsLoop
