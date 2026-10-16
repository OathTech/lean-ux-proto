import AllowedipsCallerLive
import AllowedipsResultGuard

namespace Binary.AllowedipsCaller
open TrustBase
local instance : Labels := Image.linkedLabels

theorem live_call (fetch : Int64 → Option Decoded)
    (lookupAgree : AllowedipsDecoderAgreement fetch) (agree : AnchoredDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch) (traceByte : AllowedipsTraceConstCmp1Contract fetch)
    (caller : MachineData) (peer : BitVec 64) (coverage : CommonBitsCoverage.Context)
    (ready : Ready coverage caller) (nonnull : peer ≠ 0)
    (nodePeer : caller.dmem.loadInt caller.regs.rbp.toBitVec 8 = some peer.toNat)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : caller.dmem.loadInt (peer+0x420) 4 = some count.toNat)
    (countStack : ∀ a, InRange (peer+0x420) 4 a → ¬Scratch caller a)
    (countServices : ∀ a, coverage.bytes a → ¬InRange (peer+0x420) 4 a)
    (rxSection : Nat) (history : List MachineState) :
    Eventually (historyStep fetch) (fun t => ∃ helper,
      LivePost caller peer coverage count rxSection helper ∧
      t.machine=helper.machine ∧
      t.history=history ++ [⟨peerArgument caller peer,AllowedipsImage.Lookup.entry+0x114⟩] ++ helper.history)
      ⟨⟨caller,AllowedipsImage.Lookup.entry+0x110⟩,history⟩ := by
  have first := historySteps_eventually fetch 2 _ _
    (peer_call_history fetch lookupAgree caller peer nodePeer ready.calls.mapped history)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro called ⟨machine,recorded⟩
  have cursor : called = ⟨peerCalled caller peer,
      (history ++ [⟨peerArgument caller peer,AllowedipsImage.Lookup.entry+0x114⟩]) ++ [peerCalled caller peer]⟩ := by
    cases called; simp_all [List.append_assoc]
  rw [cursor]
  have helper := live_entry fetch agree contract traceCmp traceByte caller peer coverage ready nonnull
    count nonzero bound field countStack countServices rxSection
  exact history_prepend fetch _ _ helper _

theorem live_result (fetch : Int64 → Option Decoded)
    (lookupAgree : AllowedipsDecoderAgreement fetch) (agree : AnchoredDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch) (traceByte : AllowedipsTraceConstCmp1Contract fetch)
    (caller : MachineData) (peer : BitVec 64) (coverage : CommonBitsCoverage.Context)
    (ready : Ready coverage caller) (nonnull : peer ≠ 0)
    (nodePeer : caller.dmem.loadInt caller.regs.rbp.toBitVec 8 = some peer.toNat)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : caller.dmem.loadInt (peer+0x420) 4 = some count.toNat)
    (countStack : ∀ a, InRange (peer+0x420) 4 a → ¬Scratch caller a)
    (countServices : ∀ a, coverage.bytes a → ¬InRange (peer+0x420) 4 a)
    (rxSection : Nat) (history : List MachineState) :
    Eventually (historyStep fetch) (fun t => ∃ helper guard,
      LivePost caller peer coverage count rxSection helper ∧
      CommonBits.Local (fun _ => False) helper.machine rxSection
        [CommonBits.decisionView rxSection .lookupPeerGone false] guard ∧
      guard.machine.pc=AllowedipsImage.Lookup.entry+0x122 ∧
      guard.machine.data.regs=helper.machine.data.regs ∧
      guard.machine.data.dmem=helper.machine.data.dmem ∧
      t.machine=guard.machine ∧
      t.history=(history ++ [(⟨peerArgument caller peer,AllowedipsImage.Lookup.entry+0x114⟩ : MachineState)] ++ helper.history).dropLast ++ guard.history)
      ⟨⟨caller,AllowedipsImage.Lookup.entry+0x110⟩,history⟩ := by
  have first := live_call fetch lookupAgree agree contract traceCmp traceByte caller peer coverage
    ready nonnull nodePeer count nonzero bound field countStack countServices rxSection history
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro callee ⟨helper,post,machine,recorded⟩
  have pc : helper.machine.pc=AllowedipsImage.Lookup.entry+0x119 := post.1.1
  have notZero : (helper.machine.data.regs.get (.low .rax .W64) == 0)=false := by
    have value := post.2.2.1
    rw [(pushed_shape caller peer).1] at value
    simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,value]
    simpa using nonnull
  have executed := Allowedips.result_guard fetch lookupAgree helper.machine.data rxSection
  have initialEq : (⟨helper.machine.data,AllowedipsImage.Lookup.entry+0x119⟩ : MachineState)=helper.machine := by rw [←pc]
  rw [initialEq,notZero] at executed
  have joined := history_prepend fetch _ _ executed callee.history.dropLast
  have last : callee.history.getLast?=some callee.machine := by
    rw [recorded,machine,List.getLast?_append,post.2.2.2.2.2.2.1]
    rfl
  rw [machine] at last
  rw [AllowedipsLoop.history_restore last] at joined
  have cursor : (⟨helper.machine,callee.history⟩ : Executed)=callee := by rw [←machine]
  rw [cursor] at joined
  apply eventually_weaken (historyStep fetch) _ _ _ _ joined
  rintro final ⟨guard,⟨⟨guardPC,regs,memory⟩,trace⟩,finalMachine,finalHistory⟩
  exact ⟨helper,guard,post,trace,guardPC,regs,memory,finalMachine,by rw [finalHistory,recorded]⟩

#print axioms live_result

#print axioms live_call
end Binary.AllowedipsCaller
