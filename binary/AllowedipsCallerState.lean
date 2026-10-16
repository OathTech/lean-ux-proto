import AllowedipsCaller
import AllowedipsPeerExecution
import CommonBitsCalls

namespace Binary.AllowedipsCaller
open TrustBase
local instance : Labels := Image.linkedLabels

def Scratch (s : MachineData) : BitVec 64 → Prop := InRange (s.regs.rsp.toBitVec-64) 64

structure Ready (c : CommonBitsCoverage.Context) (s : MachineData) : Prop where
  calls : CommonBitsCoverage.CallsReady c s
  mapped : ∀ n < 8, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true
  separate : ∀ a, c.bytes a → ¬Scratch s a

theorem pushed_shape (s : MachineData) (peer : BitVec 64) :
    (peerCalled s peer).data.regs = {s.regs with rdi := .ofBitVec peer, rsp := s.regs.rsp-8} ∧
    (peerCalled s peer).data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8
      (AllowedipsImage.Lookup.entry+0x119).toBitVec.toInt := by
  simp [peerCalled, peerArgument, Instrumentation.calledState, MachineData.setReg,
    Reg64s.set,Reg64s.set64]

theorem scratch_base (s : MachineData) (peer : BitVec 64) :
    (peerCalled s peer).data.regs.rsp.toBitVec-56 = s.regs.rsp.toBitVec-64 := by
  rw [(pushed_shape s peer).1]
  simp only [UInt64.toBitVec_sub,BitVec.sub_sub]
  rfl

theorem Ready.entry {c s} (ready : Ready c s) (peer : BitVec 64) :
    EntryFrame (peerCalled s peer) AllowedipsPeerExecution.returnAddress ∧
    c.At (peerCalled s peer).data.dmem ∧
    (∀ n < 7, ((peerCalled s peer).data.dmem.loadInt
      ((peerCalled s peer).data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true) ∧
    (∀ a, c.bytes a → ¬InRange ((peerCalled s peer).data.regs.rsp.toBitVec-56) 56 a) ∧
    (∀ a, c.writes a → ¬InRange ((peerCalled s peer).data.regs.rsp.toBitVec-56) 64 a) := by
  have readyArg : CommonBitsCoverage.CallsReady c (peerArgument s peer) :=
    ready.calls.congr rfl (by simp [peerArgument,MachineData.setReg,Reg64s.set,Reg64s.set64])
  have entry := CommonBitsCoverage.called_ready c (peerArgument s peer)
    (AllowedipsImage.Lookup.entry+0x119) Image.PeerGet.entry readyArg
  refine ⟨entry.1,entry.2,?_,?_,?_⟩
  · intro n hn
    rw [(pushed_shape s peer).1,(pushed_shape s peer).2]
    have address : (s.regs.rsp-8).toBitVec-.ofNat 64 ((n+1)*8) =
        s.regs.rsp.toBitVec-.ofNat 64 ((n+2)*8) := by
      rw [UInt64.toBitVec_sub,BitVec.sub_sub]
      have num : (n+2)*8 = 8+(n+1)*8 := by omega
      rw [num,BitVec.ofNat_add]; rfl
    rw [address]
    exact storeInt_defined _ _ _ _ _ _ (ready.mapped (n+1) (by omega))
  · intro a bytes inside
    rw [scratch_base] at inside
    obtain ⟨n,hn,eq⟩ := inside
    exact ready.separate a bytes ⟨n,by omega,eq⟩
  · intro a written inside
    rw [scratch_base] at inside
    exact ready.separate a (.inr (.inr ⟨written.1,.inr written.2⟩)) inside

theorem Ready.count {c s} (ready : Ready c s) (peer : BitVec 64) (count : UInt32)
    (field : s.dmem.loadInt (peer+0x420) 4 = some count.toNat)
    (apart : ∀ a, InRange (peer+0x420) 4 a → ¬Scratch s a) :
    (peerCalled s peer).data.dmem.loadInt
      ((peerCalled s peer).data.regs.rdi.toBitVec+0x420) 4 = some count.toNat := by
  rw [(pushed_shape s peer).1]
  change (peerCalled s peer).data.dmem.loadInt (peer+0x420) 4 = _
  have frame := peer_call_frame s peer
  have read := frame.loadInt (peer+0x420) 4 (by
    intro n hn inside
    obtain ⟨i,hi,eq⟩ := inside
    have base : s.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-64+56 := by
      change _ = s.regs.rsp.toBitVec-(8+56)+56
      rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
    apply apart _ ⟨n,hn,rfl⟩
    refine ⟨56+i,by omega,?_⟩
    simpa only [base,BitVec.ofNat_add,BitVec.add_assoc,show (56 : BitVec 64)=56#64 from rfl] using eq)
  exact read.symm.trans field

#print axioms Ready.entry
#print axioms Ready.count
end Binary.AllowedipsCaller
