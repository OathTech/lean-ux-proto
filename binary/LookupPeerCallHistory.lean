import CallHistory
import OwnerWord

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

def peerArgument (s : MachineData) (peer : BitVec 64) : MachineData :=
  s.setReg (.low .rdi .W64) peer

def peerCalled (s : MachineData) (peer : BitVec 64) : MachineState :=
  Instrumentation.calledState (peerArgument s peer) (Image.Lookup.entry+0xba) Image.PeerGet.entry

/-- Load the entry's one physical peer word. Owner identity does not imply
    a non-NULL word or that the referenced peer has that owner's identity. -/
theorem peer_argument (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData) (peer : BitVec 64)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some (peer.toNat : Int))
    (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0xb2⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0xb2) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get64, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
    Effects.All, peerArgument, BitVec.take] at field ⊢
  rw [field]
  simp [Effects.All]
  rfl

/-- The real lookup-to-peer CALL and its pushed return address. This is not
    a contract for peer-get: its full instruction theorem must follow. -/
theorem peer_call_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData) (peer : BitVec 64)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some (peer.toNat : Int))
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (history : List MachineState) :
    historySteps fetch 2 (fun t => t.machine = peerCalled s peer ∧
      t.history = history ++ [⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩, t.machine])
      ⟨⟨s, Image.Lookup.entry+0xb2⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (peer_argument fetch agree s peer field history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩,
      history ++ [⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩]⟩ := by
    cases t; simp_all
  rw [cursor]
  have mapped' : ((peerArgument s peer).dmem.loadInt
      ((peerArgument s peer).regs.rsp.toBitVec-8) 8).isSome = true := by
    simpa [peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64] using mapped
  have call := Instrumentation.call_instruction fetch (Image.Lookup.entry+0xb5)
    "L_ffffffff81399610" (agree _ _ (by rfl)) (peerArgument s peer)
    (history ++ [⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩]) mapped'
  apply historySteps_mono fetch 1 _ _ _ _ call
  rintro t ⟨machine, recorded⟩
  have final : t.machine = peerCalled s peer := machine
  exact ⟨final, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using recorded⟩

theorem peer_call_observed (rxSection : Nat) (s : MachineData) (peer : BitVec 64) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry+0xb2⟩, ⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩,
        peerCalled s peer] =
      .ok [LookupObservation.call "wg_peer_get_maybe_zero" (peerCalled s peer)] := by
  simp [observeHistory, LookupObservation.edge, peerCalled, Instrumentation.calledState,
    Image.Lookup.entry, Image.PeerGet.entry]
  rfl

theorem peer_call_entry (s : MachineData) (peer : BitVec 64)
    (aligned : s.regs.rsp.toNat % 8 = 0) :
    TrustBase.EntryFrame (peerCalled s peer) (Image.Lookup.entry+0xba).toUInt64 ∧
      (peerCalled s peer).data.regs.rdi.toBitVec = peer := by
  constructor
  · constructor
    · change ((peerArgument s peer).regs.rsp-8).toNat % 8 = 0
      have sp : (peerArgument s peer).regs.rsp = s.regs.rsp := by
        simp [peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64]
      rw [sp]
      simp only [UInt64.toNat_sub, show (8 : UInt64).toNat = 8 from rfl]
      have bound := s.regs.rsp.toNat_lt_size
      omega
    · unfold peerCalled Instrumentation.calledState
      simp only [UInt64.toBitVec_sub, show (8 : UInt64).toBitVec = 8#64 from rfl]
      exact load64_store _ _ _
  · simp [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg,
      Reg64s.set, Reg64s.set64]

theorem peer_call_frame (s : MachineData) (peer : BitVec 64) :
    EqualOutside (InRange (s.regs.rsp.toBitVec-8) 8) s.dmem (peerCalled s peer).data.dmem := by
  simpa [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg,
    Reg64s.set, Reg64s.set64] using
    storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (Image.Lookup.entry+0xba).toBitVec.toInt

#print axioms peer_call_history
#print axioms peer_call_observed
#print axioms peer_call_entry
#print axioms peer_call_frame
end Binary.LookupHistory
