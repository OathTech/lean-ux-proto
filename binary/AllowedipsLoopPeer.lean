import AllowedipsLoopFrame
import AllowedipsLoopObservation
import AllowedipsHistory

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

def peerLoaded (s : MachineData) (peer : BitVec 64) : MachineData :=
  {s with regs := {s.regs with rax := .ofBitVec peer}}

def peerTested (s : MachineData) (peer : BitVec 64) (af : Bool) : MachineData :=
  LookupHistory.tested (.low .rax .W64) (peerLoaded s peer) af

def peerSelected (s : MachineData) (peer : BitVec 64) (af : Bool) : MachineData :=
  {peerTested s peer af with regs := {s.regs with
    rax := .ofBitVec peer,rbp := if peer == 0 then s.regs.rbp else s.regs.rbx}}

theorem peer_load_history (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (peer : BitVec 64) (history : List MachineState)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some peer.toNat) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x95⟩,history⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x95) = some _ from rfl)
  refine instruction_history fetch ⟨s,AllowedipsImage.Lookup.entry+0x95⟩ history
    (fun t => t = ⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩) ?_
  simp only [instructionStep,here]
  refine ⟨by decide,?_⟩
  simp [Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,
    MachineData.load,MachineData.set,MachineData.setReg,AddrExpr.interp,
    ConstExpr.interp,Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_toInt,
    Effects.All,field,peerLoaded,AllowedipsImage.Lookup.entry]

theorem peer_test_history (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (peer : BitVec 64) (history : List MachineState) :
    historySteps fetch 1 (fun t => ∃ af,
      t.machine = ⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩,history⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x98) = some _ from rfl)
  simp only [historySteps,historyStep,instructionStep,here]
  refine ⟨by decide,?_⟩
  simp only [Instr.interp,Operation.interp,RegOrMem.interp,Operand.interp,Effects.All,BitVec.and_self]
  intro af
  exact ⟨af,rfl,trivial⟩

theorem peer_select_history (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (peer : BitVec 64) (af : Bool) (history : List MachineState) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨peerSelected s peer af,AllowedipsImage.Lookup.entry+0x9f⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩,history⟩ := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x9b) = some _ from rfl)
  refine instruction_history fetch ⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩ history
    (fun t => t = ⟨peerSelected s peer af,AllowedipsImage.Lookup.entry+0x9f⟩) ?_
  simp only [instructionStep,here]
  refine ⟨by decide,?_⟩
  simp [Instr.interp,Operation.interp,RegOrMem.interp,
    MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,
    Effects.All,StatusFlags.from_result,CondCode.interp,
    peerLoaded,peerTested,peerSelected,LookupHistory.tested,AllowedipsImage.Lookup.entry]
  split <;> simp_all

/-- The load, TEST and CMOVNE successors, including TEST's universal AF. -/
theorem has_peer_history (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (peer : BitVec 64) (history : List MachineState)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some peer.toNat) :
    historySteps fetch 3 (fun t => ∃ af,
      t.machine = ⟨peerSelected s peer af,AllowedipsImage.Lookup.entry+0x9f⟩ ∧
      t.history = history ++ [⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩,
        ⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩,t.machine])
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x95⟩,history⟩ := by
  rw [show 3=1+(1+1) from rfl,historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (peer_load_history fetch agree s peer history field)
  rintro t ⟨machine,recorded⟩
  have cursor : t = ⟨⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩,
      history ++ [⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩]⟩ := by cases t; simp_all
  rw [cursor,historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (peer_test_history fetch agree s peer _)
  rintro tested ⟨af,machine,recorded⟩
  have cursor : tested = ⟨⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩,
      (history ++ [⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩]) ++
        [⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩]⟩ := by cases tested; simp_all
  rw [cursor]
  apply historySteps_mono fetch 1 _ _ _ _ (peer_select_history fetch agree s peer af _)
  rintro final ⟨machine,recorded⟩
  exact ⟨af,machine,by simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using recorded⟩

theorem has_peer (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (peer : BitVec 64) (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some peer.toNat)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x95⟩) :
    historySteps fetch 3 (fun t =>
      t.machine.pc = AllowedipsImage.Lookup.entry+0x9f ∧
      t.machine.data.regs = {s.regs with
        rax := .ofBitVec peer,rbp := if peer == 0 then s.regs.rbp else s.regs.rbx} ∧
      Trace base coverage rxSection history
        (events ++ [decision rxSection .findNodeHasPeer (peer != 0) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x95⟩,history⟩ := by
  apply historySteps_mono fetch 3 _ _ _ _ (has_peer_history fetch agree s peer history field)
  rintro t ⟨af,machine,recorded⟩
  let first : MachineState := ⟨peerLoaded s peer,AllowedipsImage.Lookup.entry+0x98⟩
  let second : MachineState := ⟨peerTested s peer af,AllowedipsImage.Lookup.entry+0x9b⟩
  have nextFrame : Frame base coverage t.machine.data := by
    rw [machine]
    exact frame.congr rfl rfl rfl rfl
  have pathEq : t.history = history.dropLast ++
      [⟨s,AllowedipsImage.Lookup.entry+0x95⟩,first,second,t.machine] := by
    have restored := congrArg (fun h => h ++ [first,second,t.machine]) (history_restore last)
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have wordDecision : ((UInt64.ofBitVec peer) != (0 : UInt64)) = (peer != 0) := rfl
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0x95⟩,first,second,t.machine] =
      .ok [decision rxSection .findNodeHasPeer (peer != 0) t.machine] := by
    have e1 := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x95⟩ first
      (by change Quiet (AllowedipsImage.Lookup.entry+0x95); unfold Quiet; decide)
    have e2 := quiet_edge rxSection first second
      (by change Quiet (AllowedipsImage.Lookup.entry+0x98); unfold Quiet; decide)
    simp only [observeHistory,e1,e2]
    rw [machine]
    simp [AllowedipsObservation.edge,second,peerTested,LookupHistory.tested,peerLoaded,wordDecision,
      choice,AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
    rfl
  have traced := Trace.of_path observed last _ rfl pathEq (by simp) nextFrame _ localObserved
    (by
      intro q member cut
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq | eq | eq
      · subst q; exact frame.memory
      · subst q; exact frame.memory
      · subst q; exact frame.memory
      · subst q; exact nextFrame.memory)
    (by
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq | eq
      · subst q
        change AllowedipsImage.Lookup.entry+0x95 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x95 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0x98 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x98 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0x9b ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x9b ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide)
  exact ⟨by rw [machine],by rw [machine]; rfl,traced⟩

#print axioms has_peer_history
#print axioms has_peer
end Binary.AllowedipsLoop
