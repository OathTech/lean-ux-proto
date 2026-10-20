import AllowedipsLoopFrame
import AllowedipsLoopObservation
import AllowedipsHistory

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

theorem prefix_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xfc⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if decide ((s.regs.get (.low .r15 .W8)).toNat ≤ (s.regs.get (.low .r14 .W8)).toNat) then AllowedipsImage.Lookup.entry+0x90
        else AllowedipsImage.Lookup.entry+0x101) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history
        (events ++ [decision rxSection .findNodePrefixMatches (decide ((s.regs.get (.low .r15 .W8)).toNat ≤ (s.regs.get (.low .r14 .W8)).toNat)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xfc⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.prefix_history fetch agree s history)
  rintro t ⟨regs,memory,pc,mid,recorded,midPC,midRegs,midMem⟩
  have nextFrame : Frame base coverage t.machine.data :=
    frame.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs])
  have middleFrame : Frame base coverage mid.data :=
    frame.congr midMem (by rw [midRegs]) (by rw [midRegs]) (by rw [midRegs])
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0xfc⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0xfc⟩,mid,t.machine] =
      .ok [decision rxSection .findNodePrefixMatches (decide ((s.regs.get (.low .r15 .W8)).toNat ≤ (s.regs.get (.low .r14 .W8)).toNat)) t.machine] := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0xfc⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0xfc); unfold Quiet; decide)
    simp only [observeHistory,first]
    by_cases branch : (s.regs.get (.low .r15 .W8)).toNat ≤ (s.regs.get (.low .r14 .W8)).toNat
    all_goals simp [AllowedipsObservation.edge,midPC,pc,branch,choice,
      AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
    all_goals rfl
  have traced := Trace.of_path observed last _ rfl pathEq (by simp) nextFrame _ localObserved
    (by
      intro q member cut
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact frame.memory
      · exact middleFrame.memory
      · exact nextFrame.memory)
    (by
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq
      · subst q
        change AllowedipsImage.Lookup.entry+0xfc ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0xfc ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change mid.pc ≠ Image.PeerGet.entry+0xaf ∧ mid.pc ≠ Image.PeerGet.entry+0x4a
        rw [midPC]; constructor <;> decide)
  refine ⟨?_,regs,traced⟩
  simpa only [decide_eq_true_eq] using pc

#print axioms prefix_guard

theorem full_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xaf⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8) then AllowedipsImage.Lookup.entry+0x101
        else AllowedipsImage.Lookup.entry+0xb4) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history
        (events ++ [decision rxSection .findNodeFullLength (s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xaf⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.fullLength_history fetch agree s history)
  rintro t ⟨regs,memory,pc,mid,recorded,midPC,midRegs,midMem⟩
  have nextFrame : Frame base coverage t.machine.data :=
    frame.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs])
  have middleFrame : Frame base coverage mid.data :=
    frame.congr midMem (by rw [midRegs]) (by rw [midRegs]) (by rw [midRegs])
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0xaf⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0xaf⟩,mid,t.machine] =
      .ok [decision rxSection .findNodeFullLength (s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8)) t.machine] := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0xaf⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0xaf); unfold Quiet; decide)
    simp only [observeHistory,first]
    cases branch : s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8)
    all_goals simp [AllowedipsObservation.edge,midPC,pc,branch,choice,
      AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
    all_goals rfl
  have traced := Trace.of_path observed last _ rfl pathEq (by simp) nextFrame _ localObserved
    (by
      intro q member cut
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact frame.memory
      · exact middleFrame.memory
      · exact nextFrame.memory)
    (by
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq
      · subst q
        change AllowedipsImage.Lookup.entry+0xaf ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0xaf ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change mid.pc ≠ Image.PeerGet.entry+0xaf ∧ mid.pc ≠ Image.PeerGet.entry+0x4a
        rw [midPC]; constructor <;> decide)
  refine ⟨?_,regs,traced⟩
  simpa only [decide_eq_true_eq] using pc

#print axioms full_guard

theorem next_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xd0⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if s.regs.get (.low .rbx .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x101 else AllowedipsImage.Lookup.entry+0xd5) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history (events ++ [decision rxSection .findNodeNode
        (!(s.regs.get (.low .rbx .W64) == 0)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xd0⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.next_guard_history fetch agree s history)
  rintro t ⟨af,machine,recorded⟩
  let mid : MachineState := ⟨LookupHistory.tested (.low .rbx .W64) s af,AllowedipsImage.Lookup.entry+0xd3⟩
  have nextFrame : Frame base coverage t.machine.data := by
    rw [machine]
    exact frame.congr rfl rfl rfl rfl
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0xd0⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    rw [← machine] at recorded
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0xd0⟩,mid,t.machine] =
      .ok [decision rxSection .findNodeNode (!(s.regs.get (.low .rbx .W64) == 0)) t.machine] := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0xd0⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0xd0); unfold Quiet; decide)
    simp only [observeHistory,first]
    rw [machine]
    cases zero : s.regs.get (.low .rbx .W64) == 0
    all_goals simp [AllowedipsObservation.edge,mid,choice,
      AllowedipsImage.Lookup.entry]
    all_goals rfl
  have trace := Trace.of_path observed last _ rfl pathEq (by simp) nextFrame _ localObserved
    (by
      intro q member cut
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq | eq
      · subst q; exact frame.memory
      · subst q; exact frame.memory
      · subst q; exact nextFrame.memory)
    (by
      intro q member
      simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with eq | eq
      · subst q
        change AllowedipsImage.Lookup.entry+0xd0 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0xd0 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0xd3 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0xd3 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide)
  exact ⟨by rw [machine],by rw [machine]; rfl,trace⟩

#print axioms next_guard
end Binary.AllowedipsLoop
