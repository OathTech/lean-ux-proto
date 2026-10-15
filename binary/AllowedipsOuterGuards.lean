import AllowedipsLoopGuards

namespace Binary.AllowedipsLoop
open TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

def rootPoints (rxSection : Nat) (zero : Bool) (t : MachineState) : List Point :=
  [decision rxSection .findNodeNode (!zero) t] ++
    if zero then [decision rxSection .lookupFound false t] else []

theorem root_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x7e⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if s.regs.get (.low .rbx .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x184 else AllowedipsImage.Lookup.entry+0x87) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history (events ++ (rootPoints rxSection (s.regs.get (.low .rbx .W64) == 0) t.machine)) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x7e⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.root_guard_history fetch agree s history)
  rintro t ⟨af,machine,recorded⟩
  let mid : MachineState := ⟨LookupHistory.tested (.low .rbx .W64) s af,AllowedipsImage.Lookup.entry+0x81⟩
  have nextFrame : Frame base coverage t.machine.data := by
    rw [machine]
    exact frame.congr rfl rfl rfl rfl
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0x7e⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    rw [← machine] at recorded
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0x7e⟩,mid,t.machine] =
      .ok (rootPoints rxSection (s.regs.get (.low .rbx .W64) == 0) t.machine) := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x7e⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0x7e); unfold Quiet; decide)
    simp only [observeHistory,first]
    rw [machine]
    cases zero : s.regs.get (.low .rbx .W64) == 0
    all_goals simp [AllowedipsObservation.edge,mid,zero,choice,rootPoints,
      AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
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
        change AllowedipsImage.Lookup.entry+0x7e ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x7e ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0x81 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x81 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide)
  exact ⟨by rw [machine],by rw [machine]; rfl,trace⟩

theorem found_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x106⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if s.regs.get (.low .rbp .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x184 else AllowedipsImage.Lookup.entry+0x10b) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history (events ++ [decision rxSection .lookupFound
        (!(s.regs.get (.low .rbp .W64) == 0)) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x106⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.found_guard_history fetch agree s history)
  rintro t ⟨af,machine,recorded⟩
  let mid : MachineState := ⟨LookupHistory.tested (.low .rbp .W64) s af,AllowedipsImage.Lookup.entry+0x109⟩
  have nextFrame : Frame base coverage t.machine.data := by
    rw [machine]
    exact frame.congr rfl rfl rfl rfl
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0x106⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    rw [← machine] at recorded
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0x106⟩,mid,t.machine] =
      .ok [decision rxSection .lookupFound (!(s.regs.get (.low .rbp .W64) == 0)) t.machine] := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x106⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0x106); unfold Quiet; decide)
    simp only [observeHistory,first]
    rw [machine]
    cases zero : s.regs.get (.low .rbp .W64) == 0
    all_goals simp [AllowedipsObservation.edge,mid,zero,choice,
      AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
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
        change AllowedipsImage.Lookup.entry+0x106 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x106 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0x109 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x109 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide)
  exact ⟨by rw [machine],by rw [machine]; rfl,trace⟩

theorem peer_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x119⟩) :
    historySteps fetch 2 (fun t =>
      t.machine.pc = (if s.regs.get (.low .rax .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x74 else AllowedipsImage.Lookup.entry+0x122) ∧
      t.machine.data.regs = s.regs ∧
      Trace base coverage rxSection history (events ++ [decision rxSection .lookupPeerGone
        (s.regs.get (.low .rax .W64) == 0) t.machine]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x119⟩,history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (Allowedips.peer_guard_history fetch agree s history)
  rintro t ⟨af,machine,recorded⟩
  let mid : MachineState := ⟨LookupHistory.tested (.low .rax .W64) s af,AllowedipsImage.Lookup.entry+0x11c⟩
  have nextFrame : Frame base coverage t.machine.data := by
    rw [machine]
    exact frame.congr rfl rfl rfl rfl
  have pathEq : t.history = history.dropLast ++ [⟨s,AllowedipsImage.Lookup.entry+0x119⟩,mid,t.machine] := by
    have restored := congrArg (fun h => h ++ [mid,t.machine]) (history_restore last)
    rw [← machine] at recorded
    exact recorded.trans (by simpa only [List.append_assoc,List.singleton_append] using restored.symm)
  have localObserved : observeHistory (AllowedipsObservation.edge rxSection)
      [⟨s,AllowedipsImage.Lookup.entry+0x119⟩,mid,t.machine] =
      .ok [decision rxSection .lookupPeerGone (s.regs.get (.low .rax .W64) == 0) t.machine] := by
    have first := quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x119⟩ mid
      (by change Quiet (AllowedipsImage.Lookup.entry+0x119); unfold Quiet; decide)
    simp only [observeHistory,first]
    rw [machine]
    cases zero : s.regs.get (.low .rax .W64) == 0
    all_goals simp [AllowedipsObservation.edge,mid,zero,choice,
      AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
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
        change AllowedipsImage.Lookup.entry+0x119 ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x119 ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide
      · subst q
        change AllowedipsImage.Lookup.entry+0x11c ≠ Image.PeerGet.entry+0xaf ∧
          AllowedipsImage.Lookup.entry+0x11c ≠ Image.PeerGet.entry+0x4a
        constructor <;> decide)
  exact ⟨by rw [machine],by rw [machine]; rfl,trace⟩

#print axioms root_guard
#print axioms found_guard
#print axioms peer_guard
end Binary.AllowedipsLoop
