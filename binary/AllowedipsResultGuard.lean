import AllowedipsHistory
import CommonBitsGuardTrace
import AllowedipsLoopObservation

namespace Binary.Allowedips
open TrustBase CommonBits LookupObservation
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 8192

theorem result_guard (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (s : MachineData) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc = (if s.regs.get (.low .rax .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x74 else AllowedipsImage.Lookup.entry+0x122) ∧
       t.machine.data.regs=s.regs ∧ t.machine.data.dmem=s.dmem) ∧
      Local (fun _ => False) ⟨s,AllowedipsImage.Lookup.entry+0x119⟩ rxSection
        [decisionView rxSection .lookupPeerGone (s.regs.get (.low .rax .W64) == 0)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x119⟩,[⟨s,AllowedipsImage.Lookup.entry+0x119⟩]⟩ := by
  have run := historySteps_eventually fetch 2 _ _ (peer_guard_history fetch agree s
    [⟨s,AllowedipsImage.Lookup.entry+0x119⟩])
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨af,machine,recorded⟩
  let mid : MachineState := ⟨LookupHistory.tested (.low .rax .W64) s af,AllowedipsImage.Lookup.entry+0x11c⟩
  have memory : t.machine.data.dmem=s.dmem := by rw [machine]; rfl
  have exactPath : t.history=[⟨s,AllowedipsImage.Lookup.entry+0x119⟩,mid,t.machine] := by
    rw [←machine] at recorded
    exact recorded
  refine ⟨⟨by rw [machine],by rw [machine]; rfl,memory⟩,?_⟩
  refine ⟨by rw [exactPath]; rfl,by rw [exactPath]; rfl,?_,?_,?_,?_⟩
  · refine ⟨[decision rxSection .lookupPeerGone (s.regs.get (.low .rax .W64) == 0) t.machine],?_,?_⟩
    · rw [exactPath]
      have first := AllowedipsLoop.quiet_edge rxSection ⟨s,AllowedipsImage.Lookup.entry+0x119⟩ mid
        (by change AllowedipsLoop.Quiet (AllowedipsImage.Lookup.entry+0x119); unfold AllowedipsLoop.Quiet; decide)
      simp only [observeHistory,first]
      rw [machine]
      cases zero : s.regs.get (.low .rax .W64) == 0
      all_goals simp [AllowedipsObservation.edge,mid,zero,choice,
        AllowedipsImage.Lookup.entry,AllowedipsImage.CommonBits.entry]
      all_goals rfl
    · rfl
  · rw [memory]; intro _ _; rfl
  · intro q member cut
    rw [exactPath] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · intro _ _; rfl
    · intro _ _; rfl
    · rw [memory]; intro _ _; rfl
  · intro q member
    rw [exactPath] at member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change AllowedipsImage.Lookup.entry+0x119 ≠ Image.PeerGet.entry+0xaf ∧
        AllowedipsImage.Lookup.entry+0x119 ≠ Image.PeerGet.entry+0x4a
      decide
    · change AllowedipsImage.Lookup.entry+0x11c ≠ Image.PeerGet.entry+0xaf ∧
        AllowedipsImage.Lookup.entry+0x11c ≠ Image.PeerGet.entry+0x4a
      decide

#print axioms result_guard
end Binary.Allowedips
