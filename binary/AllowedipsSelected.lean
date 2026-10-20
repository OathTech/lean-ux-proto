import AllowedipsRoot

namespace Binary.AllowedipsOuter
open TrustBase AllowedipsLoop LookupObservation
local instance : Labels := Image.linkedLabels

theorem selected_branch (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x106⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.data.regs.rbp=s.regs.rbp ∧
      t.machine.pc=(if s.regs.get (.low .rbp .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x184 else AllowedipsImage.Lookup.entry+0x110) ∧
      ∃ guard, Trace base coverage rxSection history
        (events ++ [decision rxSection .lookupFound (!(s.regs.get (.low .rbp .W64) == 0)) guard]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x106⟩,history⟩ := by
  have first := historySteps_eventually fetch 2 _ _
    (found_guard fetch agree base s coverage frame rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro guard ⟨pc,regs,trace⟩
  cases zero : s.regs.get (.low .rbp .W64) == 0 with
  | true =>
    apply Eventually.done
    exact ⟨by rw [regs],pc.trans (ite_eq_left zero),guard.machine,by simpa only [zero] using trace⟩
  | false =>
    have pc10b : guard.machine.pc=AllowedipsImage.Lookup.entry+0x10b := pc.trans (ite_eq_right (by rw [zero]; decide))
    have called := AllowedipsLoop.call fetch (AllowedipsImage.Lookup.entry+0x10b) "L_ffffffff810f31f0"
      (agree _ _ (by rfl)) .pc contract base guard.machine.data coverage trace.frame rxSection
      guard.history _ trace.observed (by simpa only [←pc10b] using trace.last)
      (by unfold Quiet; decide) (by decide)
    have cursor : (⟨⟨guard.machine.data,AllowedipsImage.Lookup.entry+0x10b⟩,guard.history⟩ : Executed)=guard := by rw [←pc10b]
    rw [cursor] at called
    apply eventually_weaken (historyStep fetch) _ _ _ _ called
    rintro final ⟨pc110,bx,bp,r14,r15,callTrace⟩
    exact ⟨bp.trans (by rw [regs]),pc110,guard.machine,by simpa only [zero] using trace.trans callTrace⟩

theorem selected_start (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsTracePcContract fetch)
    (base s : MachineData) (coverage : CommonBitsCoverage.Context)
    (frame : Frame base coverage s) (rxSection : Nat)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0x101⟩) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.data.regs.rbp=s.regs.rbp ∧
      t.machine.pc=(if s.regs.get (.low .rbp .W64) == 0 then
        AllowedipsImage.Lookup.entry+0x184 else AllowedipsImage.Lookup.entry+0x110) ∧
      ∃ guard, Trace base coverage rxSection history
        (events ++ [decision rxSection .lookupFound (!(s.regs.get (.low .rbp .W64) == 0)) guard]) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x101⟩,history⟩ := by
  have called := AllowedipsLoop.call fetch (AllowedipsImage.Lookup.entry+0x101) "L_ffffffff810f31f0"
    (agree _ _ (by rfl)) .pc contract base s coverage frame rxSection history events observed last
    (by unfold Quiet; decide) (by decide)
  apply eventually_trans (historyStep fetch) _ _ _ called
  rintro afterCall ⟨pc106,bx,bp,r14,r15,callTrace⟩
  change afterCall.machine.pc=AllowedipsImage.Lookup.entry+0x106 at pc106
  have next := selected_branch fetch agree contract base afterCall.machine.data coverage callTrace.frame
    rxSection afterCall.history events callTrace.observed (by simpa only [←pc106] using callTrace.last)
  have cursor : (⟨⟨afterCall.machine.data,AllowedipsImage.Lookup.entry+0x106⟩,afterCall.history⟩ : Executed)=afterCall := by rw [←pc106]
  rw [cursor] at next
  apply eventually_weaken (historyStep fetch) _ _ _ _ next
  rintro final ⟨result,pc,guard,trace⟩
  have equal : afterCall.machine.data.regs.get (.low .rbp .W64)=s.regs.get (.low .rbp .W64) := by
    simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,bp]
  exact ⟨result.trans bp,by simpa only [equal] using pc,guard,
    by simpa only [equal] using callTrace.trans trace⟩

#print axioms selected_branch
#print axioms selected_start
end Binary.AllowedipsOuter
