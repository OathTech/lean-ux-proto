import PeerLiveZeroHistory
import PeerFirstLiveGuards
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- The nonzero guard and its real PC callback preserve the count address
    and frame memory outside callback writes, before any increment. The
    enclosing caller must separate the count word from those writes.
    Comparison operands are actual EBP. -/
theorem live_zero_call_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (body : MachineData) (safe : CallStackSafe outer body.regs.rsp) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body) (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine.pc = Image.PeerGet.entry+0x44 ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      StableTrace body coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzZero false
          ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x3f⟩
          (some ((body.regs.get (.low .rbp .W32)).toNat, 0))]) t)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  have guard := nonzero_guard_trace fetch agree body body coverage preempt safe (ScanFrame.initial body coverage preempt ready)
      nonzero rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ guard
  rintro guarded ⟨af, machine, trace⟩
  have pc : guarded.machine.pc = Image.PeerGet.entry+0x3f := congrArg MachineState.pc machine
  have call := scan_call_cursor fetch "L_ffffffff810f31f0" guarded
    (by rw [pc]; exact agree _ _ (by rfl)) .pc tracePc body coverage preempt safe trace.frame (trace.frame).ready.pc_allowed
    rxSection _ trace.observed trace.last (by
      simp [LookupObservation.edge, pc, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro t ⟨pc₂, bx₂, bp₂, trace₂⟩
  refine ⟨af, by rw [pc₂, pc]; rfl, ?_, ?_, ?_⟩
  · simpa only [machine, tested] using bx₂
  · simpa only [machine, tested] using bp₂
  · simpa only [machine] using trace.trans trace₂

#print axioms live_zero_call_history
end Binary.PeerGet.First
