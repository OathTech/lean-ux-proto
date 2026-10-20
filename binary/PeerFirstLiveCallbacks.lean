import PeerLiveCallbacksHistory
import PeerFirstLiveStages
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- All live suffix callbacks and four actual decisions. Nonzero old count
    is explicit because the folded dead decision reads the unchanged EBP. -/
theorem live_callbacks_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f4100) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (body : MachineData) (safe : CallStackSafe outer body.regs.rsp) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body)
    (success : body.regs.get (.low .r15 .W8) ≠ 0)
    (oldPositive : (body.regs.get (.low .rbp .W32)).msb = false)
    (newPositive : (body.regs.get (.low .r12 .W32)).msb = false)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x60⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ retry negative wrap dead : MachineState,
      t.machine.pc = Image.PeerGet.entry+0x9d ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧ t.machine.data.regs.rbp = body.regs.rbp ∧
      EqualOutside (scanWrites body coverage) body.dmem retry.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem negative.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem wrap.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem dead.data.dmem ∧
      StableTrace body coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false retry,
          LookupObservation.decision rxSection .refcountAddNzNegative false negative,
          LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead]) t)
      ⟨⟨body, Image.PeerGet.entry+0x60⟩, history⟩ := by
  have retry := live_retry_stage fetch agree tracePc traceCmp body body coverage preempt
    safe (ScanFrame.initial body coverage preempt ready) success comparison rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ retry
  rintro first ⟨retry, pc₁, bx₁, bp₁, retryFrame, trace₁⟩
  let events₁ := events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false retry]
  have oldPositive₁ : (first.machine.data.regs.get (.low .rbp .W32)).msb = false := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bp₁] using oldPositive
  have negative := live_negative_stage fetch agree tracePc traceCmp body first.machine.data coverage preempt
    safe trace₁.frame oldPositive₁ comparison rxSection first.history events₁ trace₁.observed (by rw [← pc₁]; exact trace₁.last)
  have cursor₁ : (⟨⟨first.machine.data, Image.PeerGet.entry+0x77⟩, first.history⟩ : Executed) = first := by rw [← pc₁]
  rw [cursor₁] at negative
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ negative
  rintro second ⟨negative, pc₂, bx₂, bp₂, negativeFrame, trace₂⟩
  let events₂ := events₁ ++ [LookupObservation.decision rxSection .refcountAddNzNegative false negative]
  have positive₂ : (second.machine.data.regs.get (.low .r12 .W32)).msb = false := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, trace₂.frame.query] using newPositive
  have nonzero₂ : second.machine.data.regs.get (.low .rbp .W32) ≠ 0 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bp₂, bp₁] using nonzero
  have wrap := live_wrap_stage fetch agree tracePc traceCmp body second.machine.data coverage preempt
    safe trace₂.frame positive₂ nonzero₂ comparison rxSection second.history events₂ trace₂.observed (by rw [← pc₂]; exact trace₂.last)
  have cursor₂ : (⟨⟨second.machine.data, Image.PeerGet.entry+0x8a⟩, second.history⟩ : Executed) = second := by rw [← pc₂]
  rw [cursor₂] at wrap
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ wrap
  rintro final ⟨wrap, dead, pc₃, bx₃, bp₃, wrapFrame, deadFrame, trace₃⟩
  refine ⟨retry, negative, wrap, dead, pc₃, bx₃.trans (bx₂.trans bx₁), bp₃.trans (bp₂.trans bp₁),
    retryFrame, negativeFrame, wrapFrame, deadFrame, ?_⟩
  simpa only [events₁, events₂, List.append_assoc, List.cons_append, List.nil_append] using
    trace₁.trans (trace₂.trans trace₃)

#print axioms live_callbacks_history
end Binary.PeerGet.First
