import Leanux.Proofs.WG.AuthenticatedEffects.CausalContextOrigins

/-! Delayed lexical contexts point strictly backward to the exact native
arm/enqueue occurrence and its recorded context. No recursion can manufacture
a root by cycling through a repeated peer identifier or timer slot. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ContextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

theorem timer_parent (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (index : Nat) (bound : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ suffix)
    (current : CausalScope.current scope? history = .ok (some ⟨index,.timer bound pid timer entry⟩)) :
    ∃ before after arm stamp expires,
      history = before ++ Event.armed arm :: after ∧ before.length < history.length ∧
      arm.Valid ∧ TimerOccurrences.Changed arm ∧ arm.peer = pid ∧ arm.timer = timer ∧
      TimerSlots.Pending arm.run.after pid timer stamp expires entry ∧
      arm.cause = CausalScope.current scope? before := by
  obtain ⟨scopeBefore,scopeAfter,scopePosition,origin⟩ :=
    current_timer trace placeholders history suffix index bound pid timer entry position current
  obtain ⟨selectedBefore,selection,selectedPosition,_,peer,kind,wheel,_,stamp,expires,_,
    arm,recorded,armPeer,armTimer,pending⟩ := origin
  obtain ⟨before,after,armPosition,native,changed⟩ := recorded
  let tail := after ++ [Event.old (.timerSelected selection)] ++
    Event.scope (.entered ⟨index,.timer bound pid timer entry⟩) :: scopeAfter
  have earlier : history = before ++ Event.armed arm :: tail := by
    simp only [tail,scopePosition,selectedPosition,armPosition,List.append_assoc,List.cons_append]
  have nativeContext := Receipts.initialized_arm trace placeholders before (tail ++ suffix) arm (by
    simp only [position,earlier,List.append_assoc,List.cons_append])
  refine ⟨before,tail,arm,stamp,expires,earlier,?_,native,changed,armPeer.trans peer,
    armTimer.trans kind,?_,nativeContext.2⟩
  · rw [earlier]
    simp only [List.length_append,List.length_cons]
    omega
  · simpa only [peer,kind,wheel] using pending

theorem work_parent (trace : Runner.Trace) (placeholders : Bool)
    (history suffix : List Event) (index : Nat) (pid : PeerId) (entry : CausalSources.SendEntry)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = history ++ suffix)
    (current : CausalScope.current scope? history = .ok (some ⟨index,.sendWork pid entry⟩)) :
    ∃ before after receipt,
      history = before ++ Event.queued receipt :: after ∧ before.length < history.length ∧
      receipt.Valid ∧ receipt.peer = pid ∧
      receipt.cause = CausalScope.current scope? before := by
  obtain ⟨scopeBefore,scopeAfter,scopePosition,origin⟩ :=
    current_work trace placeholders history suffix index pid entry position current
  obtain ⟨ticket,_,before,after,_,_,peer,_,recorded,_,native⟩ := origin.receipt
  let tail := after ++ Event.scope (.entered ⟨index,.sendWork pid entry⟩) :: scopeAfter
  have earlier : history = before ++ Event.queued ticket.receipt :: tail := by
    simp only [tail,scopePosition,recorded,List.append_assoc,List.cons_append]
  have nativeContext := Receipts.initialized_queue trace placeholders before (tail ++ suffix) ticket.receipt (by
    simp only [position,earlier,List.append_assoc,List.cons_append])
  refine ⟨before,tail,ticket.receipt,earlier,?_,native,peer,nativeContext.2⟩
  rw [earlier]
  simp only [List.length_append,List.length_cons]
  omega

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ContextOrigins
