import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionEpollRelease

/-! The native bounded wake/callback recursion retains suspended TX actors.
The proof follows the actual nesting fuel and does not assume empty wait queues. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

def WakeFrame (fuel : Nat) : Prop :=
  ∀ r mode nr flags key, Keeps (wakeUpCommonAt fuel r mode nr flags key)

def CallbackFrame (fuel : Nat) : Prop :=
  ∀ e mode flags key, Keeps (WaitEntry.callAt fuel e mode flags key)

theorem callbacks_of_wake (frame : WakeFrame fuel) : CallbackFrame fuel := by
  have safe (ep : EpId) (epi : Option EpiId) (flags : UInt32) :
      Keeps (epPollSafewakeAt fuel ep epi flags) := by
    unfold epPollSafewakeAt
    exact discard (frame _ _ _ _ _)
  have callback (id : PwqId) (mode flags : UInt32) (key : Option UInt32) :
      Keeps (epPollCallbackAt fuel id mode flags key) := by
    nested_suspension_source [epPollCallbackAt] using
      [get_pwq,get_epi,get_ep,set_ep,set_epi,compare,branch,invariant,unsupported,wait_active,safe]
  intro entry mode flags key
  nested_suspension_source [WaitEntry.callAt] using [callback]

theorem wake_family (fuel : Nat) : WakeFrame fuel ∧ CallbackFrame fuel := by
  induction fuel with
  | zero =>
    have walk : WakeFrame 0 := by
      intro r mode nr flags key
      nested_suspension_source [wakeUpCommonAt] using [wait_queue,invariant]
      all_goals omega
    exact ⟨walk,callbacks_of_wake walk⟩
  | succ fuel ih =>
    have walk : WakeFrame (fuel+1) := by
      have previous := ih.2
      intro r mode nr flags key
      nested_suspension_source [wakeUpCommonAt] using [wait_queue,invariant,previous]
      all_goals (simp_all only [Nat.add_one, Nat.succ.injEq]; exact previous _ _ _ _)
    exact ⟨walk,callbacks_of_wake walk⟩

theorem wake_common (r : WaitQueueRef) (mode : UInt32) (nr : Int) (flags : UInt32)
    (key : Option UInt32) : Keeps (wakeUpCommon r mode nr flags key) :=
  (wake_family WAKE_NEST_FUEL).1 _ _ _ _ _

theorem wake_locked (r : WaitQueueRef) (mode : UInt32) (nr : Int) (flags : UInt32)
    (key : Option UInt32) : Keeps (wakeUpCommonLock r mode nr flags key) := by
  nested_suspension_source [wakeUpCommonLock] using [wake_common]

theorem wake_base (r : WaitQueueRef) (mode : UInt32) (nr : Int)
    (key : Option UInt32) : Keeps (wakeUpBase r mode nr key) := wake_locked _ _ _ _ _

theorem wake_poll (r : WaitQueueRef) (mask : UInt32) : Keeps (wakeUpPoll r mask) :=
  discard (wake_base _ _ _ _)

theorem wake_interruptible_all (r : WaitQueueRef) : Keeps (wakeUpInterruptibleAll r) :=
  discard (wake_base _ _ _ _)

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
