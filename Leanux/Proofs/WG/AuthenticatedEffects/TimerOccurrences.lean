import Leanux.Proofs.WG.AuthenticatedEffects.CausalSourceMetadata
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsReceipts

/-! Live timer provenance in the full joint journal. The projection retains
peer incarnation, expiry and the complete wheel entry, including enqueue stamp.
A native arm that does not change its slot keeps the existing occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerOccurrences
open Leanux Leanux.WG Leanux.Proofs.Logged

def Changed (r : TimerEffects.Arm Cause) : Prop :=
  TimerSlots.view r.run.before r.peer r.timer ≠ TimerSlots.view r.run.after r.peer r.timer

def Recorded (record : TimerEffects.Arm Cause → E) (h : List E) (r : TimerEffects.Arm Cause) : Prop :=
  ∃ pre post, h = pre ++ record r :: post ∧ r.Valid ∧ Changed r

def HasCause (record : TimerEffects.Arm Cause → E) (h : List E) (pid : PeerId)
    (timer : PeerTimer) (stamp : Nat) (expires : Option UInt64) (entry : WheelEntry) : Prop :=
  ∃ r, Recorded record h r ∧ r.peer = pid ∧ r.timer = timer ∧
    TimerSlots.Pending r.run.after pid timer stamp expires entry

def Carrier (record : TimerEffects.Arm Cause → E) (h : List E) (w : WGWorld) : Prop :=
  ∀ pid timer stamp expires entry, TimerSlots.Pending w pid timer stamp expires entry →
    HasCause record h pid timer stamp expires entry

variable {record : TimerEffects.Arm Cause → E} {h : List E} {w v : WGWorld}
  {r : TimerEffects.Arm Cause} {pid : PeerId} {timer : PeerTimer}
  {stamp : Nat} {expires : Option UInt64} {entry : WheelEntry}

theorem Recorded.append (recorded : Recorded record h r) (suffix : List E) :
    Recorded record (h ++ suffix) r := by
  obtain ⟨pre,post,position,native,changed⟩ := recorded
  exact ⟨pre,post ++ suffix,by simp [position,List.append_assoc],native,changed⟩

theorem HasCause.append (cause : HasCause record h pid timer stamp expires entry) (suffix : List E) :
    HasCause record (h ++ suffix) pid timer stamp expires entry := by
  obtain ⟨r,recorded,peer,kind,pending⟩ := cause
  exact ⟨r,recorded.append suffix,peer,kind,pending⟩

theorem Carrier.append (carrier : Carrier record h w) (suffix : List E) : Carrier record (h ++ suffix) w :=
  fun _ _ _ _ _ pending => (carrier _ _ _ _ _ pending).append suffix

theorem Carrier.empty_device (w : WGWorld) (absent : w.dev = none) : Carrier record [] w := by
  intro pid timer stamp expires entry pending
  simp [TimerSlots.Pending,TimerSlots.view,absent] at pending

theorem Carrier.frame (carrier : Carrier record h w) (same : TimerSlots.view v = TimerSlots.view w) :
    Carrier record h v := by
  intro pid timer stamp expires entry pending
  exact carrier pid timer stamp expires entry (by simpa only [TimerSlots.Pending,same] using pending)

theorem Carrier.arm (r : TimerEffects.Arm Cause) (carrier : Carrier record h r.run.before) (native : r.Valid) :
    Carrier record (h ++ [record r]) r.run.after := by
  intro pid timer stamp expires entry pending
  by_cases target : pid = r.peer ∧ timer = r.timer
  · rcases target with ⟨rfl,rfl⟩
    by_cases changed : Changed r
    · exact ⟨r,⟨h,[],rfl,native,changed⟩,rfl,rfl,pending⟩
    · have same : TimerSlots.view r.run.before r.peer r.timer = TimerSlots.view r.run.after r.peer r.timer :=
        Classical.not_not.mp changed
      exact (carrier _ _ _ _ _ (by simpa only [TimerSlots.Pending,same] using pending)).append [record r]
  · have same := TimerSlots.armTimer_other r.peer r.timer r.delay r.caller r.run.before r.run.after
      r.run.ambientBefore r.run.ambientAfter (by cases r.run.value; exact native) pid timer target
    exact (carrier _ _ _ _ _ (by simpa only [TimerSlots.Pending,same] using pending)).append [record r]

theorem Carrier.delete (pid : PeerId) (timer : PeerTimer) (w v : WGWorld) (a b : Ambient)
    (carrier : Carrier record h w) (run : ((delTimer pid timer).run w).run a = .ok (((),v),b)) :
    Carrier record h v := by
  intro q t stamp expires entry pending
  by_cases target : q = pid ∧ t = timer
  · rcases target with ⟨peer,kind⟩
    subst q
    subst t
    exact False.elim (TimerSlots.delTimer_no_wheel pid timer w v a b run stamp expires entry pending)
  · have same := TimerSlots.delTimer_other pid timer w v a b run q t target
    exact carrier q t stamp expires entry (by simpa only [TimerSlots.Pending,same] using pending)

theorem receipt_preserves (record : TimerEffects.Arm Cause → E) (cause : Cause) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StatePrefixPreserves (fun h w _ => Carrier record h w) (fun _ => True)
      (TimerEffects.armReceipt record cause pid timer delay caller) := by
  intro w ambient h hi
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix (armTimer pid timer delay caller))
    (fun r => record ⟨cause,pid,timer,delay,caller,r⟩) w ambient h
  simp only [runWGPrefix_lift] at observed
  change runWGPrefix (TimerEffects.armReceipt record cause pid timer delay caller) w ambient h = _ at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : ((armTimer pid timer delay caller).run w).run ambient with
  | error err => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    cases result
    let receipt : TimerEffects.Arm Cause := ⟨cause,pid,timer,delay,caller,⟨(),w,v,ambient,b⟩⟩
    exact ⟨[record receipt],rfl,True.intro,Carrier.arm receipt hi run⟩

/-- The real selector retrieves the cause of its exact live wheel occurrence.
This remains conditional on the live carrier until the common driver closes it. -/
theorem selected_cause (r : TimerDispatch.Selection) (valid : r.Valid)
    (carrier : Carrier record h r.before.wg) :
    ∃ stamp expires, HasCause record h r.peer r.timer stamp expires r.entry := by
  obtain ⟨p,resident,wheel⟩ := TimerSlots.due_resident r.saved r.bound r.peer r.timer r.entry
    (TimerSlots.nextDue_member r.saved r.bound r.peer r.timer r.entry valid.2)
  apply Exists.intro p.internalId
  apply Exists.intro (p.timer r.timer)
  apply carrier
  simp [TimerSlots.Pending,TimerSlots.view,valid.1,resident,wheel]

end Leanux.Proofs.WG.AuthenticatedEffects.TimerOccurrences
