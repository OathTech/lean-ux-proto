import Leanux.Proofs.WG.AuthenticatedEffects.TimerSlotFrames

/-! Store provenance for live wheel occurrences. The carrier remembers the
peer incarnation, exact expiry and complete wheel entry, including enqueue
stamp. A no-change arm retains its existing cause. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def Pending (w : WGWorld) (pid : PeerId) (timer : PeerTimer)
    (stamp : Nat) (expires : Option UInt64) (entry : WheelEntry) : Prop :=
  view w pid timer = some (stamp,expires,some entry)

def Changed (r : TimerRoot.Arm) : Prop :=
  view r.run.before r.peer r.timer ≠ view r.run.after r.peer r.timer

def Recorded (h : List TimerRoot.Event) (r : TimerRoot.Arm) : Prop :=
  ∃ pre post, h = pre ++ .armed r :: post ∧ r.Native ∧ Changed r

def HasCause (h : List TimerRoot.Event) (pid : PeerId) (timer : PeerTimer)
    (stamp : Nat) (expires : Option UInt64) (entry : WheelEntry) : Prop :=
  ∃ r, Recorded h r ∧ r.peer = pid ∧ r.timer = timer ∧
    Pending r.run.after pid timer stamp expires entry

def Carrier (h : List TimerRoot.Event) (w : WGWorld) : Prop :=
  ∀ pid timer stamp expires entry, Pending w pid timer stamp expires entry →
    HasCause h pid timer stamp expires entry

theorem Recorded.append (recorded : Recorded h r) (suffix : List TimerRoot.Event) :
    Recorded (h ++ suffix) r := by
  obtain ⟨pre,post,position,native,changed⟩ := recorded
  exact ⟨pre,post ++ suffix,by simp [position,List.append_assoc],native,changed⟩

theorem HasCause.append (cause : HasCause h pid timer stamp expires entry) (suffix : List TimerRoot.Event) :
    HasCause (h ++ suffix) pid timer stamp expires entry := by
  obtain ⟨r,recorded,peer,kind,pending⟩ := cause
  exact ⟨r,recorded.append suffix,peer,kind,pending⟩

theorem Carrier.append (carrier : Carrier h w) (suffix : List TimerRoot.Event) : Carrier (h ++ suffix) w :=
  fun _ _ _ _ _ pending => (carrier _ _ _ _ _ pending).append suffix

theorem Carrier.empty_device (w : WGWorld) (absent : w.dev = none) : Carrier [] w := by
  intro pid timer stamp expires entry pending
  simp [Pending,view,absent] at pending

theorem Carrier.frame (carrier : Carrier h w) (same : view v = view w) : Carrier h v := by
  intro pid timer stamp expires entry pending
  exact carrier pid timer stamp expires entry (by simpa only [Pending,same] using pending)

/-- The new token is used only if this native arm changed the target slot.
All other timer occurrences retain their previous recorded causes. -/
theorem Carrier.arm (r : TimerRoot.Arm) (carrier : Carrier h r.run.before) (native : r.Native) :
    Carrier (h ++ [.armed r]) r.run.after := by
  intro pid timer stamp expires entry pending
  by_cases target : pid = r.peer ∧ timer = r.timer
  · rcases target with ⟨rfl,rfl⟩
    by_cases changed : Changed r
    · exact ⟨r,⟨h,[],rfl,native,changed⟩,rfl,rfl,pending⟩
    · have same : view r.run.before r.peer r.timer = view r.run.after r.peer r.timer :=
        Classical.not_not.mp changed
      exact (carrier _ _ _ _ _ (by simpa only [Pending,same] using pending)).append [.armed r]
  · have same := armTimer_other r.peer r.timer r.delay r.caller r.run.before r.run.after
      r.run.ambientBefore r.run.ambientAfter (by cases r.run.value; exact native) pid timer target
    exact (carrier _ _ _ _ _ (by simpa only [Pending,same] using pending)).append [.armed r]

theorem Carrier.delete (pid : PeerId) (timer : PeerTimer) (w v : WGWorld) (a b : Ambient)
    (carrier : Carrier h w) (run : ((delTimer pid timer).run w).run a = .ok (((),v),b)) : Carrier h v := by
  intro q t stamp expires entry pending
  by_cases target : q = pid ∧ t = timer
  · rcases target with ⟨peer,kind⟩
    subst q
    subst t
    exact False.elim (delTimer_no_wheel pid timer w v a b run stamp expires entry pending)
  · have same := delTimer_other pid timer w v a b run q t target
    exact carrier q t stamp expires entry (by simpa only [Pending,same] using pending)

theorem arm_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StatePrefixPreserves (fun h w _ => Carrier h w) (fun _ => True)
      (TimerRoot.arm origin kind pid timer delay caller) := by
  intro w ambient h hi
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix (armTimer pid timer delay caller))
    (fun r => TimerRoot.Event.armed ⟨origin,kind,pid,timer,delay,caller,r⟩) w ambient h
  simp only [runWGPrefix_lift] at observed
  change runWGPrefix (TimerRoot.arm origin kind pid timer delay caller) w ambient h = _ at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : ((armTimer pid timer delay caller).run w).run ambient with
  | error err => exact ⟨[],by simp,True.intro,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    cases result
    let receipt : TimerRoot.Arm := ⟨origin,kind,pid,timer,delay,caller,⟨(),w,v,ambient,b⟩⟩
    exact ⟨[.armed receipt],rfl,True.intro,Carrier.arm receipt hi run⟩

theorem delete_preserves (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h w _ => Carrier h w) (fun _ => True)
      (liftWGPrefix (delTimer pid timer) : WGPrefix TimerRoot.Event Unit) :=
  StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
    (fun _ _ _ result _ _ hi run => by cases result; exact Carrier.delete pid timer _ _ _ _ hi run)

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
