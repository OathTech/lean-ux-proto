import Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffectFrames

/-! Both delayed-effect carriers concern the same actual state and journal.
Native cross-frames retain the other carrier when one kind of receipt is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

variable {E Cause : Type}

def Inv (arm : TimerEffects.Arm Cause → E) (queue : TimerEffects.Queued Cause → E)
    (h : List E) (w : WGWorld) : Prop :=
  TimerOccurrences.Carrier arm h w ∧ QueuedOccurrences.Inv queue h w

theorem Inv.append (hi : Inv arm queue h w) (suffix : List E) : Inv arm queue (h ++ suffix) w := by
  obtain ⟨timers,tickets,work⟩ := hi
  exact ⟨timers.append suffix,tickets,work.append suffix⟩

theorem Inv.empty_device (arm : TimerEffects.Arm Cause → E) (queue : TimerEffects.Queued Cause → E)
    (w : WGWorld) (absent : w.dev = none) : Inv arm queue [] w :=
  ⟨TimerOccurrences.Carrier.empty_device w absent,[],QueuedOccurrences.Carrier.empty w (by simp [QueuedOccurrences.queue,absent])⟩

private theorem state_combine (g : WGPrefix E α) (P Q : List E → WGWorld → Prop)
    (hp : StatePrefixPreserves (fun h w _ => P h w) (fun _ => True) g)
    (hq : StatePrefixPreserves (fun h w _ => Q h w) (fun _ => True) g) :
    StatePrefixPreserves (fun h w _ => P h w ∧ Q h w) (fun _ => True) g := by
  intro w a h hi
  obtain ⟨suffix,appended,safe,post⟩ := hp w a h hi.1
  obtain ⟨_,_,_,other⟩ := hq w a h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    simp only [run] at post other
    exact ⟨post,other⟩

private theorem observed_frame (P : List E → WGWorld → Prop) (g : WGPrefix E α) (native : WG.M α)
    (erases : ErasesStatePrefix g native) (appends : StateAppends g)
    (extend : ∀ h w, P h w → ∀ suffix, P (h ++ suffix) w)
    (frame : ∀ h, Preserves (P h) native) :
    StatePrefixPreserves (fun h w _ => P h w) (fun _ => True) g := by
  intro w a h hi
  obtain ⟨suffix,append⟩ := appends w a h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have original := (erases w a h).symm.trans run
    have kept := (hoare_iff_run_ambient _ _ _).mp (frame h) w a value v b hi original
    rw [append]
    exact extend h v kept suffix

theorem arm_preserves (arm : TimerEffects.Arm Cause → E) (queue : TimerEffects.Queued Cause → E)
    (cause : Cause) (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (TimerEffects.armReceipt arm cause pid timer delay caller) := by
  apply state_combine
  · exact TimerOccurrences.receipt_preserves arm cause pid timer delay caller
  · apply observed_frame _ _ (armTimer pid timer delay caller)
      (receiptWGObserved_erases (erasesStatePrefix_lift _) _) (by
        exact (StateAppends.lift _).receiptWGObserved _)
    · intro h w hi suffix
      obtain ⟨tickets,carrier⟩ := hi
      exact ⟨tickets,carrier.append suffix⟩
    · intro h
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a value v b hi run
      obtain ⟨tickets,carrier⟩ := hi
      exact ⟨tickets,carrier.frame ((ProjectedAction.iff_run_ambient _ _ _).mp
        (queue_of_frame (arm_queue pid timer delay caller)) w a value v b run)⟩

theorem queue_preserves (arm : TimerEffects.Arm Cause → E) (queue : TimerEffects.Queued Cause → E)
    (cause : Cause) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (TimerEffects.queueReceipt queue cause pid) := by
  apply state_combine
  · apply observed_frame _ _ (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
      (receiptWGObserved_erases (erasesStatePrefix_lift _) _) (by
        exact (StateAppends.lift _).receiptWGObserved _)
    · intro h w hi suffix
      exact hi.append suffix
    · intro h
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a value v b hi run
      exact hi.frame ((ProjectedAction.iff_run_ambient _ _ _).mp (queue_edit_timers (· ++ [pid]))
        w a value v b run)
  · exact QueuedOccurrences.receipt_preserves queue cause pid

theorem delete_preserves (arm : TimerEffects.Arm Cause → E) (queue : TimerEffects.Queued Cause → E)
    (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (liftWGPrefix (delTimer pid timer)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
  intro h w a value v b hi run
  cases value
  obtain ⟨timers,tickets,work⟩ := hi
  exact ⟨timers.delete pid timer w v a b run,tickets,work.frame
    ((ProjectedAction.iff_run_ambient _ _ _).mp (queue_of_frame (delete_queue pid timer)) w a () v b run)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
