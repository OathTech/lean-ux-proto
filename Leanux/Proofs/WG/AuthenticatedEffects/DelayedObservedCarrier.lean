import Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffectCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.TimerRetentionFrames

/-! Delayed-effect carriers around an already observed native callback. The
callback's retained old receipts and its new causal receipt belong to one run;
native erasure supplies only the state endpoints of that very callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

variable {E Cause : Type} {arm : TimerEffects.Arm Cause → E} {queue : TimerEffects.Queued Cause → E}

theorem Inv.arm_record (r : TimerEffects.Arm Cause) (hi : Inv arm queue h r.run.before) (valid : r.Valid) :
    Inv arm queue (h ++ [arm r]) r.run.after := by
  obtain ⟨timers,tickets,work⟩ := hi
  exact ⟨timers.arm r valid,tickets,(work.frame
    ((ProjectedAction.iff_run_ambient _ _ _).mp (queue_of_frame (arm_queue r.peer r.timer r.delay r.caller))
      r.run.before r.run.ambientBefore r.run.value r.run.after r.run.ambientAfter valid)).append _⟩

theorem Inv.queue_record (r : TimerEffects.Queued Cause) (hi : Inv arm queue h r.run.before) (valid : r.Valid) :
    Inv arm queue (h ++ [queue r]) r.run.after := by
  obtain ⟨timers,tickets,work⟩ := hi
  refine ⟨(timers.frame ((ProjectedAction.iff_run_ambient _ _ _).mp (queue_edit_timers (· ++ [r.peer]))
    r.run.before r.run.ambientBefore r.run.value r.run.after r.run.ambientAfter valid)).append _,?_⟩
  by_cases device : r.run.before.dev.isSome
  · exact ⟨tickets ++ [⟨h.length,r⟩],work.enqueue r valid device⟩
  · have before : r.run.before.dev = none := by
      cases hd : r.run.before.dev with
      | none => rfl
      | some d => simp [hd] at device
    have after : r.run.after.dev = none := by
      simpa only [before,Option.map_none] using QueuedOccurrences.native_append r valid
    exact ⟨tickets,(work.append [queue r]).frame (by simp only [QueuedOccurrences.queue,before,after])⟩

theorem Inv.retained (hi : Inv arm queue h w)
    (timers : TimerSlots.Retained (TimerSlots.view w) v)
    (work : QueuedOccurrences.queue v = QueuedOccurrences.queue w) : Inv arm queue h v := by
  obtain ⟨carrier,tickets,queueCarrier⟩ := hi
  exact ⟨fun pid timer stamp expires entry pending => carrier pid timer stamp expires entry
    (timers pid timer _ pending),tickets,queueCarrier.frame work⟩

theorem native_retained (action : WG.M α)
    (timers : ∀ initial, Preserves (TimerSlots.Retained initial) action)
    (work : SameView QueuedOccurrences.queue action) (h : List E) :
    Preserves (Inv arm queue h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  exact hi.retained
    ((hoare_iff_run_ambient _ _ _).mp (timers (TimerSlots.view w)) w a value v b
      (TimerSlots.retained_refl w) run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp work w a value v b run)

/-- A successful callback's newly recorded state transition updates the carrier
after its actual retained prefix. No independently produced history is used. -/
theorem receipt_update (body : WGPrefix E α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (record : WGRunWitness α → E)
    (update : ∀ h r, r.Valid native → Inv arm queue h r.before →
      Inv arm queue (h ++ [record r]) r.after) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (receiptWGObserved body record) := by
  intro w a h hi
  obtain ⟨suffix,grown⟩ := appends w a h
  have observed := runWGPrefix_receiptWGObserved body record w a h
  simp only [runWGPrefix,runStatePrefix] at observed
  rw [observed]
  cases run : runPrefix (body.run w) a h with
  | mk result history =>
    rw [run] at grown
    change history = h ++ suffix at grown
    cases result with
    | error stop => exact ⟨suffix,grown,True.intro,True.intro⟩
    | ok result =>
      rcases result with ⟨⟨value,v⟩,b⟩
      let receipt : WGRunWitness α := ⟨value,w,v,a,b⟩
      have valid : receipt.Valid native := (erases w a h).symm.trans (congrArg Prod.fst run)
      have before : Inv arm queue history w := grown.symm ▸ hi.append suffix
      exact ⟨suffix ++ [record receipt],by
        change history ++ [record receipt] = _
        rw [grown,List.append_assoc],True.intro,update history receipt valid before⟩

theorem observed_arm (body : WGPrefix E Unit) (cause : Cause) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (erases : ErasesStatePrefix body (armTimer pid timer delay caller)) (appends : StateAppends body) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (receiptWGObserved body (fun r => arm ⟨cause,pid,timer,delay,caller,r⟩)) :=
  receipt_update body _ erases appends _ (fun _ _ valid hi => hi.arm_record _ valid)

theorem observed_queue (body : WGPrefix E Unit) (cause : Cause) (pid : PeerId)
    (erases : ErasesStatePrefix body (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
    (appends : StateAppends body) :
    StatePrefixPreserves (fun h w _ => Inv arm queue h w) (fun _ => True)
      (receiptWGObserved body (fun r => queue ⟨cause,pid,r⟩)) :=
  receipt_update body _ erases appends _ (fun _ _ valid hi => hi.queue_record _ valid)

end Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
