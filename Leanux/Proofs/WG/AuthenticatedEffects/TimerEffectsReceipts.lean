import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsErasure

/-! Timer and work-append receipts take a caller-supplied causal token. The
source closure passes that token directly to each actual native effect; these
receipts do not search a journal for a convenient earlier authentication. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Arm (Cause : Type) where
  cause : Cause
  peer : PeerId
  timer : PeerTimer
  delay : Nat
  caller : Option UInt64
  run : WGRunWitness Unit

def Arm.Valid (r : Arm Cause) : Prop :=
  r.run.Valid (armTimer r.peer r.timer r.delay r.caller)

structure Queued (Cause : Type) where
  cause : Cause
  peer : PeerId
  run : WGRunWitness Unit

def Queued.Valid (r : Queued Cause) : Prop :=
  r.run.Valid (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [r.peer]})

def armReceipt (record : Arm Cause → E) (cause : Cause) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) : WGPrefix E Unit :=
  receiptWGObserved (liftWGPrefix (armTimer pid timer delay caller))
    (fun r => record ⟨cause,pid,timer,delay,caller,r⟩)

def queueReceipt (record : Queued Cause → E) (cause : Cause) (pid : PeerId) : WGPrefix E Unit :=
  receiptWGObserved (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
    (fun r => record ⟨cause,pid,r⟩)

def receipts (recordArm : Arm Cause → E) (recordQueue : Queued Cause → E)
    (cause : Cause) : Ops (WGPrefix E) :=
  observed (armReceipt recordArm cause) (queueReceipt recordQueue cause)

def lifted : Ops (WGPrefix E) := observed
  (fun pid timer delay caller => liftWGPrefix (armTimer pid timer delay caller))
  (fun pid => liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))

theorem receipts_erases (recordArm : Arm Cause → E) (recordQueue : Queued Cause → E)
    (cause : Cause) : Ops.Erases (receipts recordArm recordQueue cause) where
  step := erasesStatePrefix_lift
  arm := fun _ _ _ _ => receiptWGObserved_erases (erasesStatePrefix_lift _) _
  append := fun _ => receiptWGObserved_erases (erasesStatePrefix_lift _) _

private theorem receipt_projects (ρ : E → Option F) (native : WG.M α)
    (record : WGRunWitness α → E) (quiet : ∀ r, ρ (record r) = none) :
    StateProjectsPrefix ρ id (receiptWGObserved (liftWGPrefix native) record) (liftWGPrefix native) := by
  intro w a h
  change ((native.run w).run a,h.filterMap ρ) =
    ((runWGPrefix (receiptWGObserved (liftWGPrefix native) record) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (receiptWGObserved (liftWGPrefix native) record) w a h).2.filterMap ρ)
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases result : (native.run w).run a with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨x,v⟩,b⟩
    simp only [Except.map,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      quiet,List.append_nil]

theorem receipts_projects (ρ : E → Option F) (recordArm : Arm Cause → E)
    (recordQueue : Queued Cause → E) (cause : Cause)
    (ha : ∀ r, ρ (recordArm r) = none) (hq : ∀ r, ρ (recordQueue r) = none) :
    Ops.Projects ρ (receipts recordArm recordQueue cause) lifted where
  step := by
    intro α action w a h
    change ((action.run w).run a,h.filterMap ρ) =
      (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
    cases (action.run w).run a <;> rfl
  arm := fun _ _ _ _ => receipt_projects ρ _ _ (fun _ => ha _)
  append := fun _ => receipt_projects ρ _ _ (fun _ => hq _)

/-- The recorded effect is the actual arm under the caller's exact token,
and its event precedes any continuation, even one that later Stops. -/
theorem arm_completed (record : Arm Cause → E) (cause : Cause) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (w v : WGWorld) (a b : Ambient) (h : List E)
    (run : ((armTimer pid timer delay caller).run w).run a = .ok (((),v),b)) :
    runWGPrefix (armReceipt record cause pid timer delay caller) w a h =
      (.ok (((),v),b),h ++ [record ⟨cause,pid,timer,delay,caller,⟨(),w,v,a,b⟩⟩]) := by
  rw [armReceipt,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

/-- Queue receipts describe the single native append, retaining the exact
incoming queue and caller token instead of conflating repeated peer entries. -/
theorem queue_completed (record : Queued Cause → E) (cause : Cause) (pid : PeerId)
    (w v : WGWorld) (a b : Ambient) (h : List E)
    (run : ((modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}).run w).run a =
      .ok (((),v),b)) :
    runWGPrefix (queueReceipt record cause pid) w a h =
      (.ok (((),v),b),h ++ [record ⟨cause,pid,⟨(),w,v,a,b⟩⟩]) := by
  rw [queueReceipt,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
