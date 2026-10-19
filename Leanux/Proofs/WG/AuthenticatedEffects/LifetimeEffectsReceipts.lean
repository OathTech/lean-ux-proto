import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects

/-! Add actual timer/work receipts around the original lifetime observers.
Their accesses and stopped prefixes stay present; the cause is read from the
real incoming scope, never reconstructed from a later convenient admission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem receipt_projects (ρ : E → Option F) (record : WGRunWitness α → E)
    (quiet : ∀ r, ρ (record r) = none) {g : WGPrefix E α} {t : WGPrefix F α}
    (project : StateProjectsPrefix ρ id g t) :
    StateProjectsPrefix ρ id (receiptWGObserved g record) t := by
  intro w a h
  have same := project w a h
  change runWGPrefix t w a (h.filterMap ρ) =
    ((runWGPrefix g w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix g w a h).2.filterMap ρ) at same
  change runWGPrefix t w a (h.filterMap ρ) =
    ((runWGPrefix (receiptWGObserved g record) w a h).1.map (fun ((x,v),b) => ((x,v),b)),
      (runWGPrefix (receiptWGObserved g record) w a h).2.filterMap ρ)
  rw [runWGPrefix_receiptWGObserved]
  cases run : runWGPrefix g w a h with
  | mk result history =>
    rw [run] at same
    cases result with
    | error err => exact same
    | ok out =>
      rcases out with ⟨⟨x,v⟩,b⟩
      simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
        List.append_nil] using same

def decorate (base : Ops (WGPrefix E)) (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E) : Ops (WGPrefix E) :=
  {base with
    arm := fun pid timer delay caller => CausalEffects.atCurrent decode fun context =>
      receiptWGObserved (base.arm pid timer delay caller)
        (fun r => recordArm ⟨context,pid,timer,delay,caller,r⟩)
    append := fun pid => CausalEffects.atCurrent decode fun context =>
      receiptWGObserved (base.append pid) (fun r => recordQueue ⟨context,pid,r⟩)}

theorem decorate_projects (ρ : E → Option F) (base : Ops (WGPrefix E))
    (target : Ops (WGPrefix F)) (h : Ops.Projects ρ base target)
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (ha : ∀ r, ρ (recordArm r) = none) (hq : ∀ r, ρ (recordQueue r) = none) :
    Ops.Projects ρ (decorate base decode recordArm recordQueue) target where
  step := h.step
  peer := h.peer
  keypair := h.keypair
  modifyPeer := h.modifyPeer
  guard := h.guard
  get := h.get
  put := h.put
  arm := fun pid timer delay caller => CausalEffects.atCurrent_projects decode _ ρ _
    (fun _ => receipt_projects ρ _ (fun _ => ha _) (h.arm pid timer delay caller))
  append := fun pid => CausalEffects.atCurrent_projects decode _ ρ _
    (fun _ => receipt_projects ρ _ (fun _ => hq _) (h.append pid))

theorem arm_completed (base : Ops (WGPrefix E))
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (w v : WGWorld) (a b : Ambient) (h history : List E)
    (run : runWGPrefix (base.arm pid timer delay caller) w a h = (.ok (((),v),b),history)) :
    runWGPrefix ((decorate base decode recordArm recordQueue).arm pid timer delay caller) w a h =
      (.ok (((),v),b),history ++ [recordArm ⟨CausalScope.current decode h,pid,timer,delay,caller,⟨(),w,v,a,b⟩⟩]) := by
  dsimp only [decorate]
  rw [CausalEffects.atCurrent_run,runWGPrefix_receiptWGObserved,run]

end Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
