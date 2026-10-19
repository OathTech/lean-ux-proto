import Leanux.Proofs.WG.RetirementSecurity.TxActorNeutral

/-! Native delivery, guards and section bookkeeping retain TX ownership and
service while keeping actual suspended activations. These facts feed deferred
worker and timer source composition, without a general ambient frame premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem deliver_actor : Preserves (At (Covered locals crypt) crypt active) Env.deliverSent := by
  have route:Preserves (At (Covered locals crypt) crypt active) (getRouting : Leanux.M Net.Routing) := by
    apply at_world
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl
  unfold Env.deliverSent
  repeat' first
    | (rx_retention_head getRouting; exact route)
    | actor_neutral_step

theorem drained_actor (what : String) (queues : List Bool) :
    Preserves (At (Covered locals crypt) crypt active) (Env.requireDrained what queues) := by
  have pending : Preserves (At (Covered locals crypt) crypt active) (pendingDeviceUnits : Leanux.M (List Worker)) := by
    apply at_world
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl
  unfold Env.requireDrained
  repeat' first | exact pending | actor_neutral_step

theorem no_crypt_actor : Preserves (At (Covered locals crypt) crypt active) Env.requireNoCryptWork := by
  unfold Env.requireNoCryptWork
  repeat' actor_neutral_step

theorem idle_device_actor : Preserves (At (Covered locals crypt) crypt active) Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  apply preserves_bind no_crypt_actor
  intro _
  repeat' actor_neutral_step

theorem peek_next_actor : Preserves (At (Covered locals crypt) crypt active) Env.peekNextSite := by
  unfold Env.peekNextSite
  repeat' actor_neutral_step

theorem timer_worker_actor (timer : PeerTimer) :
    Preserves (At (Covered locals crypt) crypt active) (Env.timerWorker timer) := by
  unfold Env.timerWorker
  repeat' actor_neutral_step

theorem step_complete_actor (bucket : UInt64) :
    Preserves (At (Covered locals crypt) crypt active) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  repeat' actor_neutral_step

theorem section_later_actor (worker : Worker) (unit : Nat) :
    Preserves (At P crypt active) (Env.sectionAppearsLater worker unit) := by
  apply at_world
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem nothing_due_actor (j : UInt64) :
    Preserves (At (Covered locals crypt) crypt active) (Env.requireNothingDue j) := by
  unfold Env.requireNothingDue
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact section_later_actor _ _)
    | (rx_retention_head Env.timerWorker; exact timer_worker_actor _)
    | actor_neutral_step

theorem run_worker_actor (worker : Worker) {body : Leanux.M Unit}
    (keeps : Preserves (At (Covered locals crypt) crypt active) body) :
    Preserves (At (Covered locals crypt) crypt active) (Env.runWorker worker body) := by
  unfold Env.runWorker
  repeat' first | exact keeps | actor_neutral_step

theorem timer_section_actor (worker : Worker) {body : Leanux.M Unit}
    (keeps : Preserves (At (Covered locals crypt) crypt active) body) :
    Preserves (At (Covered locals crypt) crypt active) (Env.runTimerSection worker body) := by
  unfold Env.runTimerSection
  repeat' first
    | (rx_retention_head Env.runWorker; exact run_worker_actor _ keeps)
    | actor_neutral_step

theorem del_actor (pid : PeerId) (timer : PeerTimer) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (delTimer pid timer)) :=
  At.native (fun _=>serving_del pid timer) (TxSuspension.delete pid timer)

theorem peek_u64_actor (site : HiddenSite) :
    Preserves (At P crypt active) (Leanux.peekSiteU64 site : Leanux.M (Option UInt64)) := by
  apply actor_ambient (action:=AmbientM.peekSiteU64 site)
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem jiffies_actor (site : HiddenSite) :
    Preserves (At P crypt active) (Leanux.hiddenJiffies site : Leanux.M UInt64) :=
  actor_ambient (action:=AmbientM.hiddenJiffies site) ((TxActorFrames.hidden site).bind (fun _=>SameView.pure _ _))

macro "actor_deferred_step" : tactic => `(tactic| first
  | (rx_retention_head Env.deliverSent; exact deliver_actor)
  | (rx_retention_head Env.requireDrained; exact drained_actor _ _)
  | (rx_retention_head Env.requireNoCryptWork; exact no_crypt_actor)
  | (rx_retention_head Env.requireIdleDevice; exact idle_device_actor)
  | (rx_retention_head Env.peekNextSite; exact peek_next_actor)
  | (rx_retention_head Env.timerWorker; exact timer_worker_actor _)
  | (rx_retention_head Env.requireStepComplete; exact step_complete_actor _)
  | (rx_retention_head Env.requireNothingDue; exact nothing_due_actor _)
  | (rx_retention_head peekSiteU64; exact peek_u64_actor _)
  | (rx_retention_head hiddenJiffies; exact jiffies_actor _)
  | (rx_retention_head Env.runOneSendWorker; exact send_one_actor)
  | (rx_retention_head Env.runOneClearWorker; exact clear_one_actor)
  | (rx_retention_head Env.schedule; exact native_scheduler _)
  | (rx_retention_head Env.runTimerSection; exact timer_section_actor _ (callback_actor _ _))
  | (allocation_release_lift_from WG.M; exact del_actor _ _)
  | actor_neutral_step)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
