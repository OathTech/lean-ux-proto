import Leanux.Proofs.WG.HandshakeSecurity.EmissionLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionSchedulerFrames

/-! Native deferred-loop bookkeeping and clear-work leaves preserve sent.
The actual socket and delivery callbacks remain separately observed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity HandshakeSecurity

theorem env_read : SameView EmissionOuter.Sent (getEnv : Leanux.M EnvWorld) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

theorem wg_edit (f : WGWorld → WGWorld) (same : ∀ w, (f w).sent = w.sent) :
    SameView EmissionOuter.Sent (modifyWG f : Leanux.M Unit) := by
  unfold modifyWG
  exact EmissionOuter.edit _ (fun w => same w.wg)

theorem clear_one : SameView EmissionOuter.Sent Env.runOneClearWorker := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  have edit (f : Device → Device) : Preserves P (monadLift (modifyDev f) : Leanux.M Unit) :=
    EmissionOuter.wg _ (by sent_frame [] using []) initial
  have clear (pid : PeerId) : Preserves P (monadLift (queuedExpiredZeroKeyMaterial pid) : Leanux.M Unit) :=
    EmissionOuter.wg _ (EmissionClearing.queued_clear pid) initial
  routing_tx_source [Env.runOneClearWorker,Env.runWorker,peekUnit,resolveUnit,hidden,modifyAmbient,invariant]
    using [ambient,dev,edit,clear]

theorem drained (what : String) (queues : List Bool) : SameView EmissionOuter.Sent (Env.requireDrained what queues) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  routing_tx_source [Env.requireDrained,invariant,unsupported] using [ambient,dev]

theorem no_crypt : SameView EmissionOuter.Sent Env.requireNoCryptWork := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have read : Preserves P (getWG : Leanux.M WGWorld) := EmissionOuter.read_wg initial
  routing_tx_source [Env.requireNoCryptWork,unsupported] using [ambient,read]

theorem peek_next : SameView EmissionOuter.Sent Env.peekNextSite := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.peekNextSite,getAmbient] using [ambient]

theorem timer_worker (timer : PeerTimer) : SameView EmissionOuter.Sent (Env.timerWorker timer) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.timerWorker,invariant] using [ambient]

theorem step_complete (bound : UInt64) : SameView EmissionOuter.Sent (Env.requireStepComplete bound) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  routing_tx_source [Env.requireStepComplete] using [dev]
  all_goals
    apply (hoare_iff_run _ _ _).mpr
    intro w value v hi run
    cases run

theorem nothing_due (bound : UInt64) : SameView EmissionOuter.Sent (Env.requireNothingDue bound) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have read : Preserves P (getWG : Leanux.M WGWorld) := EmissionOuter.read_wg initial
  have world : Preserves P (get : Leanux.M World) := EmissionOuter.read initial
  have timer (t : PeerTimer) : Preserves P (Env.timerWorker t) := timer_worker t initial
  routing_tx_source [Env.requireNothingDue,Env.sectionAppearsLater,unsupported] using [ambient,read,world,timer]
  all_goals
    apply (hoare_iff_run _ _ _).mpr
    intro w value v hi run
    cases run

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
