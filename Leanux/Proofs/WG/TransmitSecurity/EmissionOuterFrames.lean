import Leanux.Proofs.WG.AuthenticatedEffects.EmissionNativeFrames
import Leanux.Proofs.Framing.Syscalls
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

/-! Native product leaves preserve the actual pending sent buffer. A WGStore
frame does not imply this fact, because that projection omits emitted data. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EmissionOuter
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues AuthenticatedEffects

abbrev Sent := fun w : World => w.wg.sent

theorem wg (action : WG.M α) (frame : SameView WGWorld.sent action) :
    SameView Sent (monadLift action : Leanux.M α) :=
  sameView_liftWG Sent WGWorld.sent action frame (fun _ _ _ same => same)

theorem fs (action : FS.M α) : SameView Sent (monadLift action : Leanux.M α) :=
  fun _ => productFS_spec action _ (fun _ _ _ _ hi => hi)

theorem task (action : TaskM α) : SameView Sent (liftTask action) :=
  fun _ => productTask_spec action _ (fun _ _ _ hi => hi)

theorem seccomp (action : Seccomp.M α) : SameView Sent (monadLift action : Leanux.M α) :=
  fun _ => productSeccomp_spec action _ (fun _ _ _ _ hi => hi)

theorem ambient (action : AmbientM α) : SameView Sent (monadLift action : Leanux.M α) :=
  fun _ => productAmbient_spec action _ (fun _ _ hi => hi)

theorem routing (action : Net.M α) : SameView Sent (monadLift action : Leanux.M α) := by
  apply wg
  intro initial
  apply hoare_liftRouting
  intro w routing hi
  exact hi

theorem read : SameView Sent (get : Leanux.M World) := by
  intro initial
  exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2)

theorem read_wg : SameView Sent (getWG : Leanux.M WGWorld) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

theorem edit (f : World → World) (same : ∀ w, Sent (f w) = Sent w) :
    SameView Sent (modify f : Leanux.M Unit) :=
  fun _ => hoare_modify _ (fun w hi => (same w).symm ▸ hi)

theorem env (f : EnvWorld → EnvWorld) : SameView Sent (modifyEnv f) := by
  unfold modifyEnv
  exact edit _ (fun _ => rfl)

theorem socket (fd : Nat) (body : Leanux.M Int) (safe : SameView Sent body) :
    SameView Sent (Leanux.socketCallOn fd body) := by
  intro initial
  change Preserves (fun w : World => Sent w = initial) _
  have bodySafe : Preserves (fun w : World => Sent w = initial) body := safe initial
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := fs a initial
  routing_tx_source [Leanux.socketCallOn] using [bodySafe,files]

theorem netlink (body : Leanux.M Int) (safe : SameView Sent body) :
    SameView Sent (Leanux.netlinkRequest body) := by
  intro initial
  change Preserves (fun w : World => Sent w = initial) _
  have bodySafe : Preserves (fun w : World => Sent w = initial) body := safe initial
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := fs a initial
  have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := ambient a initial
  routing_tx_source [Leanux.netlinkRequest,Leanux.socketCall,Leanux.socketCallOn,skipCut]
    using [bodySafe,files,effects]

theorem rtnetlink (body : Leanux.M Int) (safe : SameView Sent body) :
    SameView Sent (Leanux.rtnetlinkRequest body) := by
  intro initial
  change Preserves (fun w : World => Sent w = initial) _
  have bodySafe : Preserves (fun w : World => Sent w = initial) body := safe initial
  have files {α : Type} (a : FS.M α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := fs a initial
  have tasks {α : Type} (a : TaskM α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := fs (monadLift a : FS.M α) initial
  have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Sent w = initial) (monadLift a : Leanux.M α) := ambient a initial
  have getWorld : Preserves (fun w : World => Sent w = initial) (get : Leanux.M World) := read initial
  routing_tx_source [Leanux.rtnetlinkRequest,Leanux.socketCallOn,skipCut,unsupported]
    using [bodySafe,files,tasks,effects,getWorld]
  all_goals exact edit _ (fun _ => rfl) initial

end Leanux.Proofs.WG.TransmitSecurity.EmissionOuter
