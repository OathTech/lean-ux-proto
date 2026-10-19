import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsMatching

/-! Other shared-journal projections retain their callback histories while HC
and scope events are silent. This includes the nonce/responder specializations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem capture_value (action : WG.M α) (next : α → WGPrefix E β) :
    (captureWGRun action >>= fun r => next r.value) = (liftWGPrefix action >>= next) := by
  funext w a h
  change runWGPrefix (captureWGRun action >>= fun r => next r.value) w a h =
    runWGPrefix (liftWGPrefix action >>= next) w a h
  simp only [runWGPrefix,runStatePrefix_bind]
  rw [show runStatePrefix (captureWGRun action) w a h = _ from runWGPrefix_captureWGRun action w a h]
  simp only [liftWGPrefix,runStatePrefix_lift]
  cases (action.run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

theorem constant_receive (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) (msg : Key) (src : SkbSource) :
  HandshakeWorker.receiveWith (fun _ => HandshakeWorker.ops session keepalive) msg src = receptionWith (HandshakeWorker.ops session keepalive) msg src := by
  unfold HandshakeWorker.receiveWith receptionWith
  simp only [HandshakeWorker.ops]
  congr 1
  funext cookie
  split
  · rfl
  · congr 1
    funext loaded
    exact capture_value _ _

private theorem lift_projects (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
  cases (action.run w).run a <;> rfl

private theorem callback_other (record : HandshakeCausal.Event → E) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix E α) (target : WGPrefix F α) (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (HandshakeWorker.callback record kind pid body) target :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.callback_projects)
    record ρ quiet kind pid body target projects

private theorem old_other (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ event, ρ (record event) = none) (body : WGPrefix HandshakeCausal.Event α)
    (native : WG.M α) (erases : ErasesStatePrefix body native) :
    StateProjectsPrefix ρ id (HandshakeWorker.old record decode body) (liftWGPrefix native) :=
  (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.focus_other)
    record decode ρ quiet body native erases

theorem observedOps_other (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (record e) = none)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects ρ (HandshakeWorker.observedOps record decode sg kg mac)
      (HandshakeWorker.ops st kt) where
  step := fun action => lift_projects ρ action
  session := fun pid => callback_other record ρ quiet _ _ _ _ (hs pid)
  modifyPeer := fun _ _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  create := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  mac := fun _ _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  send := fun _ _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  derived := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  traversal := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  sent := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  cookie := fun _ _ => lift_projects ρ _
  initiation := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.initiation_erases _)
  response := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.response_erases _)
  endpoint := fun _ _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  complete := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  keepalive := fun pid => callback_other record ρ quiet _ _ _ _ (hk pid)
  received := fun _ => old_other record decode ρ quiet _ _ (HandshakeCausal.call_erases _ _ _)
  put := fun _ => lift_projects ρ _
  cookieConsume := fun _ => lift_projects ρ _

theorem effects_other (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (record e) = none)
    (effects : TimerEffects.Ops (WGPrefix E))
    (he : TimerEffects.Ops.Projects ρ effects TimerEffects.lifted)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects ρ
      (withEffects (HandshakeWorker.observedOps record decode sg kg mac) record effects)
      (HandshakeWorker.ops st kt) :=
  {observedOps_other record decode ρ quiet sg st kg kt hs hk mac with
    derived := fun pid => callback_other record ρ quiet _ _ _ _ (by
      simpa only [TimerEffects.derived_lifted,HandshakeWorker.ops] using TimerEffects.derived_projects ρ he pid)
    traversal := fun pid => callback_other record ρ quiet _ _ _ _ (by
      simpa only [TimerEffects.traversal_lifted,HandshakeWorker.ops] using TimerEffects.traversal_projects ρ he pid)}

/-- Non-HC projections retain the prior native worker with its own observed
session/keepalive callbacks, rather than comparing erased native runs. -/
theorem worker_other (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (record e) = none)
    (scopeRecord : CausalScope.Event Cause → E)
    (cause : HandshakeCausal.Kind → PeerId → Cause)
    (scopeQuiet : ∀ e, ρ (scopeRecord e) = none)
    (effects : TimerEffects.Ops (WGPrefix E))
    (he : TimerEffects.Ops.Projects ρ effects TimerEffects.lifted)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) :
    StateProjectsPrefix ρ id
      (HandshakeWorker.observedWith (fun mac => scopeOps scopeRecord cause
        (withEffects (HandshakeWorker.observedOps record decode sg kg mac) record effects)))
      (HandshakeWorker.source st kt) := by
  have h := worker_projects ρ scopeRecord cause scopeQuiet
    (fun mac => withEffects (HandshakeWorker.observedOps record decode sg kg mac) record effects)
    (fun _ => HandshakeWorker.ops st kt)
    (fun mac => effects_other record decode ρ quiet effects he sg st kg kt hs hk mac)
  have same : HandshakeWorker.receiveWith (fun _ => HandshakeWorker.ops st kt) =
      receptionWith (HandshakeWorker.ops st kt) := funext fun msg => funext fun src => constant_receive st kt msg src
  simp only [HandshakeWorker.observedWith,same] at h
  exact h

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
