import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsProjection

/-! The causal handshake extension matches the existing shared observer's
callback journals. In particular its HC projection does not replace observed
consumers with separate executions of the native consumer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

private theorem lift_projects (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
  cases (action.run w).run a <;> rfl

private theorem call_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (inverse : ∀ e, decode (record e) = some e)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (action : WG.M α) :
    StateProjectsPrefix decode id
      (HandshakeWorker.old record decode (HandshakeCausal.call kind pid action))
      (HandshakeWorker.old id some (HandshakeCausal.call kind pid action)) := by
  rw [old_call,old_call]
  exact callback_projects decode record id inverse kind pid _ _ (lift_projects decode action)

theorem observedOps_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (inverse : ∀ e, decode (record e) = some e)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (kt pid)) (mac : HandshakeMac) :
    HandshakeWorker.OpsProjects decode (HandshakeWorker.observedOps record decode sg kg mac)
      (HandshakeWorker.observedOps id some st kt mac) where
  step := fun action => lift_projects decode action
  session := fun pid => callback_projects decode record id inverse _ _ _ _ (hs pid)
  modifyPeer := fun pid _ => call_matching record decode inverse _ pid _
  create := fun pid => call_matching record decode inverse _ pid _
  mac := fun pid _ => call_matching record decode inverse _ pid _
  send := fun pid _ => call_matching record decode inverse _ pid _
  derived := fun pid => call_matching record decode inverse _ pid _
  traversal := fun pid => call_matching record decode inverse _ pid _
  sent := fun pid => call_matching record decode inverse _ pid _
  cookie := fun _ _ => lift_projects decode _
  initiation := fun _ =>
    (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.focus_matching)
      record decode inverse _ (StateAppends.focus _ _ _)
  response := fun _ =>
    (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.focus_matching)
      record decode inverse _ (StateAppends.focus _ _ _)
  endpoint := fun pid _ => call_matching record decode inverse _ pid _
  complete := fun pid => call_matching record decode inverse _ pid _
  keepalive := fun pid => callback_projects decode record id inverse _ _ _ _ (hk pid)
  received := fun pid => call_matching record decode inverse _ pid _
  put := fun _ => lift_projects decode _
  cookieConsume := fun _ => lift_projects decode _

/-- The HC specialization retains its actual admission/callback stream while
new scope and timer receipts remain in the larger, shared journal. -/
theorem worker_matching (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (inverse : ∀ e, decode (record e) = some e)
    (scopeRecord : CausalScope.Event Cause → E)
    (cause : HandshakeCausal.Kind → PeerId → Cause)
    (quiet : ∀ e, decode (scopeRecord e) = none)
    (effects : TimerEffects.Ops (WGPrefix E))
    (he : TimerEffects.Ops.Projects decode effects TimerEffects.lifted)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decode id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix decode id (kg pid) (kt pid)) :
    StateProjectsPrefix decode id
      (HandshakeWorker.observedWith (fun mac => scopeOps scopeRecord cause
        (withEffects (HandshakeWorker.observedOps record decode sg kg mac) record effects)))
      (HandshakeWorker.observed id some st kt) := by
  rw [HandshakeWorker.observed_factor]
  apply worker_projects decode scopeRecord cause quiet
  intro mac
  have h := withEffects_projects decode record id inverse _ _ effects TimerEffects.lifted
    (observedOps_matching record decode inverse sg st kg kt hs hk mac) he
  rwa [withEffects_neutral] at h

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
