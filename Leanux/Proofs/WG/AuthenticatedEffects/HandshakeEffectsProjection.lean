import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral

/-! Exact old-journal projections for lexical handshake scopes and native
helper substitutions. Normal returns and every internally stopped prefix agree. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

private theorem scope_projects (ρ : E → Option F)
    (record : CausalScope.Event Cause → E) (cause : Cause)
    (quiet : ∀ event, ρ (record event) = none)
    (g : WGPrefix E α) (t : WGPrefix F α) (projects : StateProjectsPrefix ρ id g t) :
    StateProjectsPrefix ρ id (CausalScope.scope record cause g) t :=
  CausalScope.withToken_projects record cause ρ quiet (fun _ => g) t (fun _ => projects)

theorem scopeOps_projects (ρ : E → Option F)
    (record : CausalScope.Event Cause → E)
    (cause : HandshakeCausal.Kind → PeerId → Cause)
    (quiet : ∀ event, ρ (record event) = none)
    (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F))
    (projects : HandshakeWorker.OpsProjects ρ g t) :
    HandshakeWorker.OpsProjects ρ (scopeOps record cause g) t where
  step := projects.step
  session := fun pid => scope_projects ρ record _ quiet _ _ (projects.session pid)
  modifyPeer := fun pid f => scope_projects ρ record _ quiet _ _ (projects.modifyPeer pid f)
  create := fun pid => scope_projects ρ record _ quiet _ _ (projects.create pid)
  mac := fun pid msg => scope_projects ρ record _ quiet _ _ (projects.mac pid msg)
  send := fun pid msg => scope_projects ρ record _ quiet _ _ (projects.send pid msg)
  derived := fun pid => scope_projects ρ record _ quiet _ _ (projects.derived pid)
  traversal := fun pid => scope_projects ρ record _ quiet _ _ (projects.traversal pid)
  sent := fun pid => scope_projects ρ record _ quiet _ _ (projects.sent pid)
  cookie := projects.cookie
  initiation := projects.initiation
  response := projects.response
  endpoint := fun pid src => scope_projects ρ record _ quiet _ _ (projects.endpoint pid src)
  complete := fun pid => scope_projects ρ record _ quiet _ _ (projects.complete pid)
  keepalive := fun pid => scope_projects ρ record _ quiet _ _ (projects.keepalive pid)
  received := fun pid => scope_projects ρ record _ quiet _ _ (projects.received pid)
  put := projects.put
  cookieConsume := projects.cookieConsume

/-- A callback's native body adds no inner events, so its old focused observer
is exactly the entry marker followed by that same native body. -/
theorem old_call (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event) (kind : HandshakeCausal.Kind)
    (pid : PeerId) (native : WG.M α) :
    HandshakeWorker.old record decode (HandshakeCausal.call kind pid native) =
      HandshakeWorker.callback record kind pid (liftWGPrefix native) := by
  funext w a h
  change ((runWGPrefix (HandshakeCausal.call kind pid native) w a (h.filterMap decode)).1,
      h ++ ((runWGPrefix (HandshakeCausal.call kind pid native) w a (h.filterMap decode)).2.drop
        (h.filterMap decode).length).map record) =
    runWGPrefix (HandshakeWorker.callback record kind pid (liftWGPrefix native)) w a h
  simp only [HandshakeCausal.call,HandshakeWorker.callback,runWGPrefix,runStatePrefix_bind,
    runStatePrefix_emit]
  change ((native.run w).run a,h ++ (((h.filterMap decode) ++ [HandshakeCausal.Event.callback kind pid]).drop (h.filterMap decode).length).map record) = _
  simp only [List.drop_left,List.map_cons,List.map_nil]
  rfl


theorem callback_projects (ρ : E → Option F)
    (record : HandshakeCausal.Event → E) (targetRecord : HandshakeCausal.Event → F)
    (matching : ∀ event, ρ (record event) = some (targetRecord event))
    (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix E α) (target : WGPrefix F α)
    (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (HandshakeWorker.callback record kind pid body)
      (HandshakeWorker.callback targetRecord kind pid target) := by
  intro w a h
  have projected := projects w a (h ++ [record (.callback kind pid)])
  change runStatePrefix (HandshakeWorker.callback targetRecord kind pid target) w a (h.filterMap ρ) =
    ((runStatePrefix (HandshakeWorker.callback record kind pid body) w a h).1.map
      (fun ((x,v),b) => ((x,v),b)),
      (runStatePrefix (HandshakeWorker.callback record kind pid body) w a h).2.filterMap ρ)
  unfold HandshakeWorker.callback
  rw [runStatePrefix_bind,runStatePrefix_emit,runStatePrefix_bind,runStatePrefix_emit]
  simpa only [Prod.map,id,Prod.eta,runStatePrefix,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,matching,Option.toList_some,List.singleton_append] using projected

theorem withEffects_projects (ρ : E → Option F)
    (record : HandshakeCausal.Event → E) (targetRecord : HandshakeCausal.Event → F)
    (matching : ∀ event, ρ (record event) = some (targetRecord event))
    (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F))
    (effects : TimerEffects.Ops (WGPrefix E)) (targetEffects : TimerEffects.Ops (WGPrefix F))
    (base : HandshakeWorker.OpsProjects ρ g t)
    (effectProjects : TimerEffects.Ops.Projects ρ effects targetEffects) :
    HandshakeWorker.OpsProjects ρ (withEffects g record effects) (withEffects t targetRecord targetEffects) :=
  {base with
    derived := fun pid => callback_projects ρ record targetRecord matching _ _ _ _
      (TimerEffects.derived_projects ρ effectProjects pid)
    traversal := fun pid => callback_projects ρ record targetRecord matching _ _ _ _
      (TimerEffects.traversal_projects ρ effectProjects pid)}

theorem withEffects_neutral (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (mac : HandshakeMac) :
    withEffects (HandshakeWorker.observedOps record decode session keepalive mac) record TimerEffects.lifted =
      HandshakeWorker.observedOps record decode session keepalive mac := by
  simp only [withEffects,HandshakeWorker.observedOps,TimerEffects.derived_lifted,
    TimerEffects.traversal_lifted,old_call]

/-- One actual worker, with scope markers and effect receipts removed, returns
exactly the prior observer's complete result and retained journal. -/
theorem worker_projects (ρ : E → Option F)
    (record : CausalScope.Event Cause → E)
    (cause : HandshakeCausal.Kind → PeerId → Cause)
    (quiet : ∀ event, ρ (record event) = none)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (projects : ∀ mac, HandshakeWorker.OpsProjects ρ (g mac) (t mac)) :
    StateProjectsPrefix ρ id
      (HandshakeWorker.observedWith (fun mac => scopeOps record cause (g mac)))
      (HandshakeWorker.observedWith t) :=
  HandshakeWorker.observedWith_projects ρ _ t
    (fun mac => scopeOps_projects ρ record cause quiet _ _ (projects mac))

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffects
