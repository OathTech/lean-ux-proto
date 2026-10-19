import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection

/-! The existing cookie/MAC prefix with callback-parametric authenticated
suffixes. Completed consumer/create receipts and causal scopes can share this
source without replacing the native worker or losing an internal Stop prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def receiveWith (make : HandshakeMac → Ops (WGPrefix E))
    (msg : Key) (src : SkbSource) : WGPrefix E Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (make ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

def observedWith (make : HandshakeMac → Ops (WGPrefix E)) : WGPrefix E Bool :=
  workerWith (receiveWith make)

theorem observedReceive_factor (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (msg : Key) (src : SkbSource) :
    observedReceive record decode session keepalive msg src =
      receiveWith (observedOps record decode session keepalive) msg src := rfl

theorem observed_factor (record : HandshakeCausal.Event → E)
    (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) :
    observed record decode session keepalive =
      observedWith (observedOps record decode session keepalive) := rfl

structure OpsProjects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (g.step action) (t.step action)
  session : ∀ pid, StateProjectsPrefix ρ id (g.session pid) (t.session pid)
  modifyPeer : ∀ pid f, StateProjectsPrefix ρ id (g.modifyPeer pid f) (t.modifyPeer pid f)
  create : ∀ pid, StateProjectsPrefix ρ id (g.create pid) (t.create pid)
  mac : ∀ pid msg, StateProjectsPrefix ρ id (g.mac pid msg) (t.mac pid msg)
  send : ∀ pid msg, StateProjectsPrefix ρ id (g.send pid msg) (t.send pid msg)
  derived : ∀ pid, StateProjectsPrefix ρ id (g.derived pid) (t.derived pid)
  traversal : ∀ pid, StateProjectsPrefix ρ id (g.traversal pid) (t.traversal pid)
  sent : ∀ pid, StateProjectsPrefix ρ id (g.sent pid) (t.sent pid)
  cookie : ∀ msg src, StateProjectsPrefix ρ id (g.cookie msg src) (t.cookie msg src)
  initiation : ∀ msg, StateProjectsPrefix ρ id (g.initiation msg) (t.initiation msg)
  response : ∀ msg, StateProjectsPrefix ρ id (g.response msg) (t.response msg)
  endpoint : ∀ pid src, StateProjectsPrefix ρ id (g.endpoint pid src) (t.endpoint pid src)
  complete : ∀ pid, StateProjectsPrefix ρ id (g.complete pid) (t.complete pid)
  keepalive : ∀ pid, StateProjectsPrefix ρ id (g.keepalive pid) (t.keepalive pid)
  received : ∀ pid, StateProjectsPrefix ρ id (g.received pid) (t.received pid)
  put : ∀ peer, StateProjectsPrefix ρ id (g.put peer) (t.put peer)
  cookieConsume : ∀ msg, StateProjectsPrefix ρ id (g.cookieConsume msg) (t.cookieConsume msg)

macro "handshake_ops_project " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact OpsProjects.step $h _
  | with_reducible exact OpsProjects.session $h _
  | with_reducible exact OpsProjects.modifyPeer $h _ _
  | with_reducible exact OpsProjects.create $h _
  | with_reducible exact OpsProjects.mac $h _ _
  | with_reducible exact OpsProjects.send $h _ _
  | with_reducible exact OpsProjects.derived $h _
  | with_reducible exact OpsProjects.traversal $h _
  | with_reducible exact OpsProjects.sent $h _
  | with_reducible exact OpsProjects.cookie $h _ _
  | with_reducible exact OpsProjects.initiation $h _
  | with_reducible exact OpsProjects.response $h _
  | with_reducible exact OpsProjects.endpoint $h _ _
  | with_reducible exact OpsProjects.complete $h _
  | with_reducible exact OpsProjects.keepalive $h _
  | with_reducible exact OpsProjects.received $h _
  | with_reducible exact OpsProjects.put $h _
  | with_reducible exact OpsProjects.cookieConsume $h _
  | handshake_worker_project_step $rho)

theorem afterMac_projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F))
    (h : OpsProjects ρ g t) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateProjectsPrefix ρ id (afterMacWith g msg src loaded state) (afterMacWith t msg src loaded state) := by
  unfold afterMacWith responseWith
  repeat' handshake_ops_project h ρ

theorem receiveWith_projects (ρ : E → Option F)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (h : ∀ mac, OpsProjects ρ (g mac) (t mac)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receiveWith g msg src) (receiveWith t msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact afterMac_projects ρ _ _ (h _) _ _ _ _
    | with_reducible exact
        (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.capture_self) ρ _
    | handshake_worker_project_step ρ

theorem observedWith_projects (ρ : E → Option F)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (h : ∀ mac, OpsProjects ρ (g mac) (t mac)) :
    StateProjectsPrefix ρ id (observedWith g) (observedWith t) :=
  worker_projects ρ _ _ (receiveWith_projects ρ g t h)

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
