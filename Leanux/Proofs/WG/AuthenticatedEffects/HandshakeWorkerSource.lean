import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausalReceiver
import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

/-! One handshake-worker cut shared by TX/session and causal observers. Session
and keepalive callbacks stay explicit; projection compares their actual retained
journals before composing the native worker source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def ops (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) : Ops (WGPrefix E) where
  step := liftWGPrefix
  session := session
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => liftWGPrefix (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => liftWGPrefix (consumeInitiation msg)
  response := fun msg => liftWGPrefix (consumeResponse msg)
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := keepalive
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => liftWGPrefix (WG.peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)


def workerWith (receive : Key → SkbSource → WGPrefix E Unit) : WGPrefix E Bool := do
  match (← liftWGPrefix getDev).handshakeQueue.consume with
  | (none, _) =>
    _ ← liftWGPrefix (branch .workerConsumed false)
    return false
  | (some (msg, src), ring) =>
    _ ← liftWGPrefix (branch .workerConsumed true)
    liftWGPrefix (modifyDev fun d => {d with handshakeQueue := ring})
    receive msg src
    liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1})
    return true

def source (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) : WGPrefix E Bool :=
  workerWith (receptionWith (ops session keepalive))

theorem factor (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) :
    source session keepalive = stepWith (ops session keepalive) := rfl

private theorem state_pure (ρ : E → Option F) (x : α) :
    StateProjectsPrefix (Outer := Outer) (Inner := Inner) ρ id (pure x) (pure x) := by
  intro w a h
  rfl
private theorem state_lift (ρ : E → Option F) (action : WG.M α) :
    StateProjectsPrefix ρ id (liftWGPrefix action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap ρ) =
    (((action.run w).run a).map (fun ((x,v),b) => ((x,v),b)),h.filterMap ρ)
  cases (action.run w).run a <;> rfl
private theorem state_choice (ρ : E → Option F) (p : Prop) [Decidable p]
    {g k : WGPrefix E α} {a b : WGPrefix F α}
    (hg : p → StateProjectsPrefix ρ id g a) (hk : ¬p → StateProjectsPrefix ρ id k b) :
    StateProjectsPrefix ρ id (if p then g else k) (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hg hp
  · exact hk hp
macro "handshake_worker_project_step " rho:ident : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; exact state_lift $rho _)
  | (maintenance_head Pure.pure; exact state_pure $rho _)
  | (maintenance_head Bind.bind; apply StateProjectsPrefix.bind $rho id id)
  | (maintenance_head ite; apply state_choice $rho)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem worker_projects (ρ : E → Option F)
    (g : Key → SkbSource → WGPrefix E Unit) (a : Key → SkbSource → WGPrefix F Unit)
    (ha : ∀ msg src, StateProjectsPrefix ρ id (g msg src) (a msg src)) :
    StateProjectsPrefix ρ id (workerWith g) (workerWith a) := by
  unfold workerWith
  repeat' first | exact ha _ _ | handshake_worker_project_step ρ

theorem reception_projects (ρ : E → Option F)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receptionWith (ops sg kg) msg src) (receptionWith (ops sa ka) msg src) := by
  unfold receptionWith afterMacWith responseWith
  simp only [ops]
  repeat' first | exact hs _ | exact hk _ | handshake_worker_project_step ρ

theorem projects (ρ : E → Option F)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) :
    StateProjectsPrefix ρ id (source sg kg) (source sa ka) :=
  worker_projects ρ _ _ (reception_projects ρ sg sa kg ka hs hk)

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker
