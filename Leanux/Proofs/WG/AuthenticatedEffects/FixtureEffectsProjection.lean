import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource

/-! Projection contracts for the guarded local-trigger factors. Scope tokens
are allowed to change under projection; native values, states and stopped
prefixes are retained exactly. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem run_projects (ρ : E → Option F) (scopeMap : Nat → Nat)
    (g : Hooks E) (t : Hooks F)
    (enter : ∀ trigger, StateProjectsPrefix ρ scopeMap (g.enter trigger) (t.enter trigger))
    (leave : ∀ token, StateProjectsPrefix ρ id (g.leave token) (t.leave (scopeMap token)))
    (trigger : Trigger) (body : WGPrefix E α) (target : WGPrefix F α)
    (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id (runWith g trigger body) (runWith t trigger target) := by
  unfold runWith
  apply StateProjectsPrefix.bind ρ scopeMap id (enter trigger)
  intro token
  apply StateProjectsPrefix.bind ρ id id projects
  intro value
  apply StateProjectsPrefix.bind ρ id id (leave token)
  intro _
  intro w a h
  rfl

private theorem loop_projects (ρ : E → Option F) (xs : List α) (initial : β)
    (g : α → β → WGPrefix E (ForInStep β)) (t : α → β → WGPrefix F (ForInStep β))
    (h : ∀ x b, StateProjectsPrefix ρ id (g x b) (t x b)) :
    StateProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => intro w a history; rfl
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (h x initial)
    intro step
    cases step with
    | done b => intro w a history; rfl
    | yield b => exact ih b

theorem peerFinish_projects (ρ : E → Option F)
    (sg : {α : Type} → WG.M α → WGPrefix E α)
    (st : {α : Type} → WG.M α → WGPrefix F α)
    (gg kg : PeerId → WGPrefix E Unit) (gt kt : PeerId → WGPrefix F Unit)
    (og : PeerAttrs → Option PeerId → Int → WGPrefix E Int)
    (ot : PeerAttrs → Option PeerId → Int → WGPrefix F Int)
    (step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (sg action) (st action))
    (staging : ∀ pid, StateProjectsPrefix ρ id (gg pid) (gt pid))
    (keepalive : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid))
    (out : ∀ attrs peer ret, StateProjectsPrefix ρ id (og attrs peer ret) (ot attrs peer ret))
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateProjectsPrefix ρ id (peerFinishWith sg gg kg og attrs peer pid ret)
      (peerFinishWith st gt kt ot attrs peer pid ret) := by
  unfold peerFinishWith
  repeat' first
    | exact step _
    | exact staging _
    | exact keepalive _
    | exact out _ _ _
    | handshake_worker_project_step ρ

theorem open_projects (ρ : E → Option F)
    (sg : {α : Type} → WG.M α → WGPrefix E α)
    (st : {α : Type} → WG.M α → WGPrefix F α)
    (gg kg : PeerId → WGPrefix E Unit) (gt kt : PeerId → WGPrefix F Unit)
    (step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (sg action) (st action))
    (staging : ∀ pid, StateProjectsPrefix ρ id (gg pid) (gt pid))
    (keepalive : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) :
    StateProjectsPrefix ρ id (openWith sg gg kg) (openWith st gt kt) := by
  unfold openWith
  repeat' first
    | exact step _
    | exact staging _
    | exact keepalive _
    | (maintenance_head ForIn.forIn; apply loop_projects ρ)
    | handshake_worker_project_step ρ

end Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
