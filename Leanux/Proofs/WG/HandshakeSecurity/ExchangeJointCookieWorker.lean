import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointWorker

/-! Exact cookie-callback projection through the native handshake branch and
MAC-check capture, retaining the source journal on stopped executions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCookieJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources AuthenticatedEffects

private theorem capture_value (rho : E → Option F) (action : WG.M α) :
    StateProjectsPrefix rho WGRunWitness.value (captureWGRun action) (liftWGPrefix action) := by
  intro w a h
  change ((action.run w).run a,h.filterMap rho) =
    ((runWGPrefix (captureWGRun action) w a h).1.map (fun ((x,v),b) => ((x.value,v),b)),
      (runWGPrefix (captureWGRun action) w a h).2.filterMap rho)
  rw [runWGPrefix_captureWGRun]
  cases run : (action.run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨x,v⟩,b⟩; rfl

theorem receive_target (rho : E → Option F)
    (cookieSource : Key → WGPrefix E Unit)
    (g : HandshakeMac → Ops (WGPrefix E)) (target : Ops (WGPrefix F))
    (step : ∀ {α} (a : WG.M α), target.step a = liftWGPrefix a)
    (cookie : ∀ msg, StateProjectsPrefix rho id (cookieSource msg) (target.cookieConsume msg))
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac)
      {target with cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)})
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix rho id (CookieConsumption.receiveWith cookieSource g msg src)
      (receptionWith target msg src) := by
  unfold CookieConsumption.receiveWith receptionWith
  simp only [step]
  apply StateProjectsPrefix.bind rho id id
  · handshake_worker_project_step rho
  · intro isCookie
    dsimp only [id]
    split
    · apply StateProjectsPrefix.bind rho id id
      · exact cookie msg
      · intro doneValue; handshake_worker_project_step rho
    · apply StateProjectsPrefix.bind rho id id
      · handshake_worker_project_step rho
      · intro loaded
        apply StateProjectsPrefix.bind rho WGRunWitness.value id (capture_value rho _)
        intro checked
        exact HandshakeWorker.afterMac_projects rho _ _ (base _) _ _ _ _

theorem worker_target (rho : E → Option F)
    (cookieSource : Key → WGPrefix E Unit)
    (g : HandshakeMac → Ops (WGPrefix E)) (target : Ops (WGPrefix F))
    (step : ∀ {α} (a : WG.M α), target.step a = liftWGPrefix a)
    (cookie : ∀ msg, StateProjectsPrefix rho id (cookieSource msg) (target.cookieConsume msg))
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac)
      {target with cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)}) :
    StateProjectsPrefix rho id (CookieConsumption.workerWith cookieSource g) (stepWith target) := by
  have factor : stepWith target = HandshakeWorker.workerWith (receptionWith target) := by
    unfold stepWith HandshakeWorker.workerWith
    simp only [step]
    rfl
  rw [factor]
  exact HandshakeWorker.worker_projects rho _ _ (receive_target rho cookieSource g target step cookie base)

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCookieJoint
