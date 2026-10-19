import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointFrames

/-! The actual MAC-check capture and cookie branch project to the initialized
exchange driver's original receive source. This compares retained journals,
not two independent executions whose final states happen to agree. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
open AuthenticatedEffects
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

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
    (g : HandshakeMac → Ops (WGPrefix E)) (target : Ops (WGPrefix F))
    (step : ∀ {α} (a : WG.M α), target.step a = liftWGPrefix a)
    (cookie : ∀ msg, target.cookieConsume msg = liftWGPrefix (cookieMessageConsume msg))
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac) target)
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix rho id (HandshakeWorker.receiveWith g msg src)
      (receptionWith target msg src) := by
  unfold HandshakeWorker.receiveWith receptionWith
  simp only [step,cookie]
  apply StateProjectsPrefix.bind rho id id
  · handshake_worker_project_step rho
  · intro isCookie
    dsimp only [id]
    split
    · apply StateProjectsPrefix.bind rho id id
      · handshake_worker_project_step rho
      · intro doneValue; handshake_worker_project_step rho
    · apply StateProjectsPrefix.bind rho id id
      · handshake_worker_project_step rho
      · intro loaded
        apply StateProjectsPrefix.bind rho WGRunWitness.value id (capture_value rho _)
        intro checked
        exact HandshakeWorker.afterMac_projects rho _ _ (base _) _ _ _ _

theorem worker_target (rho : E → Option F)
    (g : HandshakeMac → Ops (WGPrefix E)) (target : Ops (WGPrefix F))
    (step : ∀ {α} (a : WG.M α), target.step a = liftWGPrefix a)
    (cookie : ∀ msg, target.cookieConsume msg = liftWGPrefix (cookieMessageConsume msg))
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac) target) :
    StateProjectsPrefix rho id (HandshakeWorker.observedWith g) (stepWith target) := by
  have factor : stepWith target = HandshakeWorker.workerWith (receptionWith target) := by
    unfold stepWith HandshakeWorker.workerWith
    simp only [step]
    rfl
  rw [factor]
  exact HandshakeWorker.worker_projects rho _ _ (receive_target rho g target step cookie base)

theorem worker_exchange (rho : E → Option Exchange.Event)
    (g : HandshakeMac → Ops (WGPrefix E))
    (session : PeerId → WGPrefix Exchange.Event Bool) (keepalive : PeerId → WGPrefix Exchange.Event Unit)
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac) (ExchangeDriver.receiveOps session keepalive)) :
    StateProjectsPrefix rho id (HandshakeWorker.observedWith g) (ExchangeDriver.worker session keepalive) :=
  worker_target rho g _ (fun _ => rfl) (fun _ => rfl) base

theorem observed_worker_exchange (decodeExchange : E → Option Exchange.Event)
    (recordExchange : Exchange.Event → E)
    (matching : ∀ event, decodeExchange (recordExchange event) = some event)
    (recordHC : HandshakeCausal.Event → E) (decodeHC : E → Option HandshakeCausal.Event)
    (quietHC : ∀ event, decodeExchange (recordHC event) = none)
    (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix Exchange.Event Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix Exchange.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix decodeExchange id (sg pid) (sa pid))
    (hk : ∀ pid, StateProjectsPrefix decodeExchange id (kg pid) (ka pid)) :
    StateProjectsPrefix decodeExchange id
      (HandshakeWorker.observedWith (fun mac => receiveOps recordExchange
        (HandshakeWorker.observedOps recordHC decodeHC sg kg mac)))
      (ExchangeDriver.worker sa ka) :=
  worker_exchange decodeExchange _ sa ka (fun mac =>
    receive_native decodeExchange recordExchange matching _ sa ka
      (observed_ops_native recordHC decodeHC decodeExchange quietHC sg sa kg ka hs hk mac))

/-- The completed consumer/create receipts augment the existing authenticated
callbacks; dropping only those receipts recovers the previous worker journal. -/
theorem worker_ignored (rho : E → Option F) (record : Exchange.Event → E)
    (quiet : ∀ event, rho (record event) = none)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (base : ∀ mac, HandshakeWorker.OpsProjects rho (g mac) (t mac)) :
    StateProjectsPrefix rho id
      (HandshakeWorker.observedWith (fun mac => receiveOps record (g mac)))
      (HandshakeWorker.observedWith t) :=
  HandshakeWorker.observedWith_projects rho _ _
    (fun mac => receive_ignored rho record quiet _ _ (base mac))

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
