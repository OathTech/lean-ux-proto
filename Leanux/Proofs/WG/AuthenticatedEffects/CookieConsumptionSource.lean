import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration

/-! A completed native cookie-consumer cut in the actual hsCookie arm.
The existing MAC-qualified receive suffix is unchanged; decorating its Ops
would miss this earlier branch. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumption
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

structure Receipt where
  input : Key
  run : WGRunWitness Unit

def Receipt.Valid (r : Receipt) : Prop := r.run.Valid (cookieMessageConsume r.input)

def observed (record : Receipt → E) (msg : Key) : WGPrefix E Unit :=
  receiptWGObserved (liftWGPrefix (cookieMessageConsume msg)) (fun run => record ⟨msg,run⟩)

def receiveWith (cookie : Key → WGPrefix E Unit) (make : HandshakeMac → Ops (WGPrefix E))
    (msg : Key) (src : SkbSource) : WGPrefix E Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    cookie msg
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (make ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

def workerWith (cookie : Key → WGPrefix E Unit) (make : HandshakeMac → Ops (WGPrefix E)) : WGPrefix E Bool :=
  HandshakeWorker.workerWith (receiveWith cookie make)

theorem receive_native (make : HandshakeMac → Ops (WGPrefix E)) (msg : Key) (src : SkbSource) :
    receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg)) make msg src =
      HandshakeWorker.receiveWith make msg src := rfl

theorem worker_native (make : HandshakeMac → Ops (WGPrefix E)) :
    workerWith (fun msg => liftWGPrefix (cookieMessageConsume msg)) make =
      HandshakeWorker.observedWith make := rfl

theorem observed_erases (record : Receipt → E) (msg : Key) :
    ErasesStatePrefix (observed record msg) (cookieMessageConsume msg) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem observed_projects (ρ : E → Option F) (record : Receipt → E)
    (quiet : ∀ r, ρ (record r) = none) (msg : Key) :
    StateProjectsPrefix ρ id (observed record msg) (liftWGPrefix (cookieMessageConsume msg)) :=
  HandshakeSecurity.Exchange.receipt_ignored ρ _ _ _
    (by handshake_worker_project_step ρ) (fun _ => quiet _)

theorem observed_matching (ρ : E → Option F) (record : Receipt → E) (target : Receipt → F)
    (matching : ∀ r, ρ (record r) = some (target r)) (msg : Key) :
    StateProjectsPrefix ρ id (observed record msg) (observed target msg) :=
  HandshakeSecurity.Exchange.receipt_projects ρ _ _ _ _
    (by handshake_worker_project_step ρ) (fun _ => matching _)

theorem receive_projects (ρ : E → Option F)
    (cookie : Key → WGPrefix E Unit) (cookie' : Key → WGPrefix F Unit)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (hc : ∀ msg, StateProjectsPrefix ρ id (cookie msg) (cookie' msg))
    (h : ∀ mac, HandshakeWorker.OpsProjects ρ (g mac) (t mac)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receiveWith cookie g msg src) (receiveWith cookie' t msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact hc _
    | (maintenance_head afterMacWith; exact HandshakeWorker.afterMac_projects ρ _ _ (h _) _ _ _ _)
    | (maintenance_head captureWGRun; exact
        (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.capture_self) ρ _)
    | handshake_worker_project_step ρ

theorem worker_projects (ρ : E → Option F)
    (cookie : Key → WGPrefix E Unit) (cookie' : Key → WGPrefix F Unit)
    (g : HandshakeMac → Ops (WGPrefix E)) (t : HandshakeMac → Ops (WGPrefix F))
    (hc : ∀ msg, StateProjectsPrefix ρ id (cookie msg) (cookie' msg))
    (h : ∀ mac, HandshakeWorker.OpsProjects ρ (g mac) (t mac)) :
    StateProjectsPrefix ρ id (workerWith cookie g) (workerWith cookie' t) :=
  HandshakeWorker.worker_projects ρ _ _ (receive_projects ρ cookie cookie' g t hc h)

theorem observed_completed (record : Receipt → E) (msg : Key)
    (w v : WGWorld) (a b : Ambient) (history : List E)
    (run : ((cookieMessageConsume msg).run w).run a = .ok (((),v),b)) :
    runWGPrefix (observed record msg) w a history =
      (.ok (((),v),b),history ++ [record ⟨msg,⟨(),w,v,a,b⟩⟩]) := by
  rw [observed,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

theorem observed_appends (record : Receipt → E) (msg : Key) : StateAppends (observed record msg) :=
  (StateAppends.lift _).receiptWGObserved _

end Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumption
