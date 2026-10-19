import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.CookieSocketSource
import Leanux.Proofs.WG.AuthenticatedEffects.SendEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsNatural

/-! Only the two native protocol-send leaves gain socket receipts. Existing
consumer, exchange, session and causal callback observations remain in place. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSender
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

def sendOps (record : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) : HandshakeSecurity.SendExchange.Ops (WGPrefix E) :=
  {SendEffects.native with send := ProtocolSocket.observed record scope}

theorem send_projects (ρ : E → Option F)
    (record : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause))
    (quiet : ∀ receipt, ρ (record receipt) = none) :
    HandshakeSecurity.SendExchange.Ops.Projects ρ (sendOps record scope) SendEffects.native :=
  {SendEffects.native_projects ρ with
    send := fun pid msg => ProtocolSocket.observed_ignored ρ record quiet scope pid msg}

def receiveOps (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit)
    (mac : HandshakeMac)
    (socket : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (cookie : CookieSocket.Receipt → E) : Ops (WGPrefix E) :=
  {HandshakeWorker.observedOps record decode session keepalive mac with
    send := fun pid msg => HandshakeWorker.callback record .send pid (ProtocolSocket.observed socket scope pid msg)
    cookie := CookieSocket.observed cookie mac}

theorem receive_projects (ρ : E → Option F)
    (eg : HandshakeCausal.Event → E) (dg : E → Option HandshakeCausal.Event)
    (et : HandshakeCausal.Event → F) (dt : F → Option HandshakeCausal.Event)
    (enc : ∀ event, ρ (eg event) = some (et event)) (dec : ∀ event, dg event = (ρ event).bind dt)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac)
    (socket : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (cookie : CookieSocket.Receipt → E)
    (socketQuiet : ∀ receipt, ρ (socket receipt) = none)
    (cookieQuiet : ∀ receipt, ρ (cookie receipt) = none) :
    HandshakeWorker.OpsProjects ρ (receiveOps eg dg sg kg mac socket scope cookie)
      (HandshakeWorker.observedOps et dt st kt mac) := by
  refine {HandshakeEffects.observedOps_natural ρ eg dg et dt enc dec sg st kg kt hs hk mac with
    send := ?_, cookie := ?_}
  · intro pid msg
    change StateProjectsPrefix ρ id (HandshakeWorker.callback eg .send pid (ProtocolSocket.observed socket scope pid msg))
      (HandshakeWorker.old et dt (HandshakeCausal.call .send pid (sendBufferToPeer pid msg)))
    rw [HandshakeEffects.old_call]
    exact HandshakeEffects.callback_projects ρ eg et enc .send pid _ _
      (ProtocolSocket.observed_ignored ρ socket socketQuiet scope pid msg)
  · intro msg src
    exact CookieSocket.observed_ignored ρ cookie cookieQuiet mac msg src

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSender
