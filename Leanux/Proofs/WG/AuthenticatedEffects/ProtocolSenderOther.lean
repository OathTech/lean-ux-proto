import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSenderOps
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsOther

/-! Other projections discard the new wire receipts and the HC markers while
retaining their supplied session/keepalive observers on the same source run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSender
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

theorem receive_other (ρ : E → Option F)
    (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (quiet : ∀ event, ρ (record event) = none)
    (sg : PeerId → WGPrefix E Bool) (st : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (kt : PeerId → WGPrefix F Unit)
    (hs : ∀ pid, StateProjectsPrefix ρ id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix ρ id (kg pid) (kt pid)) (mac : HandshakeMac)
    (socket : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (cookie : CookieSocket.Receipt → E)
    (socketQuiet : ∀ receipt, ρ (socket receipt) = none)
    (cookieQuiet : ∀ receipt, ρ (cookie receipt) = none) :
    HandshakeWorker.OpsProjects ρ (receiveOps record decode sg kg mac socket scope cookie)
      (HandshakeWorker.ops st kt) :=
  {HandshakeEffects.observedOps_other record decode ρ quiet sg st kg kt hs hk mac with
    send := fun pid msg =>
      (pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved.«0».Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorker.callback_projects)
        record ρ quiet .send pid _ _ (ProtocolSocket.observed_ignored ρ socket socketQuiet scope pid msg)
    cookie := fun msg src => CookieSocket.observed_ignored ρ cookie cookieQuiet mac msg src}

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSender
