import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric

/-! Actual final-release cuts in the existing handshake and queued-send
callbacks. Other callback journals are retained; the target's native repayment
is an explicit local projection premise, not an initialized lifetime claim. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Decoration
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

def release (record : Event → E) (decode : E → Option Event) (peer : Option PeerId) : WGPrefix E Unit :=
  focusStatePrefix record decode (releaseObserved peer)

theorem release_projects (record : Event → E) (decode : E → Option Event)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (release record decode peer) (liftWGPrefix (peerPut peer)) :=
  Exchange.quiet_native_projection ρ _ _
    (focusStatePrefix_erases record decode (release_erases peer))
    (fun w => focusPrefix_other record decode ρ quiet ((releaseObserved peer).run w))

def send (record : Event → E) (decode : E → Option Event)
    (base : SendExchange.Ops (WGPrefix E)) : SendExchange.Ops (WGPrefix E) :=
  {base with put := release record decode}

theorem send_projects (record : Event → E) (decode : E → Option Event)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    {base : SendExchange.Ops (WGPrefix E)} {target : SendExchange.Ops (WGPrefix F)}
    (projected : SendExchange.Ops.Projects ρ base target)
    (native : ∀ peer, target.put peer = liftWGPrefix (peerPut peer)) :
    SendExchange.Ops.Projects ρ (send record decode base) target := by
  refine {projected with put := ?_}
  intro peer
  rw [native]
  exact release_projects record decode ρ quiet peer

def receive (record : Event → E) (decode : E → Option Event)
    (base : Origins.HandshakeSources.Ops (WGPrefix E)) : Origins.HandshakeSources.Ops (WGPrefix E) :=
  {base with put := release record decode}

theorem receive_projects (record : Event → E) (decode : E → Option Event)
    (ρ : E → Option F) (quiet : ∀ event, ρ (record event) = none)
    {base : Origins.HandshakeSources.Ops (WGPrefix E)} {target : Origins.HandshakeSources.Ops (WGPrefix F)}
    (projected : HandshakeWorker.OpsProjects ρ base target)
    (native : ∀ peer, target.put peer = liftWGPrefix (peerPut peer)) :
    HandshakeWorker.OpsProjects ρ (receive record decode base) target := by
  refine {projected with put := ?_}
  intro peer
  rw [native]
  exact release_projects record decode ρ quiet peer

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Decoration
