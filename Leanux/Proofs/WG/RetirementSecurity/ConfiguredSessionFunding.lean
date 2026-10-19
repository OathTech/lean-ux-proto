import Leanux.Proofs.WG.RetirementSecurity.SessionPeerFunding
import Leanux.Proofs.WG.Origins.ConfiguredSession

/-! Normal native session publication selects a live configured peer. Its base
reference is derived from the existing configured registry and actual funded
base list; the caller need not assume an independent selected-slot premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

variable {holders : DurableHolders} {w v : WGWorld} {d : Device} {p : Peer}

theorem live_peer_base_reference (funded : holders.Funded carriers loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (device : w.dev = some d) (stored : d.peers[pid]? = some p)
    (alive : p.isDead = false) :
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base := by
  have registry := configured (ConfiguredIdentity.state d) (by simp [ConfiguredIdentity.view,device])
  have row := registry.live pid (ConfiguredIdentity.cell p)
    (by simp [ConfiguredIdentity.state,stored]) alive (by simp)
  apply base_peer_reference funded _ device stored
  rw [funded.aligned.base]
  exact coherent.2 (p.remoteStatic,pid) (by simpa [BaseCoherence.rows,ConfiguredIdentity.state,ConfiguredIdentity.cell,device] using row)

/-- Actual session refusal changes no state, and a normal publication has passed
its native live-peer check. Registry completeness therefore supplies the
independent base reference needed to protect every newly published key slot. -/
theorem SlotPeerReferences.session_configured
    (before : SlotPeerReferences holders loans w)
    (funded : holders.Funded carriers loans w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (pid : PeerId) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    SlotPeerReferences holders loans v := by
  have source := run
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at source
  obtain ⟨context,middle,middleAmbient,frontRun,tailRun⟩ := source
  cases context with
  | none =>
    cases tailRun
    exact (Origins.front_none pid w v a b frontRun) ▸ before
  | some ctx =>
    obtain ⟨d,device,stored,row,_,_⟩ := ConfiguredSession.front_configured pid ctx w middle v
      a middleAmbient b result configured frontRun tailRun
    apply before.session_from_base funded _ a b run
    rw [funded.aligned.base]
    exact coherent.2 (ctx.peer.remoteStatic,pid) (by simpa [BaseCoherence.rows,ConfiguredIdentity.state,ConfiguredIdentity.cell,device] using row)

end Leanux.Proofs.WG.RetirementSecurity
