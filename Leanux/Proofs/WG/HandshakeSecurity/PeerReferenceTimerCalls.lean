import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTimerFrames

/-! Native timer callers preserve positive resident peer references. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem traversal (pid : PeerId) :
    Framing.Preserves Inv (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' peer_reference_timer_step

theorem complete (pid : PeerId) (site : HiddenSite) :
    Framing.Preserves Inv (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' peer_reference_timer_step

theorem data_received (pid : PeerId) :
    Framing.Preserves Inv (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' peer_reference_timer_step

theorem data_sent (pid : PeerId) :
    Framing.Preserves Inv (timersDataSent pid) := by
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_timer_step

theorem initiated (pid : PeerId) :
    Framing.Preserves Inv (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated

  repeat' peer_reference_timer_step

theorem derived (pid : PeerId) :
    Framing.Preserves Inv (timersSessionDerived pid) := by
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' peer_reference_timer_step

theorem sent (pid : PeerId) :
    Framing.Preserves Inv (timersAnyAuthenticatedPacketSent pid) :=
  del_timer pid .sendKeepalive

theorem received (pid : PeerId) :
    Framing.Preserves Inv (timersAnyAuthenticatedPacketReceived pid) :=
  del_timer pid .newHandshake

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
