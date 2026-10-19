import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimerFrames

/-! Native timer callers retain the allocation-indexed replay archive. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem traversal (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' archive_timer_step history

theorem complete (pid : PeerId) (site : HiddenSite) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' archive_timer_step history

theorem data_received (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' archive_timer_step history

theorem data_sent (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersDataSent pid) := by
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' archive_timer_step history

theorem initiated (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated

  repeat' archive_timer_step history

theorem derived (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersSessionDerived pid) := by
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' archive_timer_step history

theorem sent (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersAnyAuthenticatedPacketSent pid) :=
  del_timer pid .sendKeepalive history

theorem received (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (timersAnyAuthenticatedPacketReceived pid) :=
  del_timer pid .newHandshake history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
