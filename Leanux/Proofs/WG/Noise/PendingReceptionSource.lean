import Leanux.Proofs.WG.Noise.PendingReceptionFrames
import Leanux.Proofs.WG.Noise.PendingObserverSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingReception
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues ConfiguredReceive

theorem responseCaller_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendHandshakeResponse pid) := by
  rw [← Origins.HandshakeSources.response_original]
  unfold Origins.HandshakeSources.responseWith Origins.HandshakeSources.original
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact create _ seen)
    | (rx_retention_head addMacToPacket; exact mac _ _ seen)
    | (rx_retention_head beginSession
       exact (hoare_iff_run_ambient _ _ _).mpr (PendingSession.native _ seen))
    | (rx_retention_head timersSessionDerived; exact derived _ seen)
    | (rx_retention_head timersTraversal; exact traversal _ seen)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _ seen)
    | (rx_retention_head sendBufferToPeer; exact send _ _ seen)
    | pending_native_step seen

theorem afterMac_native (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (state : MacState) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (Cookies.afterMac msg src loaded state) := by
  rw [← Origins.HandshakeSources.afterMac_original]
  unfold Origins.HandshakeSources.afterMacWith
  simp only [Origins.HandshakeSources.response_original]
  unfold Origins.HandshakeSources.original
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact initiation _ seen)
    | (rx_retention_head consumeResponse; exact response _ seen)
    | (rx_retention_head sendHandshakeResponse; exact responseCaller_native _ seen)
    | (rx_retention_head beginSession
       exact (hoare_iff_run_ambient _ _ _).mpr (PendingSession.native _ seen))
    | (rx_retention_head sendHandshakeCookie; exact sendCookie _ _ seen)
    | (rx_retention_head setPeerEndpointFromSkb; exact endpoint _ _ seen)
    | (rx_retention_head timersSessionDerived; exact derived _ seen)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _ seen)
    | (rx_retention_head sendKeepalive; exact keepalive _ seen)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _ seen)
    | (rx_retention_head timersTraversal; exact traversal _ seen)
    | (rx_retention_head peerPut; exact pay _ seen)
    | pending_native_step seen

theorem reception_native (msg : List UInt8) (src : SkbSource) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (receiveHandshakePacket msg src) := by
  rw [← Origins.HandshakeSources.reception_original]
  unfold Origins.HandshakeSources.receptionWith
  simp only [Origins.HandshakeSources.afterMac_original]
  unfold Origins.HandshakeSources.original
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact cookieConsume _ seen)
    | (rx_retention_head Cookies.loadPhase; exact native_store _ Cookies.loadPhase_sameStore seen)
    | (rx_retention_head cookieValidatePacket
       exact native_cookie _ (cookieValidatePacket_sameCookie _ _ _) seen)
    | (rx_retention_head Cookies.afterMac; exact afterMac_native _ _ _ _ seen)
    | pending_native_step seen

theorem receiveStep_native (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) WG.receiveStep := by
  rw [← Origins.HandshakeSources.step_original]
  unfold Origins.HandshakeSources.stepWith
  simp only [Origins.HandshakeSources.reception_original]
  unfold Origins.HandshakeSources.original
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact reception_native _ _ seen)
    | pending_native_step seen


end Leanux.Proofs.WG.Noise.PendingReception

namespace Leanux.Proofs.WG.Noise.PendingReception
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues ConfiguredReceive

/-- This specialization is exact for the original Origins observer. Focus
retains incoming RX events while adding no consumed-event labels. -/
theorem observed {α : Type} (g : PrefixM Origins.Event α) (action : WG.M α)
    (erases : ErasesPrefix g (liftWG action))
    (normal : ∀ seen, Preserves (fun w => PendingSession.NativeInv w seen) action) :
    PrefixPreserves PendingSession.StateInv PendingSession.HistorySafe
      (Origins.HistoryAdapters.focus g) :=
  PendingSession.observer _ _ (Appends.focus _ _ _) (focusPrefix_erases _ _ erases)
    (Origins.HistoryAdapters.focus_other CounterConsume.eventLabel
      (by intro e; cases e <;> rfl) g)
    (PendingSession.native_product action normal)

theorem responseCaller (pid : PeerId) :
    PrefixPreserves PendingSession.StateInv PendingSession.HistorySafe
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localResponse pid)) :=
  observed _ _ (Origins.HistoryAdapters.localResponse_erases pid) (responseCaller_native pid)

theorem reception (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves PendingSession.StateInv PendingSession.HistorySafe
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localReception msg src)) :=
  observed _ _ (Origins.HistoryAdapters.localReception_erases msg src) (reception_native msg src)

/-- One actual receive-worker step, including empty queue, dequeue, every
handshake caller branch, and the final queue-length decrement. -/
theorem receiveStep :
    PrefixPreserves PendingSession.StateInv PendingSession.HistorySafe
      Origins.HistoryAdapters.receiveStep :=
  observed _ _ Origins.HistoryAdapters.localStep_erases receiveStep_native

end Leanux.Proofs.WG.Noise.PendingReception
