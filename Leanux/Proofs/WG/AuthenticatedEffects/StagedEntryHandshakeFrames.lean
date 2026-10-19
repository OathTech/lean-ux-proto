import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEndpointFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedSocketSendFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeSendFrames

/-! Native protocol-send and handshake maintenance retain the complete entry
view. Socket frames include packet allocation bounds, staged payloads and
ordered TX ownership, not merely the encryption-ring projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem socket4 e cache bytes ds exactRx : SameView StagedEntry.view (send4 e cache bytes ds exactRx) :=
  TimerFrames.combine
    (PacketOrigins.epoch_ring ((OccurrenceHandshake.socket4_wire e cache bytes ds exactRx).factor Prod.fst))
    (Staged.Exact.send4_staged e cache bytes ds exactRx)
    (AllocatedObligation.CompletionGeometry.send4_geometry e cache bytes ds exactRx)
    (OccurrenceHandshake.socket4_contents e cache bytes ds exactRx)

theorem socket6 e cache bytes ds exactRx : SameView StagedEntry.view (send6 e cache bytes ds exactRx) :=
  TimerFrames.combine
    (PacketOrigins.epoch_ring ((OccurrenceHandshake.socket6_wire e cache bytes ds exactRx).factor Prod.fst))
    (Staged.Exact.send6_staged e cache bytes ds exactRx)
    (AllocatedObligation.CompletionGeometry.send6_geometry e cache bytes ds exactRx)
    (OccurrenceHandshake.socket6_contents e cache bytes ds exactRx)

theorem cookie_frame {action : WG.M α} (same : SameCookie action) : SameView StagedEntry.view action := by
  apply same.of_factor (fun s : WGOwnedView => StagedEntry.view {dev := s.dev}) StagedEntry.view
  intro w
  cases w with
  | mk dev => cases dev <;> rfl

theorem update_then (pid : PeerId) (f : Peer → Peer) (next : Peer → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ p, SameView StagedEntry.view (next p)) :
    SameView StagedEntry.view (getPeer pid >>= fun p => setPeer pid (f p) >>= fun _ => next p) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,rest⟩ := run
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,q,d,write,finish⟩ := rest
  have performed : (((getPeer pid >>= fun p => setPeer pid (f p)).run w).run a) = .ok ((ignored,q),d) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,u,c,read,write⟩
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp (tail p) q d value v b finish).trans
    ((ProjectedAction.iff_run_ambient _ _ _).mp (Queued.update pid f same) w a ignored q d performed)

macro "entry_handshake_native_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head send4; exact socket4 _ _ _ _ _ $initial)
  | (rx_retention_head send6; exact socket6 _ _ _ _ _ $initial)
  | (rx_retention_head makeCookie; exact cookie_frame (makeCookie_sameCookie _) $initial)
  | (rx_retention_head setPeerEndpoint; exact EndpointFrames.set _ _ $initial)
  | (rx_retention_head delTimer; exact TimerFrames.delete _ _ $initial)
  | (rx_retention_head hiddenAlloc; unfold hiddenAlloc; exact hoare_liftAmbient _ _)
  | (rx_retention_head hidden; unfold hidden; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; exact TimerFrames.branch_frame _ _ $initial)
  | (rx_retention_head endpointFromSkb; exact TimerFrames.store (endpointFromSkb_sameWGStore _) $initial)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => StagedEntry.view w = $initial))
  | entry_key_step $initial)

theorem create_response (pid : PeerId) : SameView StagedEntry.view (createResponse pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' entry_handshake_native_step initial

theorem add_mac (pid : PeerId) (msg : Key) : SameView StagedEntry.view (addMacToPacket pid msg) := by
  unfold addMacToPacket
  dsimp only
  apply update_then
  · intro p; exact ⟨rfl,rfl,rfl⟩
  intro peer initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold WG.andM
  repeat' entry_handshake_native_step initial

theorem buffer (pid : PeerId) (msg : Key) : SameView StagedEntry.view (sendBufferToPeer pid msg) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' entry_handshake_native_step initial

theorem cookie (msg : Key) (src : SkbSource) : SameView StagedEntry.view (sendHandshakeCookie msg src) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold sendHandshakeCookie cookieMessageCreate sendBufferAsReplyToSkb
  repeat' entry_handshake_native_step initial

theorem sent (pid : PeerId) : SameView StagedEntry.view (timersAnyAuthenticatedPacketSent pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold timersAnyAuthenticatedPacketSent
  repeat' entry_handshake_native_step initial

theorem received (pid : PeerId) : SameView StagedEntry.view (timersAnyAuthenticatedPacketReceived pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold timersAnyAuthenticatedPacketReceived
  repeat' entry_handshake_native_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeFrames
