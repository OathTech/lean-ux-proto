import Leanux.Proofs.WG.TransmitSecurity.StagedNativeSupportFrames

/-! Source decomposition for native staged-queue frames. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

macro "staged_origin_native" : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply Native.update_peer_bind
     · intro p; exact ⟨rfl,rfl⟩
     intro x)
  | (receive_update_head setPeer; apply Native.update_peer; intro p; exact ⟨rfl,rfl⟩)
  | (rx_retention_head getPeer; exact Native.read_peer _)
  | (rx_retention_head getKeypair; exact Native.read_key _)
  | (rx_retention_head getDev; exact Native.store getDev_sameWGStore)
  | (rx_retention_head modifyDev; apply Native.modify_device <;> intro d <;> rfl)
  | (rx_retention_head peerGet; exact Native.peer_get _)
  | (rx_retention_head peerPut; exact Native.peer_put _)
  | (rx_retention_head createResponse; exact Native.create_response _)
  | (rx_retention_head createInitiation; exact Native.create_initiation _)
  | (rx_retention_head addMacToPacket; exact Native.add_mac _ _)
  | (rx_retention_head sendBufferToPeer; exact Native.send_buffer _ _)
  | (rx_retention_head setPeerEndpointFromSkb; exact Native.endpoint_from_skb _ _)
  | (rx_retention_head timersHandshakeComplete; exact Native.handshake_complete _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketSent; exact Native.delete_timer _ _)
  | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact Native.delete_timer _ _)
  | (rx_retention_head sendHandshakeCookie; exact Native.cookie_reply _ _)
  | (rx_retention_head cookieMessageConsume; exact Native.cookie_consume _)
  | (rx_retention_head Cookies.loadPhase; exact Native.store Cookies.loadPhase_sameStore)
  | (rx_retention_head cookieValidatePacket; exact Native.cookie (cookieValidatePacket_sameCookie _ _ _))
  | (rx_retention_head WG.andM; unfold WG.andM)
  | (rx_retention_head WG.orM; unfold WG.orM)
  | (rx_retention_head hiddenClock64; unfold hiddenClock64)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp _)
  | (rx_retention_head branchCmp; unfold branchCmp; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; unfold branch; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head hidden | rx_retention_head invariant | rx_retention_head unsupported | rx_retention_head getAmbient
     first | unfold hidden | unfold invariant | unfold unsupported | unfold getAmbient
     exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)


end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
