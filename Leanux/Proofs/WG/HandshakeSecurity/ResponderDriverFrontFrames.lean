import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverPollFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining ConfiguredTraffic Packets

theorem carrier_lookup (family addr : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (lookupDst family addr) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.lookupDst_view) family addr)
    (native_join (authorization_of_frames (pool_of_material (lookupDst_material family addr))
      (keyEffects_view (project := id) (allowed := NoPromotion) (lookupDst_keyView family addr)) confirmed)
      (CurrentSlots.view_preserves (project := id)
        ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.lookupDst_view) family addr)))

theorem carrier_trim (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (xmitTrim pid) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitTrim_view) pid)
    (native_join (authorization_of_frames (pool_of_material (xmitTrim_material pid))
      (keyEffects_view (project := id) (allowed := NoPromotion) (xmitTrim_keyView pid)) confirmed)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.trim_preserves) pid))

theorem carrier_splice (pid : PeerId) (packets : List WG.Packet) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (xmitSplice pid packets) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.xmitSplice_view) pid packets)
    (native_join (authorization_of_frames (pool_of_material (xmitSplice_material pid packets))
      (keyEffects_view (project := id) (allowed := NoPromotion) (xmitSplice_keyView pid packets)) confirmed)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotStack.«0».Leanux.Proofs.WG.CurrentSlots.splice_preserves) pid packets))

theorem carrier_tx_front (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (txFront family addr packets mtu) := by
  unfold txFront txCheck txSelect txError txHeaders txWalk WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact carrier_lookup _ _ confirmed)
    | (rx_retention_head xmitTrim; exact carrier_trim _ confirmed)
    | (rx_retention_head xmitSplice; exact carrier_splice _ _ confirmed)
    | (rx_retention_head loopbackSend; exact carrier_store (loopbackSend_kernel _ _) confirmed)
    | (allocation_release_lift_from Net.M; exact carrier_store (liftRouting_sameWGStore _) confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Framing.Preserves (Carrier confirmed) _)
    | responder_carrier_poll_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
