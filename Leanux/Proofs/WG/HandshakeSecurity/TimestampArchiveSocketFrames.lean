import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveReceiveFrames

/-! Native socket sends and cookie maintenance preserve timestamp history.
Cached endpoint writes use their actual saved peer read. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 800000

theorem cookie_frame {action : WG.M α} (same : Cookies.NoNoiseChange action)
    (history : List TimestampReceipt) : Framing.Preserves (StateInv history) action := by
  apply frame history action
  · apply Freshness.of_view
    apply same.of_factor (fun s => fun pid =>
      (s.1.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp))
    intro w
    simp only [Cookies.noiseView,Cookies.viewOfStore,wgStoreView,Option.bind_map]
    rfl
  · exact same.factor (fun s => s.2.1)

theorem cache_get (pid : PeerId) (gen : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (dstCacheGet pid gen) := by
  let P := StateInv history
  let R := fun p w => P w ∧ Responder.SavedNativePeer pid p w
  have finish (p : Peer) : Hoare (do
      let ts ← hiddenJiffies .dstCacheRefreshTs
      setPeer pid {p with dstCache := {p.dstCache with slot := none,refreshTs := ts}}
      Pure.pure none : WG.M (Option DstSlot)) (R p) (fun _ => P) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenJiffies .dstCacheRefreshTs) (R p))
    intro ts
    apply hoare_bind _ _ (write_saved pid p
      (fun current => {current with dstCache := {current.dstCache with slot := none,refreshTs := ts}})
      (fun _ => ⟨rfl,rfl⟩) history)
    intro _
    exact preserves_pure _
  unfold dstCacheGet getAmbient
  apply preserves_bind (hoare_liftAmbient (get : AmbientM Ambient) P)
  intro a
  apply preserves_bind (hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2))
  intro w
  split
  · exact preserves_pure _
  · apply hoare_bind _ _ (read_saved pid history)
    intro p
    cases slot_eq : p.dstCache.slot with
    | none => simpa only [slot_eq] using finish p
    | some slot =>
      simp only [slot_eq]
      split
      · exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
      · exact finish p

theorem cache_set (pid : PeerId) (src gen dev : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (dstCacheSet pid src gen dev) :=
  update_peer pid (fun p => {p with dstCache := {p.dstCache with slot := some {src,gen,dev}}})
    (fun _ => ⟨rfl,rfl⟩) history

theorem tunnel (ep : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route)
    (exactRx : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history)
      ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) ep bytes ds route exactRx) := by
  index_unfold _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
  simp (config := {zeta := false}) only [unsupported,skipCut]
  repeat' first
    | (rx_retention_head loopbackSend; exact frame_store history _ (loopbackSend_kernel _ _))
    | (rx_retention_head socketPort; exact cookie_frame (Cookies.socketPort_frame _) history)
    | archive_timer_step history

macro "archive_socket_step " history:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head dstCacheGet; exact cache_get _ _ $history)
  | (rx_retention_head dstCacheSet; exact cache_set _ _ _ _ $history)
  | (rx_retention_head dstCacheReset; exact cache_reset _ $history)
  | (with_reducible exact tunnel _ _ _ _ _ $history)
  | (allocation_release_lift_from Net.M; exact frame_store $history _ (liftRouting_sameWGStore _))
  | (rx_retention_head getRouting; exact frame_store $history _ (liftRouting_sameWGStore ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))))
  | archive_timer_step $history)

theorem send4 (ep : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (WG.send4 ep cache bytes ds exactRx) := by
  unfold WG.send4
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' archive_socket_step history

theorem send6 (ep : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (WG.send6 ep cache bytes ds exactRx) := by
  unfold WG.send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' archive_socket_step history

theorem send_buffer (pid : PeerId) (bytes : List UInt8) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (sendBufferToPeer pid bytes) := by
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head WG.send4; exact send4 _ _ _ _ _ history)
    | (rx_retention_head WG.send6; exact send6 _ _ _ _ _ history)
    | archive_timer_step history

theorem mac (pid : PeerId) (msg : List UInt8) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (addMacToPacket pid msg) := by
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  apply hoare_bind _ _ (write_saved pid p (fun current => {current with
    lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)),haveSentMac1 := true})
    (fun _ => ⟨rfl,rfl⟩) history)
  intro _
  change Framing.Preserves (StateInv history) _
  repeat' archive_timer_step history

theorem cookie_consume (msg : List UInt8) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' archive_handshake_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
