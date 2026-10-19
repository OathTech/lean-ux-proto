import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceReceiveFrames

/-! Socket and cookie operations preserve positive resident peer counts.
No cookie-authentication or successful-send assumption is required. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem cookie_frame {action : WG.M α} (same : Cookies.NoNoiseChange action) : Preserves Inv action := by
  apply frame
  apply same.of_factor (fun s => fun pid =>
    (s.1.bind fun d => d.peers[pid]?).map Peer.refcount)
  intro w
  simp only [Cookies.noiseView,Cookies.viewOfStore,wgStoreView,Option.bind_map]
  rfl

theorem cache_get (pid : PeerId) (gen : Nat) :
    Framing.Preserves Inv (dstCacheGet pid gen) := by
  let P := Inv
  let R := fun (p : Peer) (w : WGWorld) => P w ∧ 0 < p.refcount
  have finish (p : Peer) : Hoare (do
      let ts ← hiddenJiffies .dstCacheRefreshTs
      setPeer pid {p with dstCache := {p.dstCache with slot := none,refreshTs := ts}}
      Pure.pure none : WG.M (Option DstSlot)) (R p) (fun _ => P) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.hiddenJiffies .dstCacheRefreshTs) (R p))
    intro ts
    apply hoare_bind _ _ (write_saved pid p
      (fun current => {current with dstCache := {current.dstCache with slot := none,refreshTs := ts}})
      (fun _ => rfl))
    intro _
    exact preserves_pure _
  unfold dstCacheGet getAmbient
  apply preserves_bind (hoare_liftAmbient (get : AmbientM Ambient) P)
  intro a
  apply preserves_bind (hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2))
  intro w
  split
  · exact preserves_pure _
  · apply hoare_bind _ _ (read_saved pid)
    intro p
    cases slot_eq : p.dstCache.slot with
    | none => simpa only [slot_eq] using finish p
    | some slot =>
      simp only [slot_eq]
      split
      · exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
      · exact finish p

theorem cache_set (pid : PeerId) (src gen dev : Nat) :
    Framing.Preserves Inv (dstCacheSet pid src gen dev) :=
  update_peer pid (fun p => {p with dstCache := {p.dstCache with slot := some {src,gen,dev}}})
    (fun _ positive => positive)

theorem tunnel (ep : Endpoint) (bytes : List UInt8) (ds : Nat) (route : Route)
    (exactRx : Bool) :
    Framing.Preserves Inv
      ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) ep bytes ds route exactRx) := by
  index_unfold _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
  simp (config := {zeta := false}) only [unsupported,skipCut]
  repeat' first
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _))
    | (rx_retention_head socketPort; exact cookie_frame (Cookies.socketPort_frame _))
    | peer_reference_timer_step

macro "peer_reference_socket_step" : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head dstCacheGet; exact cache_get _ _)
  | (rx_retention_head dstCacheSet; exact cache_set _ _ _ _)
  | (rx_retention_head dstCacheReset; exact cache_reset _)
  | (with_reducible exact tunnel _ _ _ _ _)
  | (allocation_release_lift_from Net.M; exact store (liftRouting_sameWGStore _))
  | (rx_retention_head getRouting; exact store (liftRouting_sameWGStore ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))))
  | peer_reference_timer_step)

theorem send4 (ep : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) :
    Framing.Preserves Inv (WG.send4 ep cache bytes ds exactRx) := by
  unfold WG.send4
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' peer_reference_socket_step

theorem send6 (ep : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) :
    Framing.Preserves Inv (WG.send6 ep cache bytes ds exactRx) := by
  unfold WG.send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' peer_reference_socket_step

theorem send_buffer (pid : PeerId) (bytes : List UInt8) :
    Framing.Preserves Inv (sendBufferToPeer pid bytes) := by
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head WG.send4; exact send4 _ _ _ _ _)
    | (rx_retention_head WG.send6; exact send6 _ _ _ _ _)
    | peer_reference_timer_step

theorem mac (pid : PeerId) (msg : List UInt8) :
    Framing.Preserves Inv (addMacToPacket pid msg) := by
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  apply hoare_bind _ _ (read_saved pid)
  intro p
  apply hoare_bind _ _ (write_saved pid p (fun current => {current with
    lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)),haveSentMac1 := true})
    (fun _ => rfl))
  intro _
  change Framing.Preserves Inv _
  repeat' peer_reference_timer_step

theorem cookie_consume (msg : List UInt8) :
    Framing.Preserves Inv (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' peer_reference_handshake_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
