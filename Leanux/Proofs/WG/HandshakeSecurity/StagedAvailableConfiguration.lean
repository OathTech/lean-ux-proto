import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableEffects
import Leanux.Proofs.WG.TransmitSecurity.StagedAllowedIpFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedConfigurationFrames

/-! Configuration leaves retain live staged birth credits. A newly created
peer contributes only an empty queue; send/drain callbacks are not framed. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem write_empty_peer (pid : PeerId) (peer : Peer) (empty : peer.staged = []) :
    Preserves (Inv h) (setPeer pid peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases run
  intro generation atEpoch q stamp packets resident
  cases device : w.dev with
  | none => simp [Packets.epoch,device] at atEpoch
  | some d =>
    have epoch : Packets.epoch w = some generation := by
      simpa only [Packets.epoch,device,Option.map_some] using atEpoch
    by_cases same : pid = q
    · subst q
      have entry : (peer.internalId,peer.staged) = (stamp,packets) := by
        simpa only [stagedAt,device,Option.map_some,Option.bind_some,
          Std.TreeMap.getElem?_insert_self,Option.some.injEq] using resident
      have packets_eq := congrArg Prod.snd entry
      change peer.staged = packets at packets_eq
      rw [← packets_eq,empty]
      exact .nil
    · apply before generation epoch q stamp packets
      simpa only [stagedAt,device,Option.map_some,Option.bind_some,
        Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq,same,↓reduceIte] using resident

private theorem precompute_staged (pid : PeerId) : SameView stagedAt (precomputeStaticStatic pid) := by
  intro initial
  unfold precomputeStaticStatic requireNotPending
  simp only [pure_bind]
  apply preserves_bind ((Exact.store getDev_sameWGStore).wp (· = initial))
  intro device
  apply hoare_bind _ _ (Staged.read_saved (· = initial) pid)
  intro peer
  let P := fun w => stagedAt w = initial ∧ stagedAt w pid = some (peer.internalId,peer.staged)
  apply hoare_consequence (P := P) (Q := fun _ => P) ?_ (fun _ before => before) (fun _ _ before => before.1)
  change Preserves P _
  simp only [branch]
  repeat' first
    | (receive_update_head setPeer
       apply (Exact.update_peer _ _ ?_).wp (fun q => q = initial ∧ q pid = some (peer.internalId,peer.staged))
       intro p
       exact ⟨rfl,rfl⟩)
    | (rx_retention_head setPeer; exact Exact.write_known (· = initial) pid _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem precompute (pid : PeerId) : Preserves (Inv h) (precomputeStaticStatic pid) :=
  frame (epoch_rx_ring ((pinned_const _private.Leanux.Proofs.WG.Queues.ConfigurationPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical.precompute_cell) pid))
    (Staged.of_view _ (precompute_staged pid))

theorem handshake_init (pid : PeerId) (psk : Option Key) : Preserves (Inv h) (handshakeInit pid psk) := by
  unfold handshakeInit IndexOwner.setPeerWord
  repeat' first
    | (rx_retention_head precomputeStaticStatic; exact precompute _)
    | (rx_retention_head setKeypair; exact write_key _ _)
    | staged_available_native

theorem reset_handshake (pid : PeerId) : Preserves (Inv h) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake hiddenClock64
  repeat' staged_available_native

theorem cache_reset (pid : PeerId) : Preserves (Inv h) (dstCacheReset pid) :=
  exact_ring (RxRing.dstCacheReset_cell pid) (Exact.cache_reset pid)

theorem peer_create (key : Key) (psk : Option Key) : Preserves (Inv h) (peerCreate key psk) := by
  unfold peerCreate
  simp only [branch,branchCmp,hiddenAlloc]
  repeat' first
    | (rx_retention_head setPeer; exact write_empty_peer _ _ rfl)
    | (rx_retention_head handshakeInit; exact handshake_init _ _)
    | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
    | (rx_retention_head dstCacheReset; exact cache_reset _)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem aip (action : AipM α) : Preserves (Inv h) (liftAip action) := by
  apply hoare_liftAip
  intro w d table before device
  apply before.retains
  · simp only [Packets.epoch,device,Option.map_some]
  · intro pid cell found
    simpa only [stagedAt,device,Option.bind_some] using found

theorem list_add (pid : PeerId) (node : NodeId) : Preserves (Inv h) (listAddTail pid node) := by
  unfold listAddTail
  exact update_peer _ _ (fun _ => ⟨rfl,rfl⟩)

theorem list_delete (node : NodeId) : Preserves (Inv h) (listDel node) := by
  have same := AllowedIps.listDel_clearListView node
  apply frame
  · exact same.of_factor (fun s => s.1.dev.map Device.ifindex) Packets.epoch
      (fun w => by simp only [AllowedIps.clearListView,Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => fun pid => (s.2 pid).map (fun p => (p.internalId,p.staged))) stagedAt
      (fun w => by funext pid; simp only [AllowedIps.clearListView,stagedAt,Option.map_bind,
        Option.map_map,Function.comp_def])

theorem node {action : WG.M α} (same : SameNode action) : Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun w => by simp only [nodeView,nodeDevice,wgStoreView,Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [nodeView,nodeDevice,wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

macro "staged_available_aip" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip _)
  | (rx_retention_head liftAip; exact aip _)
  | (rx_retention_head listAddTail; exact list_add _ _)
  | (rx_retention_head listDel; exact list_delete _)
  | staged_available_native)

theorem allowedip_add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves (Inv h) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' staged_available_aip

theorem allowedip_insert (family addr cidr : Nat) (pid : PeerId) :
    Preserves (Inv h) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact allowedip_add _ _ _ _ _)
    | staged_available_aip

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Inv h) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  repeat' first
    | (rx_retention_head WG.insert; exact allowedip_insert _ _ _ _)
    | staged_available_aip

theorem allowedip_remove (pid : PeerId) : Preserves (Inv h) (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head AllowedIps.removeNodeBody; exact node (removeNodeBody_sameNode _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_available_aip

theorem allowedip_free : Preserves (Inv h) WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have same := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a value v b rfl run
  apply before.retains
  · have epoch := congrArg (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map Device.ifindex) same
    simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
      wgStoreView,Packets.epoch,Option.map_map,Function.comp_def] using epoch
  · have queues := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
        fun pid => (s.2 pid).map (fun p => (p.internalId,p.staged))) same
    have retained : stagedAt v = stagedAt w := by
      funext pid
      simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
        stagedAt,wgStoreView,Option.bind_map,Option.map_bind,Option.map_map,Function.comp_def] using congrFun queues pid
    intro pid cell found
    simpa only [retained] using found

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun _ => by simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
        Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [configurationView,configurationDevice,wgOwnedView,
        wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

theorem socket {action : WG.M α} (same : SameSocket action) :
    Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun _ => by simp only [socketView,socketDevice,wgOwnedView,wgStoreView,
        Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [socketView,socketDevice,wgOwnedView,
        wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

theorem public_lookup (key : Key) : Preserves (Inv h) (pubkeyLookup key) :=
  frame (epoch_rx_ring (RxRing.pubkeyLookup_cell key)) (Staged.pubkey_lookup key)

theorem expire_keys (pid : PeerId) : Preserves (Inv h) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs
  simp only [requireNotPending,pure_bind]
  repeat' first
    | (rx_retention_head handshakeClear; exact native_clear_handshake _)
    | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
    | (rx_retention_head setKeypair; exact write_key _ _)
    | staged_available_native

theorem set_port (port : Nat) : Preserves (Inv h) (setPort port) := by
  unfold setPort
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_available_native

theorem keepalive_decision (p : Peer) (interval : Nat) (running : Bool) : SameWGStore
    (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))) := by
  intro initial
  change Preserves (fun w => wgStoreView w = initial) _
  unfold WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem Native.make_dead (pid : PeerId) : Preserves (Inv h) (peerMakeDead pid) := by
  unfold peerMakeDead
  repeat' first
    | (rx_retention_head removeByPeer; exact Native.allowedip_remove _)
    | staged_available_native

macro "staged_available_configuration" : tactic => `(tactic| first
  | (rx_retention_head setAllowedip; exact Native.allowedip_set _ _)
  | (rx_retention_head removeByPeer; exact Native.allowedip_remove _)
  | (rx_retention_head WG.free; exact Native.allowedip_free)
  | (rx_retention_head peerMakeDead; exact Native.make_dead _)
  | (rx_retention_head keypairsClear; exact native_clear_keys _)
  | (rx_retention_head handshakeClear; exact native_clear_handshake _)
  | (rx_retention_head runFlushedClearWork; exact native_flushed_clear _)
  | (rx_retention_head resetLastSentHandshake; exact Native.reset_handshake _)
  | (rx_retention_head peerCreate; exact Native.peer_create _ _)
  | (rx_retention_head pubkeyLookup; exact Native.public_lookup _)
  | (rx_retention_head precomputeStaticStatic; exact Native.precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact Native.expire_keys _)
  | (rx_retention_head setStaticIdentityPrivateKey; exact Native.configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact Native.configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head socketInit; exact Native.socket (socketInit_sameSocket _))
  | (rx_retention_head socketReinit; exact Native.socket (socketReinit_sameSocket _ _))
  | (rx_retention_head setPort; exact Native.set_port _)
  | (rx_retention_head clearPeerEndpointSrc; exact Native.clear_endpoint _)
  | (rx_retention_head setPeerEndpoint; exact Native.endpoint _ _)
  | (rx_retention_head delTimer; exact Native.delete_timer _ _)
  | (rx_retention_head purgeStagedPackets; exact Native.purge _)
  | (rx_retention_head lookupInterface; exact Native.store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head generatePublic; exact Native.store ((generatePublic_sameWGWorld _).factor wgStoreView))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a value v b before run
     cases run)
  | (rx_retention_head peekUnit; unfold peekUnit; exact hoare_liftAmbient _ _)
  | (rx_retention_head resolveUnit; unfold resolveUnit; exact hoare_liftAmbient _ _)
  | staged_available_native)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
