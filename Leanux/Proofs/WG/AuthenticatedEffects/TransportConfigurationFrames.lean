import Leanux.Proofs.WG.AuthenticatedEffects.TransportRemovalFrames
import Leanux.Proofs.WG.Packets.PublicationDeviceConfiguration

/-! Concrete RX frames for configuration leaves; key and peer mutation is
allowed while existing receive cells and their epoch are retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportConfiguration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration
open OwnerCompletion (geometry)
set_option maxHeartbeats 600000

theorem socket_rx (action : WG.M α) (same : SameSocket action) :
    SameView RxDisposition.nativeRxStore action := by
  apply same.of_factor
    (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,RxDisposition.nativeRxStore,
    Option.map_map,Option.bind_map,Function.comp_def]

theorem configuration_rx (action : WG.M α) (same : SameConfiguration action) :
    SameView RxDisposition.nativeRxStore action := by
  apply same.of_factor
    (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,RxDisposition.nativeRxStore,
    Option.map_map,Option.bind_map,Function.comp_def]

theorem peerCreate_rx (key : Key) (psk : Option Key) :
    SameView RxDisposition.nativeRxStore (peerCreate key psk) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.peerCreate_rx) key psk

theorem allowedip_rx (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView RxDisposition.nativeRxStore (setAllowedip pid ip) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationAllowedIps.«0».Leanux.Proofs.WG.PublicationFrontier.setAllowedip_geometry) pid ip).factor Prod.snd

theorem clearEndpoint_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (clearPeerEndpointSrc pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.clearEndpoint_geometry) pid).factor Prod.snd

theorem pubkey_rx (key : Key) : SameView RxDisposition.nativeRxStore (pubkeyLookup key) := by
  apply SameView.factor (view := geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold pubkeyLookup peerGetMaybeZero
  simp (config := {zeta := false}) only [branch,branchCmp,refcountIncNotZero,invariant,unsupported,requireNotPending]
  repeat' completion_step initial

theorem precompute_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (precomputeStaticStatic pid) := by
  apply SameView.factor (view := geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold precomputeStaticStatic
  simp (config := {zeta := false}) only [branch,requireNotPending]
  repeat' completion_step initial

theorem expire_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (expireCurrentPeerKeypairs pid) := by
  apply SameView.factor (view := geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold expireCurrentPeerKeypairs handshakeClear handshakeZero resetLastSentHandshake
  simp (config := {zeta := false}) only [requireNotPending,branch,invariant,hiddenClock64]
  repeat' first
    | (allocation_release_lift_from IndexM
       apply hoare_liftIndex
       intro w d table hi hd
       simpa only [geometry,RxCredits.rxView,hd,Option.map_some,Option.bind_some] using hi)
    | completion_step initial

theorem port_rx (port : Nat) : SameView RxDisposition.nativeRxStore (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (snapshot_head clearPeerEndpointSrc; exact clearEndpoint_rx _)
    | (snapshot_head socketInit; exact socket_rx _ (socketInit_sameSocket _))
    | (snapshot_head modifyDev; apply TransportCarrier.modifyDev_rx <;> intro d <;> rfl)
    | solve | transport_native_rx
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ForIn.forIn; apply DumpComposition.forIn_sameView)
    | (snapshot_head ite; split)
    | keypairs_intro_forall
    | snapshot_head_reduce
    | snapshot_head_match

end Leanux.Proofs.WG.AuthenticatedEffects.TransportConfiguration
