import Leanux.Proofs.WG.Config.DeviceSource
import Leanux.Proofs.WG.Config.AllowedTransferOperations
import Leanux.Proofs.WG.Noise.PendingMaintenanceSource
import Leanux.Proofs.WG.Config.PeerSource
import Leanux.Proofs.WG.Origins.ConfiguredCommand
import Leanux.Proofs.WG.Queues.SlotConfiguration
import Leanux.Proofs.WG.Noise.PendingTicketControlFrames
import Leanux.Proofs.WG.Noise.PendingTicketAllowedIpFrames

/-! Concrete configuration leaves preserve pending allocation identities.
Lookup, precomputation and socket contracts project existing proved views;
read/update pairs never admit an arbitrary replacement peer. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do

theorem peerGet_frame (pid : PeerId) : SameView view (peerGet pid) :=
  frame_from_fields (CurrentSlots.peerGet_fields pid) (Keypairs.WGFrames.peerGet_sameSnapshot pid)

theorem pubkeyLookup_frame (key : Key) : SameView view (pubkeyLookup key) := by
  apply frame_from_fresh
  · intro tracked entry w ambient result final after hi run
    exact (pubkeyLookup_spec_freshTransport_variant tracked entry key
      w ambient result final after hi run).1
  · exact Keypairs.WGFrames.pubkeyLookup_sameSnapshot key

theorem precomputeStaticStatic_frame (pid : PeerId) :
    SameView view (precomputeStaticStatic pid) :=
  frame_from_fields (CurrentSlots.precomputeStaticStatic_fields pid)
    (Keypairs.WGFrames.precomputeStaticStatic_sameSnapshot pid)

theorem frame_configuration {α : Type} (action : WG.M α) (frame : SameConfiguration action) :
    SameView view action := by
  apply frame.of_factor (fun s : WGOwnedView => storeView s.toWGStoreView) view
  intro w
  simp [storeView,configurationView,configurationDevice,wgOwnedView,wgStoreView,view,pending,
    Option.bind_map,Function.comp_def]

theorem setStaticIdentityPrivateKey_frame (key : Key) :
    SameView view (setStaticIdentityPrivateKey key) :=
  frame_configuration _ (setStaticIdentityPrivateKey_sameConfiguration key)

theorem cookiePrecomputeDeviceKeys_frame : SameView view cookiePrecomputeDeviceKeys :=
  frame_configuration _ cookiePrecomputeDeviceKeys_sameConfiguration

theorem dstCacheResetNow_frame (pid : PeerId) : SameView view (dstCacheResetNow pid) := by
  have factor : dstCacheResetNow pid = (do
      dstCacheReset pid
      modifyPeer pid (fun p => {p with dstCache := {p.dstCache with slot := none}})) := rfl
  rw [factor]
  exact (dstCacheReset_frame pid).bind (fun _ =>
    modifyPeer_spec_pending_variant pid _ (fun _ => rfl))

theorem clearPeerEndpointSrc_frame (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : clearPeerEndpointSrc pid = (do
      modifyPeer pid (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
      dstCacheResetNow pid) := by
    simp only [clearPeerEndpointSrc,modify_eq,bind_assoc]
  rw [factor]
  exact (modifyPeer_spec_pending_variant pid
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
    (fun _ => rfl)).bind (fun _ => dstCacheResetNow_frame pid)

/-- Port changes preserve pending tickets even when the socket rebind returns
an errno. The peer-list loop and every record consumer remain the original ones. -/
theorem setPort_frame (port : Nat) : SameView view (setPort port) := by
  unfold setPort
  apply (frame_store getDev_sameWGStore).bind
  intro d
  apply (frame_ambient (AmbientM.branch .setPortSame (d.incomingPort == port))).bind
  intro same
  cases same with
  | true => exact SameView.pure view 0
  | false =>
    apply (DumpComposition.forIn_sameView d.peerList ()
      (fun pid _ => do
        _ ← branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        pure (.yield ()))
      (fun pid _ => (frame_ambient (AmbientM.branch .setPortPeerIter true)).bind (fun _ =>
        (clearPeerEndpointSrc_frame pid).bind (fun _ => SameView.pure view (ForInStep.yield ()))))).bind
    intro u
    apply (frame_ambient (AmbientM.branch .setPortPeerIter false)).bind
    intro u
    apply (frame_ambient (AmbientM.branch .setPortNotRunning !d.running)).bind
    intro down
    cases down with
    | true => exact (modifyDev_frame (fun d => {d with incomingPort := port})
        (fun _ => rfl) (fun _ => rfl)).bind (fun _ => SameView.pure view 0)
    | false => exact frame_socket _ (socketInit_sameSocket port)

end Leanux.Proofs.WG.Noise.PendingTickets
