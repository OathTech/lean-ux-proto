import Leanux.Proofs.WG.Noise.DriverTagLeafFrames
import Leanux.Proofs.WG.Noise.PendingConfigurationFrames
import Leanux.Proofs.WG.Noise.ReceptionTagFrames

/-! Concrete socket and configuration leaves retain every optional tag.
The peer read and its actual field write remain grouped. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do

theorem read_frame : SameView tagView (get : WG.M WGWorld) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases run
  rfl

theorem dstCacheReset_frame (pid : PeerId) : SameView tagView (dstCacheReset pid) := by
  unfold dstCacheReset
  apply (ambient_frame (get : AmbientM Ambient)).bind
  intro ambient
  apply read_frame.bind
  intro g
  split
  · exact SameView.pure tagView ()
  · apply (ambient_frame (AmbientM.hiddenJiffies .dstCacheResetTs)).bind
    intro ts
    exact modifyPeer_frame pid (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
      (fun _ => rfl)

theorem dstCacheResetNow_frame (pid : PeerId) : SameView tagView (dstCacheResetNow pid) := by
  unfold dstCacheResetNow
  exact (dstCacheReset_frame pid).bind (fun _ =>
    modifyPeer_frame pid (fun p => {p with dstCache := {p.dstCache with slot := none}}) (fun _ => rfl))

theorem clearPeerEndpointSrc_frame (pid : PeerId) : SameView tagView (clearPeerEndpointSrc pid) := by
  have factor : clearPeerEndpointSrc pid = (do
      (do let p ← getPeer pid
          setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
      dstCacheResetNow pid) := by
    simp only [clearPeerEndpointSrc,bind_assoc]
  rw [factor]
  exact (modifyPeer_frame pid
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
    (fun _ => rfl)).bind (fun _ => dstCacheResetNow_frame pid)

theorem setPort_frame (port : Nat) : SameView tagView (setPort port) := by
  unfold setPort
  apply (store_frame getDev_sameWGStore).bind
  intro d
  apply (ambient_frame (AmbientM.branch .setPortSame (d.incomingPort == port))).bind
  intro same
  cases same with
  | true => exact SameView.pure tagView 0
  | false =>
    apply (DumpComposition.forIn_sameView d.peerList ()
      (fun pid _ => do
        _ ← branch .setPortPeerIter true
        clearPeerEndpointSrc pid
        pure (.yield ()))
      (fun pid _ => (ambient_frame (AmbientM.branch .setPortPeerIter true)).bind (fun _ =>
        (clearPeerEndpointSrc_frame pid).bind (fun _ => SameView.pure tagView (ForInStep.yield ()))))).bind
    intro u
    apply (ambient_frame (AmbientM.branch .setPortPeerIter false)).bind
    intro u
    apply (ambient_frame (AmbientM.branch .setPortNotRunning !d.running)).bind
    intro down
    cases down with
    | true => exact (modifyDev_frame (fun d => {d with incomingPort := port})
        (fun _ => rfl)).bind (fun _ => SameView.pure tagView 0)
    | false => exact socket_frame (socketInit_sameSocket port)

theorem endpointWrite_frame (pid : PeerId) (endpoint : Endpoint) :
    SameView tagView (do
      setPeer pid { (← getPeer pid) with endpoint := some endpoint }
      dstCacheReset pid) := by
  have grouped := (modifyPeer_frame pid
    (fun p => {p with endpoint := some endpoint}) (fun _ => rfl)).bind
    (fun _ => dstCacheReset_frame pid)
  simpa only [bind_assoc] using grouped

theorem setPeerEndpoint_frame (pid : PeerId) (endpoint : Endpoint) :
    SameView tagView (setPeerEndpoint pid endpoint) := by
  unfold setPeerEndpoint
  apply (SameView.pure tagView ()).bind
  intro u
  apply (getPeer_frame pid).bind
  intro p
  apply (store_frame (endpointEq_sameStore endpoint p.endpoint)).bind
  intro eq
  apply (ambient_frame (AmbientM.branch .setEndpointEq eq)).bind
  intro same
  cases same with
  | true => exact SameView.pure tagView ()
  | false =>
    apply (ambient_frame (AmbientM.branch .setEndpointV4 (endpoint.family == AF_INET))).bind
    intro v4
    cases v4 with
    | true => exact endpointWrite_frame pid endpoint
    | false =>
      apply (ambient_frame (AmbientM.branch .setEndpointV6 (endpoint.family == AF_INET6))).bind
      intro v6
      cases v6 with
      | true => exact endpointWrite_frame pid endpoint
      | false => exact SameView.pure tagView ()

end Leanux.Proofs.WG.Noise.DriverTags

