import Leanux.Proofs.WG.Config.ConfiguredDeviceFrames
import Leanux.Proofs.WG.Config.ConfiguredCommandSource
import Leanux.Proofs.WG.Index.ConfigurationDeviceSource
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem get_ready {P : WGWorld → Prop} : Preserves P getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨rfl,rfl,_⟩ := DecryptCarrier.getDev_current a b run
  exact pre

theorem join_ready {α : Type} (cs : Ledger) (loans : Reservations) (action : WG.M α)
    (account : Preserves (Index.ConfigurationIndex.Entry cs loans) action)
    (routing : Preserves Ready action) : Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account g a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp routing g a result v b pre.2 run⟩

theorem free_ready : Preserves Ready WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  cases result
  obtain ⟨d,device,t4,t6,routing,_⟩ := pre
  obtain ⟨out,store,cleared⟩ := free_endpoint g v a b d device t4 t6 routing run
  exact ⟨out,congrArg WGStoreView.dev store,.empty,.empty,cleared.routing routing,
    configuredOwners_empty out⟩

theorem makeDead_ready (pid : PeerId) : Preserves Ready (peerMakeDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨d,device,t4,t6,routing,owners⟩ := pre
  obtain ⟨out,p,present,_,_,represented,configured⟩ :=
    peerMakeDead_configured_run d t4 t6 pid routing owners g a result v b device run
  exact ⟨out,present,_,_,represented,configured⟩

theorem afterDead_ready (pid : PeerId) : Preserves Ready (peerRemoveAfterDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  obtain ⟨d,device,t4,t6,routing,owners⟩ := pre
  obtain ⟨out,present,_,represented,configured⟩ :=
    peerRemoveAfterDead_configured_run d t4 t6 pid routing owners g a result v b device run
  exact ⟨out,present,_,_,represented,configured⟩

/-- Original free, first make-dead pass, and saved-list cleanup retain represented
ownership. The boundary claim allows normal errno paths elsewhere and does not
assert physical node or peer-store emptiness. -/
theorem bulk_ready : Preserves Ready peerRemoveAll := by
  rw [peerRemoveAll_factor]
  unfold peerRemoveAllWith
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_ready)
    | (rx_retention_head getDev; exact get_ready)
    | (rx_retention_head peerMakeDead; exact makeDead_ready _)
    | (rx_retention_head peerRemoveAfterDead; exact afterDead_ready _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id Ready
       intro x b
       change Preserves Ready _)
    | rx_retention_step

theorem configuration_ready {α : Type} (action : WG.M α) (same : SameConfiguration action) :
    Preserves Ready action :=
  retained_ready action (ProjectedRetainsRoutingCall.of_same (configuration_routing_native action same))
    (configuration_base action same)

theorem socket_ready {α : Type} (action : WG.M α) (same : SameSocket action) :
    Preserves Ready action :=
  retained_ready action (ProjectedRetainsRoutingCall.of_same (socketControl_routing_native action same))
    (socket_base action same)

theorem precompute_ready (pid : PeerId) : Preserves Ready (precomputeStaticStatic pid) :=
  retained_ready _ (ProjectedRetainsRoutingCall.of_same (precomputeStaticStatic_routing pid)) (precompute_base pid)

theorem expire_ready (pid : PeerId) : Preserves Ready (expireCurrentPeerKeypairs pid) :=
  retained_ready _ (ProjectedRetainsRoutingCall.of_same (expireCurrentPeerKeypairs_routing pid)) (expire_base pid)

theorem clearEndpoint_ready (pid : PeerId) : Preserves Ready (clearPeerEndpointSrc pid) :=
  retained_ready _ (ProjectedRetainsRoutingCall.of_same (clearPeerEndpointSrc_routing pid))
    (BaseCoherence.clearEndpoint_view pid)

theorem conflict_ready (key : Key) : Preserves Ready (do
    let peer ← pubkeyLookup key
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer : WG.M Unit) := by
  apply preserves_bind (retained_ready _
    (ProjectedRetainsRoutingCall.of_same (pubkeyLookup_routing key)) (BaseCoherence.pubkeyLookup_view key))
  intro peer
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevOldPeer peer.isSome) Ready)
  intro selected
  cases selected with
  | false => exact preserves_pure ()
  | true =>
    exact preserves_bind
      (retained_ready _ (peerPut_retainsRouting peer) (BaseCoherence.peerPut_view peer))
      (fun _=>remove_ready peer)


end Leanux.Proofs.WG.Config.OwnerConfiguration
