import Leanux.Proofs.WG.Config.GetterContextFrames

/-! Actual original setter composition through the existing configuration factories. No alternate operation or accounting traversal. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterContext
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

theorem conflict (key : Key) : SameView getterMetadata (do
    let peer ← pubkeyLookup key
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer : WG.M Unit) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  repeat' first
    | (rx_retention_head pubkeyLookup; exact (GetterPeerCommand.lookup _).wp (fun v=>v=initial))
    | (rx_retention_head peerPut; exact (GetterCleanup.peerPut_metadata_getter_variant _).wp (fun v=>v=initial))
    | (rx_retention_head peerRemove; exact (GetterPeerCommand.remove _).wp (fun v=>v=initial))
    | getter_cleanup_step initial

theorem key_contracts (initial : Context) :
    Index.ConfigurationKeyRules.Contracts (fun g=>view g=initial) where
  read := (metadata GetterCleanup.read_device).wp (fun v=>v=initial)
  identity key := (identity key).wp (fun v=>v=initial)
  cookie := cookie.wp (fun v=>v=initial)
  precompute pid := (metadata (GetterPeerCommand.precompute pid)).wp (fun v=>v=initial)
  expire pid := (metadata (expire pid)).wp (fun v=>v=initial)
  staged pid := (metadata (GetterStaging.staged pid)).wp (fun v=>v=initial)
  conflict key := (metadata (conflict key)).wp (fun v=>v=initial)

macro "getter_context_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact (metadata GetterCleanup.read_device).wp (fun v=>v=$initial))
  | (rx_retention_head modifyDev; exact (modify_device _).wp (fun v=>v=$initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun g=>view g=$initial)
     intro x b
     change Preserves (fun g=>view g=$initial) _)
  | rx_retention_step)

theorem peers (attrs : DeviceAttrs) :
    SameView view (Configuration.devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  intro initial
  change Preserves (fun g=>view g=initial) _
  unfold devicePeersWith
  repeat' first
    | (rx_retention_head setPeerCmd; exact (metadata (GetterPeerCommand.command _)).wp (fun v=>v=initial))
    | getter_context_step initial

theorem key (attrs : DeviceAttrs) :
    SameView view (Configuration.deviceKeySource attrs) :=
  fun initial=>Index.ConfigurationKeyRules.key _ (key_contracts initial) attrs
    ((peers attrs).wp (fun v=>v=initial))

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    SameView view (Configuration.deviceUpdateSource attrs flags) := by
  rw [deviceUpdateSource_factor]
  intro initial
  change Preserves (fun g=>view g=initial) _
  unfold deviceUpdateWith
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (clear _).wp (fun v=>v=initial))
    | (rx_retention_head setPort; exact (port _).wp (fun v=>v=initial))
    | (rx_retention_head peerRemoveAll; exact (metadata GetterCleanup.remove_all).wp (fun v=>v=initial))
    | (rx_retention_head Configuration.deviceKeySource; exact (key _).wp (fun v=>v=initial))
    | getter_context_step initial

theorem request (attrs : DeviceAttrs) : SameView view (wgSetDevice attrs) := by
  rw [←Configuration.wgSetDevice_source,setDeviceSource_factor]
  intro initial
  change Preserves (fun g=>view g=initial) _
  unfold setDeviceWith WG.orM
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (fun g=>view g=initial))
    | (rx_retention_head Configuration.deviceUpdateSource; exact (update _ _).wp (fun v=>v=initial))
    | getter_context_step initial

end Leanux.Proofs.WG.Config.GetterContext
