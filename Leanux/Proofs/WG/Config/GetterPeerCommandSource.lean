import Leanux.Proofs.WG.Config.CommandScalarRulesSource
import Leanux.Proofs.WG.Config.GetterPeerCommandFrames
import Leanux.Proofs.WG.Config.GetterStagingSource
import Leanux.Proofs.WG.Queues.JointPeerCommand
import Leanux.Proofs.WG.Index.ConfigurationPeerSource

/-! Metadata preservation through the actual peer command, using the existing
source factories and allowed-IP loop. All normal errno returns are included. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterPeerCommand
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do Queues
open GetterCleanup Leanux.Proofs.WG.Configuration

theorem create (key : Key) (psk : Option Key) :
    SameView getterMetadata (peerCreate key psk) := by
  rw [RxCredits.BaseCreation.peerCreate_factor]
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold RxCredits.BaseCreation.finish ConfiguredIdentity.publishRow
  repeat' first
    | (rx_retention_head hiddenAlloc; exact hoare_liftAmbient (AmbientM.hiddenAlloc _) _)
    | (rx_retention_head Peers.peerCreateCore; exact (create_core _ _).wp (fun s=>s=initial))
    | (rx_retention_head dstCacheReset; exact (cache_reset _).wp (fun s=>s=initial))
    | (rx_retention_head handshakeInit; exact (handshake_init _ _).wp (fun s=>s=initial))
    | (rx_retention_head resetLastSentHandshake; exact (reset_last _).wp (fun s=>s=initial))
    | getter_cleanup_step initial


theorem remove (peer : Option PeerId) :
    SameView getterMetadata (peerRemove peer) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold peerRemove
  repeat' first
    | (rx_retention_head peerMakeDead; exact (make_dead _).wp (fun s=>s=initial))
    | (rx_retention_head peerRemoveAfterDead; exact (after_dead _).wp (fun s=>s=initial))
    | getter_cleanup_step initial

macro "getter_command_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerPut; exact (peerPut_metadata_getter_variant _).wp (fun s=>s=$initial))
  | (rx_retention_head WG.andM; unfold WG.andM)
  | getter_cleanup_step $initial)
theorem scalar_contracts (initial : GetterMetadata) (pid : Leanux.WG.PeerId) :
    CommandScalarRules.Contracts (fun g=>getterMetadata g=initial) pid where
  readDevice:=GetterCleanup.read_device.wp (fun s=>s=initial)
  readPeer:=(GetterCleanup.read_peer pid).wp (fun s=>s=initial)
  writePeer:=fun p=>(GetterCleanup.set_peer pid p).wp (fun s=>s=initial)
  put:=fun peer=>(GetterCleanup.peerPut_metadata_getter_variant peer).wp (fun s=>s=initial)
  remove:=fun peer=>(remove peer).wp (fun s=>s=initial)
  endpoint:=fun e=>(endpoint pid e).wp (fun s=>s=initial)
  replace:=(GetterCleanup.remove_allowed pid).wp (fun s=>s=initial)
  allowed:=fun ip=>(allowed pid ip).wp (fun s=>s=initial)
  keepalive:=(GetterStaging.keepalive pid).wp (fun s=>s=initial)
  staged:=(GetterStaging.staged pid).wp (fun s=>s=initial)

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    SameView getterMetadata (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) := by
  intro initial
  exact CommandScalarRules.out (scalar_contracts initial 0) attrs peer ret
theorem finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    SameView getterMetadata (Leanux.Proofs.WG.Configuration.peerTailFinishSource attrs peer pid ret) := by
  intro initial
  exact CommandScalarRules.finish (scalar_contracts initial pid) attrs peer ret
theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    SameView getterMetadata (Leanux.Proofs.WG.Configuration.peerConfigTailSource attrs peer pid) := by
  intro initial
  exact CommandScalarRules.tail (scalar_contracts initial pid) attrs peer
theorem update (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    SameView getterMetadata (Leanux.Proofs.WG.Configuration.peerConfigUpdateSource attrs peer flags psk pid) := by
  intro initial
  exact CommandScalarRules.update (scalar_contracts initial pid) attrs peer flags psk
theorem acquired (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    SameView getterMetadata
      (Leanux.Proofs.WG.Configuration.peerCommandAcquiredWith (fun {_} a=>a) peerCreate peerGet
        (fun ret=>do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
        (Leanux.Proofs.WG.Configuration.peerConfigUpdateSource attrs) key psk flags peer) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold Leanux.Proofs.WG.Configuration.peerCommandAcquiredWith
  repeat' first
    | (rx_retention_head peerCreate; exact (create _ _).wp (fun s=>s=initial))
    | (rx_retention_head peerGet; exact (GetterStaging.acquire_peer _).wp (fun s=>s=initial))
    | (rx_retention_head Leanux.Proofs.WG.Configuration.peerConfigUpdateSource; exact (update _ _ _ _ _).wp (fun s=>s=initial))
    | getter_command_step initial
theorem command (attrs : PeerAttrs) : SameView getterMetadata (setPeerCmd attrs) := by
  rw [←Leanux.Proofs.WG.Configuration.setPeerCmd_source,Leanux.Proofs.WG.Configuration.setPeerCmdSource_factor]
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold Leanux.Proofs.WG.Configuration.setPeerCmdWith
  repeat' first
    | (rx_retention_head pubkeyLookup; exact (lookup _).wp (fun s=>s=initial))
    | (rx_retention_head Leanux.Proofs.WG.Configuration.peerCommandAcquiredWith; exact (acquired _ _ _ _ _).wp (fun s=>s=initial))
    | getter_command_step initial
end Leanux.Proofs.WG.Config.GetterPeerCommand
