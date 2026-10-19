import Leanux.Proofs.WG.Config.GetterPeerCommandFrames
import Leanux.Proofs.WG.Config.GetterStagingSource
import Leanux.Proofs.WG.Queues.JointPeerCommand
import Leanux.Proofs.WG.Index.ConfigurationPeerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CommandScalarRules
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do Queues
open Leanux.Proofs.WG.Configuration

structure Contracts (P : WGWorld → Prop) (pid : PeerId) : Prop where
  readDevice : Preserves P getDev
  readPeer : Preserves P (getPeer pid)
  writePeer : ∀ p, Preserves P (setPeer pid p)
  put : ∀ peer, Preserves P (peerPut peer)
  remove : ∀ peer, Preserves P (peerRemove peer)
  endpoint : ∀ e, Preserves P (setPeerEndpoint pid e)
  replace : Preserves P (removeByPeer pid)
  allowed : ∀ ip, Preserves P (setAllowedip pid ip)
  keepalive : Preserves P (sendKeepalive pid)
  staged : Preserves P (sendStagedPackets pid)

variable {P : WGWorld → Prop} {pid : PeerId}

macro "command_scalar_step " contracts:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact ($contracts).readDevice)
  | (rx_retention_head getPeer; exact ($contracts).readPeer)
  | (rx_retention_head setPeer; exact ($contracts).writePeer _)
  | (rx_retention_head peerPut; exact ($contracts).put _)
  | (rx_retention_head WG.andM; unfold WG.andM)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | rx_retention_step)

theorem out (contracts : Contracts P pid) (attrs : PeerAttrs)
    (peer : Option PeerId) (ret : Int) :
    Preserves P (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) := by
  repeat' command_scalar_step contracts

theorem finish (contracts : Contracts P pid) (attrs : PeerAttrs)
    (peer : Option PeerId) (ret : Int) :
    Preserves P (Configuration.peerTailFinishSource attrs peer pid ret) := by
  unfold Configuration.peerTailFinishSource
  repeat' first
    | (rx_retention_head sendKeepalive; exact contracts.keepalive)
    | (rx_retention_head sendStagedPackets; exact contracts.staged)
    | command_scalar_step contracts

theorem tail (contracts : Contracts P pid) (attrs : PeerAttrs)
    (peer : Option PeerId) :
    Preserves P (Configuration.peerConfigTailSource attrs peer pid) := by
  rw [Configuration.peerConfigTailSource_factor]
  exact Index.ConfigurationIndex.allowedIps_rule _ _ attrs peer pid _
    contracts.allowed (out contracts attrs peer) (finish contracts attrs peer)

theorem update (contracts : Contracts P pid) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) :
    Preserves P (Configuration.peerConfigUpdateSource attrs peer flags psk pid) := by
  rw [Configuration.peerConfigUpdateSource_factor]
  unfold peerConfigUpdateWith
  repeat' first
    | (rx_retention_head peerRemove; exact contracts.remove _)
    | (rx_retention_head setPeerEndpoint; exact contracts.endpoint _)
    | (rx_retention_head removeByPeer; exact contracts.replace)
    | (rx_retention_head Configuration.peerConfigTailSource; exact tail contracts _ _)
    | command_scalar_step contracts

end Leanux.Proofs.WG.Config.CommandScalarRules
