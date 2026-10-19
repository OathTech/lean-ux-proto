import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEndpointFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedConfigurationFrames

/-! Native configuration and namespace metadata retain the full entry
projection. Peer creation and device destruction require separate accounting;
neither is treated as a metadata frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ControlFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    SameView StagedEntry.view action := by
  exact same.of_factor (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view
    (fun w => by
      cases device : w.dev <;>
        simp [funext_iff,StagedEntry.view,configurationView,configurationDevice,wgOwnedView,wgStoreView,
          Packets.epoch,Staged.stagedAt,PacketMaterial.view,TxDisposition.txPackets,
          Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,device])

theorem socket {action : WG.M α} (same : SameSocket action) :
    SameView StagedEntry.view action := by
  exact same.of_factor (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view
    (fun w => by
      cases device : w.dev <;>
        simp [funext_iff,StagedEntry.view,socketView,socketDevice,wgOwnedView,wgStoreView,
          Packets.epoch,Staged.stagedAt,PacketMaterial.view,TxDisposition.txPackets,
          Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,device])

macro "entry_control_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact (EndpointFrames.clear _).wp (· = $initial))
  | (rx_retention_head setPeerEndpoint; exact (EndpointFrames.set _ _).wp (· = $initial))
  | (rx_retention_head socketInit; exact (socket (socketInit_sameSocket _)).wp (· = $initial))
  | (rx_retention_head socketReinit; exact (socket (socketReinit_sameSocket _ _)).wp (· = $initial))
  | (rx_retention_head setStaticIdentityPrivateKey; exact (configuration (setStaticIdentityPrivateKey_sameConfiguration _)).wp (· = $initial))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact (configuration cookiePrecomputeDeviceKeys_sameConfiguration).wp (· = $initial))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec StagedEntry.view (· = $initial)
     intro item acc
     change Preserves (fun w => StagedEntry.view w = $initial) _)
  | entry_key_maintenance $initial)

theorem set_port (port : Nat) : SameView StagedEntry.view (setPort port) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' entry_control_step initial

theorem pre_exit : SameView StagedEntry.view netnsPreExit := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' entry_control_step initial

theorem reset_handshake (pid : PeerId) :
    SameView StagedEntry.view (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold resetLastSentHandshake hiddenClock64
  repeat' entry_control_step initial

theorem limiter : SameView StagedEntry.view ratelimiterUninit := by
  exact ratelimiterUninit_sameRatelimiter.of_factor
    (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ControlFrames
