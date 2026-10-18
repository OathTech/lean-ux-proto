import Leanux.Proofs.WG.Noise.PendingPeerConfigurationFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues

private theorem keepaliveUpdate_then {α : Type} (entry : Store PeerId)
    (pid : PeerId) (interval : Nat) (running : Bool) (tail : Bool → WG.M α)
    (rest : ∀ send, Preserves (fun w => Retained entry (view w)) (tail send)) :
    Preserves (fun w => Retained entry (view w)) (do
      let p ← getPeer pid
      let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
      setPeer pid {p with persistentKeepaliveInterval := interval}
      tail send) := by
  simpa only [bind_assoc,pure_bind] using
    preserves_bind ((keepaliveUpdate_frame pid interval running).wp (Retained entry)) rest

private theorem update_then {α : Type} (entry : Store PeerId)
    (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (next : ∀ p, (f p).keypairNext = p.keypairNext)
    (rest : ∀u, Preserves (fun w => Retained entry (view w)) (tail u)) :
    Preserves (fun w => Retained entry (view w))
      (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  have paired : modifyPeer pid f = (getPeer pid >>= fun p => setPeer pid (f p)) := rfl
  simpa only [paired,bind_assoc] using
    preserves_bind ((modifyPeer_spec_pending_variant pid f next).wp (Retained entry)) rest

macro "pending_peer_config_step " entry:term : tactic => `(tactic| first
  | (rx_retention_head setAllowedip; exact (setAllowedip_frame _ _).wp (Retained $entry))
  | (rx_retention_head pubkeyLookup; exact (pubkeyLookup_frame _).wp (Retained $entry))
  | (rx_retention_head peerGet; exact (peerGet_frame _).wp (Retained $entry))
  | (rx_retention_head setPeerEndpoint; exact (setPeerEndpoint_frame _ _).wp (Retained $entry))
  | (rx_retention_head removeByPeer; exact (removeByPeer_frame _).wp (Retained $entry))
  | (rx_retention_head peerPut; exact (peerPut_retained _).wp (Retained $entry)
      (fun _ _ later earlier => earlier.trans later))
  | (rx_retention_head peerRemove; exact (peerRemove_retained _).wp (Retained $entry)
      (fun _ _ later earlier => earlier.trans later))
  | (rx_retention_head peerCreate; exact (peerCreate_retained _ _).wp (Retained $entry)
      (fun _ _ later earlier => earlier.trans later))
  | (rx_retention_head sendStagedPackets; exact (sendStagedPackets_retained _).wp (Retained $entry)
      (fun _ _ later earlier => earlier.trans later))
  | (rx_retention_head sendKeepalive; exact (sendKeepalive_retained _).wp (Retained $entry)
      (fun _ _ later earlier => earlier.trans later))
  | pending_retention_step $entry)

theorem peerConfigTailSource_retained (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    RetainsCall (Config.peerConfigTailSource a peer pid) := by
  apply retains_of_preserves
  intro entry
  apply (ensures_iff (Config.peerConfigTailSource a peer pid) (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr
  change Preserves (fun w => Retained entry (view w)) _
  unfold Config.peerConfigTailSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (env_bind_head getPeer
       apply keepaliveUpdate_then entry
       intro send)
    | pending_peer_config_step entry

theorem peerConfigUpdateSource_retained (a : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    RetainsCall (Config.peerConfigUpdateSource a peer flags psk pid) := by
  apply retains_of_preserves
  intro entry
  apply (ensures_iff (Config.peerConfigUpdateSource a peer flags psk pid) (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr
  change Preserves (fun w => Retained entry (view w)) _
  unfold Config.peerConfigUpdateSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (receive_update_head setPeer
       exact (modifyPeer_spec_pending_variant _ _ (fun _ => rfl)).wp (Retained entry))
    | (receive_update_head Bind.bind
       apply update_then entry
       · intro p; rfl
       intro u)
    | (rx_retention_head Config.peerConfigTailSource
       exact (peerConfigTailSource_retained _ _ _).wp (Retained entry)
         (fun _ _ later earlier => earlier.trans later))
    | pending_peer_config_step entry

theorem setPeerCmd_retained (a : PeerAttrs) : RetainsCall (setPeerCmd a) := by
  apply retains_of_preserves
  intro entry
  apply (ensures_iff (setPeerCmd a) (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr
  change Preserves (fun w => Retained entry (view w)) _
  rw [← Config.setPeerCmd_source]
  unfold Config.setPeerCmdSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Config.peerConfigUpdateSource
       exact (peerConfigUpdateSource_retained _ _ _ _ _).wp (Retained entry)
         (fun _ _ later earlier => earlier.trans later))
    | pending_peer_config_step entry

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing

theorem peer_configuration (attrs : PeerAttrs) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (setPeerCmd attrs) :=
  PendingReception.native_preserves _ (ConfiguredCommand.command attrs)
    (CurrentSlots.Configuration.command attrs) (PendingTickets.setPeerCmd_retained attrs) seen

end Leanux.Proofs.WG.Noise.PendingSession
