import Leanux.Proofs.WG.Roaming.RemoteConfigurationFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent

theorem out_retained (entry : RemoteMap) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Ensures (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret : WG.M Int)
      (Retained entry) (fun _=>Retained entry) :=
  ensures_bind _ _ (peerPut_remotes peer entry) (fun _ =>
    ensures_bind _ _ (of_frame entry _ (ambient_frame (AmbientM.branch _ _)))
      (fun _ => (ensures_iff _ _ _).mpr (preserves_pure ret)))

theorem finish_retained (entry : RemoteMap) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Ensures (peerTailFinishSource attrs peer pid ret) (Retained entry) (fun _=>Retained entry) := by
  refine (ensures_iff (peerTailFinishSource attrs peer pid ret) (Retained entry) (fun _=>Retained entry)).mpr ?_
  change Preserves (Retained entry) _
  rw [HolderConfigTail.finish_factor]
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head HolderConfigTail.setup; exact (keepaliveSetup_frame _ _ _).wp (RemoteRetained entry))
    | (rx_retention_head sendKeepalive; exact (ensures_iff _ _ _).mp (sendKeepalive_remotes _ entry))
    | (rx_retention_head sendStagedPackets; exact (ensures_iff _ _ _).mp (sendStagedPackets_remotes _ entry))
    | (rx_retention_head peerPut; exact (ensures_iff _ _ _).mp (peerPut_remotes _ entry))
    | (rx_retention_head getDev; exact (RemoteCompletion.store_remotes getDev_sameWGStore).wp (RemoteRetained entry))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem tail_retained (entry : RemoteMap) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    Ensures (peerConfigTailSource attrs peer pid) (Retained entry) (fun _=>Retained entry) := by
  rw [peerConfigTailSource_factor]
  refine (ensures_iff (peerAllowedIpsSource attrs peer pid (peerTailFinishSource attrs peer pid))
    (Retained entry) (fun _=>Retained entry)).mpr ?_
  exact Index.ConfigurationIndex.allowedIps_rule _ _ attrs peer pid _
    (fun ip => (Config.AllowedFrame.allowed RemoteMaintenance.allowedContracts pid ip).wp (RemoteRetained entry))
    (fun ret => (ensures_iff _ _ _).mp (out_retained entry attrs peer ret))
    (fun ret => (ensures_iff _ _ _).mp (finish_retained entry attrs peer pid ret))

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
