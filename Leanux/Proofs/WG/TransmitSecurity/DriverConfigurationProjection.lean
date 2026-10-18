import Leanux.Proofs.WG.TransmitSecurity.DriverStagingProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem configOut_projects (ρ : E → Option F) (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateProjectsPrefix ρ id (configOut attrs peer ret) (configOut attrs peer ret) := by
  unfold configOut
  repeat' driver_state_step ρ

theorem configTailFinish_projects (h : HooksProjects ρ g a) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateProjectsPrefix ρ id (configTailFinish g attrs peer pid ret) (configTailFinish a attrs peer pid ret) := by
  unfold configTailFinish
  repeat' first
    | (maintenance_head configOut; exact configOut_projects ρ _ _ _)
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | (maintenance_head keepaliveObserved; exact keepalive_projects h _)
    | driver_state_step ρ

theorem configTail_projects (h : HooksProjects ρ g a) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateProjectsPrefix ρ id (configTail g attrs peer pid) (configTail a attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (maintenance_head configOut; exact configOut_projects ρ _ _ _)
    | (maintenance_head configTailFinish; exact configTailFinish_projects h _ _ _ _)
    | driver_state_step ρ

theorem configUpdate_projects (h : HooksProjects ρ g a) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix ρ id (configUpdate g attrs peer flags psk pid) (configUpdate a attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (maintenance_head configOut; exact configOut_projects ρ _ _ _)
    | (maintenance_head configTail; exact configTail_projects h _ _ _)
    | driver_state_step ρ

theorem configPeer_projects (h : HooksProjects ρ g a) (attrs : PeerAttrs) :
    StateProjectsPrefix ρ id (configPeer g attrs) (configPeer a attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (maintenance_head configOut; exact configOut_projects ρ _ _ _)
    | (maintenance_head configUpdate; exact configUpdate_projects h _ _ _ _ _)
    | driver_state_step ρ

theorem configPeers_projects (h : HooksProjects ρ g a) (attrs : DeviceAttrs) :
    StateProjectsPrefix ρ id (configPeers g attrs) (configPeers a attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (maintenance_head configPeer; exact configPeer_projects h _)
    | driver_state_step ρ

theorem configKey_projects (h : HooksProjects ρ g a) (attrs : DeviceAttrs) :
    StateProjectsPrefix ρ id (configKey g attrs) (configKey a attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (maintenance_head configPeers; exact configPeers_projects h _)
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | driver_state_step ρ

theorem configDeviceUpdate_projects (h : HooksProjects ρ g a) (attrs : DeviceAttrs) (flags : UInt32) :
    StateProjectsPrefix ρ id (configDeviceUpdate g attrs flags) (configDeviceUpdate a attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (maintenance_head configKey; exact configKey_projects h _)
    | driver_state_step ρ

theorem configDevice_projects (h : HooksProjects ρ g a) (attrs : DeviceAttrs) :
    StateProjectsPrefix ρ id (configDevice g attrs) (configDevice a attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (maintenance_head configDeviceUpdate; exact configDeviceUpdate_projects h _ _)
    | driver_state_step ρ

theorem open_projects (h : HooksProjects ρ g a) :
    StateProjectsPrefix ρ id (openObserved g) (openObserved a) := by
  unfold openObserved
  repeat' first
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | (maintenance_head keepaliveObserved; exact keepalive_projects h _)
    | driver_state_step ρ

theorem up_projects (h : HooksProjects ρ g a) :
    StateProjectsPrefix ρ id (upObserved g) (upObserved a) := by
  unfold upObserved
  repeat' first
    | (maintenance_head openObserved; exact open_projects h)
    | driver_state_step ρ

theorem envUp_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (envUpObserved g) (envUpObserved a) := by
  unfold envUpObserved
  repeat' first
    | (maintenance_head upObserved; exact (up_projects h).liftWGObserver ρ id)
    | driver_product_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
