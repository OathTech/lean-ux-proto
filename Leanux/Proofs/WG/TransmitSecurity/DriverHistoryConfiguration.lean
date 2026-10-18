import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryStaging

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem configOut_history (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateHistorySafe Safe (configOut attrs peer ret) := by
  unfold configOut
  repeat' driver_state_history_step

theorem configTailFinish_history (h : HooksHistorySafe Safe g) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateHistorySafe Safe (configTailFinish g attrs peer pid ret) := by
  unfold configTailFinish
  repeat' first
    | (driver_history_head configOut; exact configOut_history _ _ _)
    | (driver_history_head stagingObserved; exact staging_history h _)
    | (driver_history_head keepaliveObserved; exact keepalive_history h _)
    | driver_state_history_step

theorem configTail_history (h : HooksHistorySafe Safe g) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateHistorySafe Safe (configTail g attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (driver_history_head configOut; exact configOut_history _ _ _)
    | (driver_history_head configTailFinish; exact configTailFinish_history h _ _ _ _)
    | driver_state_history_step

theorem configUpdate_history (h : HooksHistorySafe Safe g) (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateHistorySafe Safe (configUpdate g attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (driver_history_head configOut; exact configOut_history _ _ _)
    | (driver_history_head configTail; exact configTail_history h _ _ _)
    | driver_state_history_step

theorem configPeer_history (h : HooksHistorySafe Safe g) (attrs : PeerAttrs) :
    StateHistorySafe Safe (configPeer g attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (driver_history_head configOut; exact configOut_history _ _ _)
    | (driver_history_head configUpdate; exact configUpdate_history h _ _ _ _ _)
    | driver_state_history_step

theorem configPeers_history (h : HooksHistorySafe Safe g) (attrs : DeviceAttrs) :
    StateHistorySafe Safe (configPeers g attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (driver_history_head configPeer; exact configPeer_history h _)
    | driver_state_history_step

theorem configKey_history (h : HooksHistorySafe Safe g) (attrs : DeviceAttrs) :
    StateHistorySafe Safe (configKey g attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (driver_history_head configPeers; exact configPeers_history h _)
    | (driver_history_head stagingObserved; exact staging_history h _)
    | driver_state_history_step

theorem configDeviceUpdate_history (h : HooksHistorySafe Safe g) (attrs : DeviceAttrs) (flags : UInt32) :
    StateHistorySafe Safe (configDeviceUpdate g attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (driver_history_head configKey; exact configKey_history h _)
    | driver_state_history_step

theorem configDevice_history (h : HooksHistorySafe Safe g) (attrs : DeviceAttrs) :
    StateHistorySafe Safe (configDevice g attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (driver_history_head configDeviceUpdate; exact configDeviceUpdate_history h _ _)
    | driver_state_history_step

theorem open_history (h : HooksHistorySafe Safe g) :
    StateHistorySafe Safe (openObserved g) := by
  unfold openObserved
  repeat' first
    | (driver_history_head stagingObserved; exact staging_history h _)
    | (driver_history_head keepaliveObserved; exact keepalive_history h _)
    | driver_state_history_step

theorem up_history (h : HooksHistorySafe Safe g) :
    StateHistorySafe Safe (upObserved g) := by
  unfold upObserved
  repeat' first
    | (driver_history_head openObserved; exact open_history h)
    | driver_state_history_step

theorem envUp_history (h : HooksHistorySafe Safe g) :
    ProductHistorySafe Safe (envUpObserved g) := by
  unfold envUpObserved
  repeat' first
    | (driver_history_head upObserved; exact (up_history h).liftWGObserver)
    | driver_product_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
