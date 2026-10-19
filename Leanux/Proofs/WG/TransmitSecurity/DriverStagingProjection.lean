import Leanux.Proofs.WG.TransmitSecurity.DriverProjectionBase

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Leanux.Proofs.WG.Origins.HandshakeSources
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}

set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem staging_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    StateProjectsPrefix ρ id (stagingObserved g pid) (stagingObserved a pid) := by
  unfold stagingObserved
  repeat' first
    | (maintenance_head AuthenticatedEffects.PacketEffects.noKeyWith; exact AuthenticatedEffects.PacketEffects.noKey_projects ρ (effectOps_projects h) _ _ _ _)
    | (maintenance_head Hooks.selection; exact h.selection _)
    | (maintenance_head Hooks.reserve; exact h.reserve _)
    | (maintenance_head Hooks.allocate; exact h.allocate _)
    | (maintenance_head Hooks.create; exact h.create _ _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem keepalive_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    StateProjectsPrefix ρ id (keepaliveObserved g pid) (keepaliveObserved a pid) := by
  unfold keepaliveObserved
  repeat' first
    | (maintenance_head Hooks.keepalivePrepare; exact h.keepalivePrepare _)
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem transmit_projects (h : HooksProjects ρ g a) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix ρ id (transmitObserved g family addr packets mtu) (transmitObserved a family addr packets mtu) := by
  unfold transmitObserved
  repeat' first
    | (maintenance_head Hooks.front; exact h.front _ _ _ _)
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem expired_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    StateProjectsPrefix ρ id (expiredKeepaliveObserved g pid) (expiredKeepaliveObserved a pid) := by
  exact AuthenticatedEffects.TimerEffects.expiredKeepalive_projects ρ (effectOps_projects h)
    _ _ (keepalive_projects h) pid

theorem persistent_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    StateProjectsPrefix ρ id (persistentObserved g pid) (persistentObserved a pid) := by
  exact AuthenticatedEffects.TimerEffects.persistent_projects ρ (effectOps_projects h)
    _ _ (keepalive_projects h) pid

theorem timer_projects (h : HooksProjects ρ g a) (pid : PeerId) (t : PeerTimer) :
    StateProjectsPrefix ρ id (timerObserved g pid t) (timerObserved a pid t) := by
  cases t with
  | retransmitHandshake => exact HandshakeSecurity.StagedDisposal.Effects.retransmit_projects ρ (effectOps_projects h) _ _ h.peerRelease _ _ h.stagedPurge _
  | sendKeepalive => exact expired_projects h _
  | newHandshake => exact HandshakeSecurity.StagedDisposal.Effects.newHandshake_projects ρ (effectOps_projects h) _ _ h.peerRelease _
  | zeroKeyMaterial => exact Projection.state_lift ρ _
  | persistentKeepalive => exact persistent_projects h _

theorem response_projects (h : HooksProjects ρ g a) (pid : PeerId) :
    StateProjectsPrefix ρ id (responseWith (handshakeOps g) pid) (responseWith (handshakeOps a) pid) := by
  unfold responseWith
  dsimp only [handshakeOps]
  repeat' first
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem afterMac_projects (h : HooksProjects ρ g a) (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    StateProjectsPrefix ρ id (afterMacWith (handshakeOps g) msg src loaded mac)
      (afterMacWith (handshakeOps a) msg src loaded mac) := by
  unfold afterMacWith
  dsimp only [handshakeOps]
  repeat' first
    | (maintenance_head responseWith; exact response_projects h _)
    | (maintenance_head keepaliveObserved; exact keepalive_projects h _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem reception_projects (h : HooksProjects ρ g a) (msg : List UInt8) (src : SkbSource) :
    StateProjectsPrefix ρ id (receptionWith (handshakeOps g) msg src)
      (receptionWith (handshakeOps a) msg src) := by
  unfold receptionWith
  dsimp only [handshakeOps]
  repeat' first
    | (maintenance_head afterMacWith; exact afterMac_projects h _ _ _ _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem handshake_projects (h : HooksProjects ρ g a) :
    StateProjectsPrefix ρ id (handshakeObserved g) (handshakeObserved a) := by
  exact h.handshake _ _ _ _ h.session (keepalive_projects h)

theorem receiveTail_projects (h : HooksProjects ρ g a) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateProjectsPrefix ρ id (receiveTailObserved g pid pkt confirmed) (receiveTailObserved a pid pkt confirmed) := by
  unfold receiveTailObserved
  repeat' first
    | (maintenance_head AuthenticatedEffects.PacketEffects.prepareWith; exact AuthenticatedEffects.PacketEffects.prepare_projects ρ (effectOps_projects h) _ _)
    | (maintenance_head stagingObserved; exact staging_projects h _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

theorem consume_projects (h : HooksProjects ρ g a) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateProjectsPrefix ρ id (consumeObserved g pid pkt ep) (consumeObserved a pid pkt ep) := by
  unfold consumeObserved
  repeat' first
    | (maintenance_head receiveTailObserved; exact receiveTail_projects h _ _ _)
    | (maintenance_head Hooks.session; exact h.session _)
    | (maintenance_head Hooks.confirmation; exact h.confirmation _ _)
    | (maintenance_head Hooks.peerRelease; exact h.peerRelease _)
    | driver_state_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
