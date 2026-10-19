import Leanux.Proofs.WG.RetirementSecurity.ZeroTimerOwnership
import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceFrames

/-! All five native timer callbacks retain the exact key account. Actual
keepalive staging uses the already derived allocation and compatible current
slot; clear-work admission touches only its independently acquired peer loan. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits HolderKeepalive

theorem purge_points (pid : PeerId) : SameView ownershipPointView (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold purgeStagedPackets
  repeat' ownership_source_step initial

theorem retransmit_points (pid : PeerId) : SameView ownershipPointView (expiredRetransmitHandshake pid) := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold expiredRetransmitHandshake
  simp (config:={zeta:=false}) only [branch,branchCmp,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_ownership _ _).wp (·=initial))
    | (rx_retention_head modPeerTimer; exact (modPeerTimer_ownership _ _ _ _).wp (·=initial))
    | (rx_retention_head purgeStagedPackets; exact (purge_points _).wp (·=initial))
    | (rx_retention_head clearPeerEndpointSrc; exact (HolderDevice.clear_endpoint_points _).wp (·=initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_ownership _ _).wp (·=initial))
    | ownership_source_step initial

theorem new_points (pid : PeerId) : SameView ownershipPointView (expiredNewHandshake pid) :=
  (HolderDevice.clear_endpoint_points pid).bind (fun _=>sendQueued_ownership pid false)

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Ready temporary) (modPeerTimer site pid timer delay) :=
  HolderDevice.join (HolderResponse.points (MaintenanceCall.erases (.modifyTimer site pid timer delay))
    (MaintenanceCall.allocation (.modifyTimer site pid timer delay)) (modPeerTimer_ownership site pid timer delay))
    (CurrentSlots.modPeerTimer_preserves site pid timer delay)

macro "holder_timer_ready_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply HolderKeepalive.update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     rw [←bind_assoc]
     apply preserves_bind
     · apply HolderKeepalive.update <;> intro p <;> rfl
     intro u)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact HolderDevice.store getDev_sameWGStore)
  | (rx_retention_head sendKeepalive; exact HolderKeepalive.keepalive _)
  | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem keepalive (pid : PeerId) : Preserves (Ready temporary) (expiredSendKeepalive pid) := by
  unfold expiredSendKeepalive
  simp (config:={zeta:=false}) only [branch,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' holder_timer_ready_step

theorem persistent (pid : PeerId) : Preserves (Ready temporary) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalive
  simp (config:={zeta:=false}) only [branch]
  repeat' holder_timer_ready_step

theorem passive (pid : PeerId) (timer : PeerTimer)
    (points : SameView ownershipPointView (timerCallback pid timer)) :
    Preserves (Ready temporary) (timerCallback pid timer) :=
  HolderDevice.join (HolderResponse.points (TimerCallbackCall.erases (.dispatch pid timer))
    (TimerCallbackCall.allocation (.dispatch pid timer)) points) (CurrentSlots.Timer.callback pid timer)

theorem callback (pid : PeerId) (timer : PeerTimer) : Preserves (Ready temporary) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake=>exact passive pid .retransmitHandshake (retransmit_points pid)
  | sendKeepalive=>exact keepalive pid
  | newHandshake=>exact passive pid .newHandshake (new_points pid)
  | zeroKeyMaterial=>exact passive pid .zeroKeyMaterial (zero_timer_ownership pid)
  | persistentKeepalive=>exact persistent pid

end Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys
