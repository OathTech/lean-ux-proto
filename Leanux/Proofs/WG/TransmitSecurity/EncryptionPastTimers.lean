import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTimerFrames
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStaging

/-! Native keepalive and all five timer callbacks preserve the same supplied
historical encryption exclusion, including actual fresh staged admissions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition RetirementSecurity
set_option maxHeartbeats 600000

macro "encryption_past_ready_step" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact ready_frame (LiveFrontier.store_ready _ getDev_sameWGStore) (store getDev_sameWGStore))
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head setPeer; exact ready_set_peer _ _)
  | (rx_retention_head modPeerTimer; exact ready_frame (LiveFrontier.mod_timer _ _ _ _) (mod_timer _ _ _ _))
  | (rx_retention_head sendStagedPackets; exact send _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem keepalive (pid : PeerId) : Preserves (Ready past active) (sendKeepalive pid) := by
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' encryption_past_ready_step

theorem expired_keepalive (pid : PeerId) : Preserves (Ready past active) (expiredSendKeepalive pid) := by
  unfold expiredSendKeepalive
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | encryption_past_ready_step

theorem persistent_keepalive (pid : PeerId) :
    Preserves (Ready past active) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalive
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | encryption_past_ready_step

theorem timer (pid : PeerId) (t : PeerTimer) : Preserves (Ready past active) (timerCallback pid t) := by
  cases t with
  | retransmitHandshake => exact ready_frame (LiveFrontier.timer_callback pid _) (retransmit pid)
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake => exact ready_frame (LiveFrontier.timer_callback pid _) (new_handshake pid)
  | zeroKeyMaterial => exact ready_frame (LiveFrontier.timer_callback pid _) (zero_key pid)
  | persistentKeepalive => exact persistent_keepalive pid

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
