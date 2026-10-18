import Leanux.Proofs.WG.TransmitSecurity.NonceTimerFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceCallers

/-! Exact allocation observers for all five original timer callbacks.
Timer detachment and scheduling are the caller's separate obligations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def expiredKeepaliveObserved (pid : PeerId) : WGPrefix Allocation Unit := do
  keepaliveObserved pid
  if ← liftWGPrefix (branch .keepaliveNeedAnother (← liftWGPrefix (getPeer pid)).timerNeedAnotherKeepalive) then
    liftWGPrefix (setPeer pid { (← liftWGPrefix (getPeer pid)) with timerNeedAnotherKeepalive := false })
    liftWGPrefix (discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)

def persistentObserved (pid : PeerId) : WGPrefix Allocation Unit := do
  if ← liftWGPrefix (branch .persistentKeepaliveInterval ((← liftWGPrefix (getPeer pid)).persistentKeepaliveInterval != 0)) then
    keepaliveObserved pid

def timerObserved (pid : PeerId) : PeerTimer → WGPrefix Allocation Unit
  | .retransmitHandshake => liftWGPrefix (expiredRetransmitHandshake pid)
  | .sendKeepalive => expiredKeepaliveObserved pid
  | .newHandshake => liftWGPrefix (expiredNewHandshake pid)
  | .zeroKeyMaterial => liftWGPrefix (expiredZeroKeyMaterial pid)
  | .persistentKeepalive => persistentObserved pid

theorem expiredKeepaliveObserved_erases (pid : PeerId) :
    ErasesStatePrefix (expiredKeepaliveObserved pid) (expiredSendKeepalive pid) := by
  unfold expiredKeepaliveObserved expiredSendKeepalive
  apply erasesStatePrefix_bind (keepaliveObserved_erases pid)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro another
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro q
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    exact erasesStatePrefix_lift _
  · exact erasesStatePrefix_pure _

theorem persistentObserved_erases (pid : PeerId) :
    ErasesStatePrefix (persistentObserved pid) (expiredSendPersistentKeepalive pid) := by
  unfold persistentObserved expiredSendPersistentKeepalive
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro enabled
  split
  · exact keepaliveObserved_erases pid
  · exact erasesStatePrefix_pure _

theorem timerObserved_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (timerObserved pid timer) (timerCallback pid timer) := by
  cases timer
  · exact erasesStatePrefix_lift _
  · exact expiredKeepaliveObserved_erases pid
  · exact erasesStatePrefix_lift _
  · exact erasesStatePrefix_lift _
  · exact persistentObserved_erases pid

private theorem reset_timer (pid : PeerId) : SameView view
    (discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) :=
  (Frames.timer_arm _ _ _ _).map (fun _ => ())

macro "nonce_timer_observer_step" : tactic => `(tactic| first
  | (nonce_source_head keepaliveObserved; exact keepaliveObserved_safe _)
  | (nonce_source_head getPeer; exact Frames.lift_frame (Frames.peer_read _))
  | (nonce_source_head setPeer; exact Frames.lift_frame (Frames.peer_write _ _))
  | (nonce_source_head branch; exact Frames.lift_frame (Frames.ambient _))
  | (nonce_source_head discard; exact Frames.lift_frame (reset_timer _))
  | (nonce_source_head Pure.pure
     exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

theorem timerObserved_safe (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (timerObserved pid timer) := by
  cases timer
  · exact Frames.lift_preserves (Frames.expired_retransmit pid)
  · change StatePrefixPreserves _ _ (expiredKeepaliveObserved pid)
    unfold expiredKeepaliveObserved
    repeat' nonce_timer_observer_step
  · exact Frames.lift_preserves (Frames.expired_new pid)
  · exact Frames.lift_preserves (Frames.expired_zero pid)
  · change StatePrefixPreserves _ _ (persistentObserved pid)
    unfold persistentObserved
    repeat' nonce_timer_observer_step

end Leanux.Proofs.WG.TransmitSecurity.Nonce
