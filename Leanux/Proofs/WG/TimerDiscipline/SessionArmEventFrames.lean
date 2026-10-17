import Leanux.Proofs.WG.TimerDiscipline.SessionArmEventModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Arming preserves the allocation serial and adds zero or one enqueue, in
both recorded and unrecorded timer-arm modes, including early same-expiry arms. -/
theorem peerTimerArmEffect_counters (entry : Campaign2.Snapshot) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (delay : Nat) (final : Campaign2.State)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    final.keypairCounter = entry.wg.keypairCounter ∧
    (final.timerEnqueues = entry.wg.timerEnqueues ∨ final.timerEnqueues = entry.wg.timerEnqueues + 1) := by
  have placement (state : Campaign2.State) (expires clk : UInt64) :
      (wheelPlacementView state pid p timer expires clk).keypairCounter = state.keypairCounter ∧
      ((wheelPlacementView state pid p timer expires clk).timerEnqueues = state.timerEnqueues ∨
       (wheelPlacementView state pid p timer expires clk).timerEnqueues = state.timerEnqueues + 1) := by
    cases h : TimerWheel.place p timer expires clk <;> simp [wheelPlacementView,h]
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩ := effect
    split at effect
    · subst final
      exact ⟨rfl,Or.inl rfl⟩
    · obtain ⟨clk,rfl⟩ := effect
      exact placement _ _ _
  · subst final
    exact placement _ _ _

end Leanux.Proofs.WG.TimerDiscipline
