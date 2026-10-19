import Leanux.Proofs.WG.TimerDiscipline.SessionWheelModel

/-! Only the selected peer can change in the exact zero-key arm effect; this projection reuses the existing wheel-placement transformation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG

theorem placement_other (entry : Campaign2.State) (pid : PeerId) (p : Peer)
    (expires clk : UInt64) :
    OtherPeers entry (wheelPlacementView entry pid p .zeroKeyMaterial expires clk) pid := by
  intro other different
  cases device : entry.device with
  | none => cases place : TimerWheel.place p .zeroKeyMaterial expires clk <;> simp [wheelPlacementView,place,device]
  | some d =>
    cases place : TimerWheel.place p .zeroKeyMaterial expires clk <;>
      simp [wheelPlacementView,place,device,Std.TreeMap.getElem?_insert,Ne.symm different]

theorem arm_zero_other (entry : Campaign2.Snapshot) (pid : PeerId) (p : Peer)
    (final : Campaign2.State)
    (effect : peerTimerArmEffect entry pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final) :
    OtherPeers entry.wg final pid := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩:=effect
    split at effect
    · subst final
      intro other _
      rfl
    · obtain ⟨clk,changed⟩:=effect
      rw [changed]
      let base := {recordedArmPrefixView entry.wg pid .zeroKeyMaterial now unit with timerClk:=some clk}
      have placed := placement_other base pid p (caller+ZERO_KEY_MATERIAL_TICKS.toUInt64) clk
      change OtherPeers entry.wg (wheelPlacementView base pid p .zeroKeyMaterial _ clk) pid
      intro other different
      have point := placed other different
      have baseDevice : base.device=entry.wg.device := rfl
      change (wheelPlacementView base pid p .zeroKeyMaterial _ clk).device.bind
        (fun d=>d.peers[other]?)=base.device.bind (fun d=>d.peers[other]?) at point
      rw [baseDevice] at point
      exact point
  · subst final
    exact placement_other entry.wg pid p _ _

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
