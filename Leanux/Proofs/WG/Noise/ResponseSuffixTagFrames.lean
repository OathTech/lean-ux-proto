import Leanux.Proofs.WG.Noise.ResponseCallerClaims
import Leanux.Proofs.WG.Noise.SocketTagFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingLifecycleClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ResponseSuffix
open Leanux Leanux.WG TimerDiscipline

theorem wheelPlacementView_tags (entry : Campaign2.State) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (expires clk : UInt64)
    (device : entry.device = some d) (resident : d.peers[pid]? = some p) :
    responseTagMap (wheelPlacementView entry pid p timer expires clk).device =
      responseTagMap entry.device := by
  unfold wheelPlacementView
  split
  · simp only [device, Option.map_some]
    exact tagMap_write d pid p _ resident (by cases timer <;> rfl)
  · simp only [device, Option.map_some]
    exact tagMap_write d pid p _ resident (by cases timer <;> rfl)

theorem peerTimerArmEffect_tags (entry : Campaign2.Snapshot) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (delay : Nat)
    (final : Campaign2.State) (device : entry.wg.device = some d)
    (resident : d.peers[pid]? = some p)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    responseTagMap final.device = responseTagMap entry.wg.device := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller, now, unit, _, _, effect⟩ := effect
    split at effect
    · rw [effect]; rfl
    · obtain ⟨clk, effect⟩ := effect
      rw [effect]
      exact wheelPlacementView_tags _ d pid p timer _ clk device resident
  · rw [effect]
    exact wheelPlacementView_tags entry.wg d pid p timer _ _ device resident

/-- The original guard reads the peer while preparing its arguments, so a
missing peer cannot yield a normal timer-hook result. -/
theorem modPeerTimer_missing_false (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (g final : WGWorld)
    (ambient after : Ambient) (value : Bool)
    (missing : peerAt g pid = none)
    (run : ((modPeerTimer site pid timer delay).run g).run ambient =
      .ok ((value, final), after)) :
    False := by
  change (((callerJiffies site).run g).run ambient >>= fun ((caller, current), inputs) =>
    ((do
      if ← modPeerTimerGuard pid then
        armTimer pid timer delay caller
        return true
      return false : WG.M Bool).run current).run inputs) = _ at run
  cases read : ((callerJiffies site).run g).run ambient with
  | error stop => rw [read] at run; cases run
  | ok out =>
    obtain ⟨⟨caller, current⟩, inputs⟩ := out
    obtain ⟨unchanged, _, _⟩ := callerJiffies_input_effect site g current
      ambient inputs caller read
    subst current
    rw [read] at run
    cases device : g.dev with
    | none =>
      simp [modPeerTimerGuard, WG.andM, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      have absent : d.peers[pid]? = none := by simpa [peerAt, device] using missing
      simp [modPeerTimerGuard, WG.andM, getDev, getPeer, device, absent,
        invariant, AmbientM.invariant] at run
      cases run

theorem modPeerTimer_missing_tags (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (g final : WGWorld)
    (ambient after : Ambient) (value : Bool)
    (missing : peerAt g pid = none)
    (run : ((modPeerTimer site pid timer delay).run g).run ambient =
      .ok ((value, final), after)) :
    responseTagMap final.dev = responseTagMap g.dev :=
  False.elim (modPeerTimer_missing_false site pid timer delay g final ambient after value missing run)

theorem modPeerTimer_tag_frame (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (entry : Option Device) :
    Ensures (modPeerTimer site pid timer delay)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    simpa only [device] using modPeerTimer_missing_tags site pid timer delay g final ambient after result
      (by simp [peerAt, device]) run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simpa only [device] using modPeerTimer_missing_tags site pid timer delay g final ambient after result
        (by simp [peerAt, device, resident]) run
    | some p =>
      obtain ⟨value, effect⟩ := modPeerTimer_effect site pid timer delay d p resident
        (Campaign2.snapshot g ambient) g ambient result final after ⟨rfl, device⟩ run
      cases result with
      | false =>
        simpa only [Campaign2.snapshot, Campaign2.core, device] using
          congrArg (fun s : Campaign2.State => responseTagMap s.device) effect
      | true =>
        simpa only [Campaign2.snapshot, Campaign2.core, device] using
          peerTimerArmEffect_tags (Campaign2.snapshot g ambient) d pid p timer delay
          (Campaign2.snapshot final after).wg device resident effect

theorem derived_tag_frame (pid : PeerId) (entry : Option Device) :
    Ensures (timersSessionDerived pid)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  change Ensures (modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS >>= fun _ => pure ()) _ _
  refine ensures_bind _ _ (modPeerTimer_tag_frame _ _ _ _ entry) ?_
  intro _ g ambient result final after pre run
  cases run
  exact pre

theorem traversal_tag_frame (pid : PeerId) (entry : Option Device) :
    Ensures (timersTraversal pid)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    simp [timersTraversal, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [timersTraversal, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := timersTraversal_effect pid d p resident (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl, device⟩ run
      split at effect
      · simpa only [Campaign2.snapshot, Campaign2.core, device] using
          peerTimerArmEffect_tags (Campaign2.snapshot g ambient) d pid p .persistentKeepalive
          (p.persistentKeepaliveInterval * HZ) (Campaign2.snapshot final after).wg device resident effect
      · simpa only [Campaign2.snapshot, Campaign2.core, device] using
          congrArg (fun s : Campaign2.State => responseTagMap s.device) effect

theorem delTimer_tag_frame (pid : PeerId) (timer : PeerTimer) (entry : Option Device) :
    Ensures (delTimer pid timer)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    simp [delTimer, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [delTimer, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := delTimer_exact pid timer p (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl, by change peerAt g pid = some p; simp [peerAt,device,resident]⟩ run
      have projected := congrArg (fun s : Campaign2.Snapshot => responseTagMap s.wg.device) effect
      change responseTagMap final.dev = _ at projected
      rw [projected]
      change responseTagMap (g.dev.map fun d =>
        {d with peers := d.peers.insert pid ((p.setTimer timer none).setWheel timer none)}) =
        responseTagMap (some d)
      rw [device]
      exact tagMap_write d pid p _ resident (by cases timer <;> rfl)

end Leanux.Proofs.WG.Noise.ResponseSuffix

