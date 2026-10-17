import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Every actual arm effect retains owner words and counts. The recorded
prefix may update clocks and unit registration; placement updates only the
selected peer's expiry/wheel fields, without requiring wheel consistency. -/
theorem peerTimerArmEffect_owner_coherent (entry : Campaign2.Snapshot)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (delay : Nat)
    (final : Campaign2.State) (d : Device)
    (device : entry.wg.device = some d) (resident : d.peers[pid]? = some p)
    (coherent : HashedOwnersCoherent d)
    (effect : TimerDiscipline.peerTimerArmEffect entry pid p timer delay final) :
    ∀actual, final.device = some actual → HashedOwnersCoherent actual := by
  have wheel (before : Campaign2.State) (present : before.device = some d)
      (expires clk : UInt64) :
      ∀actual, (TimerDiscipline.wheelPlacementView before pid p timer expires clk).device =
        some actual → HashedOwnersCoherent actual := by
    intro actual found
    cases placed : TimerWheel.place p timer expires clk with
    | kept slot =>
      simp only [TimerDiscipline.wheelPlacementView,placed,present,Option.map_some] at found
      cases found
      exact peerWrite_owner_coherent d pid p _ resident (by cases timer <;> rfl)
        (by cases timer <;> rfl) coherent
    | enqueued slot expiry =>
      simp only [TimerDiscipline.wheelPlacementView,placed,present,Option.map_some] at found
      cases found
      exact peerWrite_owner_coherent d pid p _ resident (by cases timer <;> rfl)
        (by cases timer <;> rfl) coherent
  unfold TimerDiscipline.peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩ := effect
    split at effect
    · rw [effect]
      intro actual found
      change entry.wg.device = some actual at found
      rw [device] at found
      cases found
      exact coherent
    · obtain ⟨clk,effect⟩ := effect
      rw [effect]
      exact wheel {TimerDiscipline.recordedArmPrefixView entry.wg pid timer now unit with timerClk := some clk} device _ _
  · rw [effect]
    exact wheel entry.wg device _ _

/-- Owner-coherence variant of `Keypairs/Frames/WGBase.delTimer_spec`.
The exact owned deletion contract includes the wheel entry. -/
theorem delTimer_spec_ownerCoherent_variant (pid : PeerId) (timer : PeerTimer) :
    Ensures (delTimer pid timer)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun _ g => ∀d, g.dev = some d → HashedOwnersCoherent d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [delTimer,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [delTimer,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := TimerDiscipline.delTimer_exact pid timer p (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl,by simp [Campaign2.Snapshot.peerAt,Campaign2.snapshot,
          Campaign2.core,device,resident]⟩ run
      have changed := congrArg (fun s : Campaign2.Snapshot => s.wg.device) effect
      change final.dev = (Campaign2.snapshot g ambient).wg.device.map
        (fun d => {d with peers := d.peers.insert pid ((p.setTimer timer none).setWheel timer none)}) at changed
      change final.dev = g.dev.map (fun d => {d with peers := d.peers.insert pid ((p.setTimer timer none).setWheel timer none)}) at changed
      rw [device] at changed
      simp only [Option.map_some] at changed
      intro actual found
      rw [changed] at found
      cases found
      exact peerWrite_owner_coherent d pid p _ resident (by cases timer <;> rfl)
        (by cases timer <;> rfl) (pre d device)

/-- Owner-coherence variant of `Keypairs/Frames/WGTransitions.purgeStagedPackets_spec`.
The staged-data purge changes no embedded owner or reference count. -/
theorem purgeStagedPackets_spec_ownerCoherent_variant (pid : PeerId) :
    Ensures (purgeStagedPackets pid)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun _ g => ∀d, g.dev = some d → HashedOwnersCoherent d) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [purgeStagedPackets,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [purgeStagedPackets,getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro actual found
      cases found
      exact peerWrite_owner_coherent {d with txDropped := d.txDropped + p.staged.length}
        pid p {p with staged := []} resident rfl rfl (pre d device)

/-- Owner-coherence variant of `Keypairs/Frames/WGTransitions.modPeerTimer_spec`.
The exact all-mode arm contract supplies every normal wheel effect; caller
clock and wheel failures remain original Stops, including a refused guard. -/
theorem modPeerTimer_spec_ownerCoherent_variant (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) :
    Ensures (modPeerTimer site pid timer delay)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun _ g => ∀d, g.dev = some d → HashedOwnersCoherent d) := by
  intro g ambient result final after pre run
  have missing (absent : peerAt g pid = none) : False := by
    change (((callerJiffies site).run g).run ambient >>= fun ((caller,current),inputs) =>
      ((do
        if ← modPeerTimerGuard pid then
          armTimer pid timer delay caller
          return true
        return false : WG.M Bool).run current).run inputs) = _ at run
    cases read : ((callerJiffies site).run g).run ambient with
    | error stop => rw [read] at run; cases run
    | ok out =>
      obtain ⟨⟨caller,current⟩,inputs⟩ := out
      have unchanged := (TimerDiscipline.callerJiffies_input_effect site g current
        ambient inputs caller read).1
      subst current
      rw [read] at run
      change (((do
        if ← modPeerTimerGuard pid then
          armTimer pid timer delay caller
          return true
        return false : WG.M Bool).run g).run inputs) = _ at run
      cases device : g.dev with
      | none =>
        simp [modPeerTimerGuard,getPeer,getDev,device,invariant,AmbientM.invariant] at run
        cases run
      | some d =>
        have noPeer : d.peers[pid]? = none := by simpa [peerAt,device] using absent
        simp [modPeerTimerGuard,getPeer,getDev,device,noPeer,invariant,AmbientM.invariant] at run
        cases run
  cases device : g.dev with
  | none => exact (missing (by simp [peerAt,device])).elim
  | some d =>
    cases resident : d.peers[pid]? with
    | none => exact (missing (by simp [peerAt,device,resident])).elim
    | some p =>
      obtain ⟨_,effect⟩ := TimerDiscipline.modPeerTimer_effect site pid timer delay d p resident
        (Campaign2.snapshot g ambient) g ambient result final after ⟨rfl,device⟩ run
      cases result with
      | false =>
        simp only [Bool.false_eq_true,ite_false] at effect
        have same := congrArg (fun s : Campaign2.State => s.device) effect
        change final.dev = g.dev at same
        intro actual found
        exact pre actual (same ▸ found)
      | true =>
        simp only [ite_true] at effect
        exact peerTimerArmEffect_owner_coherent (Campaign2.snapshot g ambient) pid p timer delay
          (Campaign2.snapshot final after).wg d device resident (pre d device) effect


end Leanux.Proofs.WG.Index
