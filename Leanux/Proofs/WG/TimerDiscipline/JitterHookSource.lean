import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource

/-! All-mode effects of the original jittered timer arms. The existing loop
supplies the actual bounded jitter; caller, guard and wheel failures remain exact. -/

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise

theorem optional_arm_effect (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : Option UInt64) (g final : WGWorld) (ambient after : Ambient)
    (p : Peer) (resident : peerAt g pid = some p)
    (mode : caller.isSome = ambient.armRecords)
    (run : ((armTimer pid timer delay caller).run g).run ambient = .ok (((),final),after)) :
    peerTimerArmEffect (Campaign2.snapshot g ambient) pid p timer delay
      (Campaign2.snapshot final after).wg := by
  cases enabled : ambient.armRecords with
  | false =>
    have effect := armTimer_off_effect pid timer delay caller g p resident ambient after final enabled run
    simp only [peerTimerArmEffect,Campaign2.snapshot,enabled,Bool.false_eq_true,ite_false]
    rw [effect]
    cases placement : TimerWheel.place p timer (g.jiffiesLast.getD 0 + delay.toUInt64) (g.jiffiesLast.getD 0) <;>
      simp only [wheelPlacementState,wheelPlacementView,placement]
    all_goals rfl
  | true =>
    cases caller with
    | none => simp [enabled] at mode
    | some caller =>
      have effect := armTimer_recorded pid timer delay caller p (Campaign2.snapshot g ambient)
        g ambient () final after ⟨rfl,enabled,resident⟩ run
      obtain ⟨now,unit,lo,hi,exactState⟩:=effect
      simp only [peerTimerArmEffect,Campaign2.snapshot,enabled,ite_true]
      exact ⟨caller,now,unit,lo,hi,exactState⟩

theorem jitteredArm_effect (callerSite jitterSite : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (baseDelay : Nat) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (jitteredArm callerSite jitterSite pid timer baseDelay)
      (fun s=>s=entry ∧ s.wg.device=some d)
      (fun _ final=>∃jitter, jitter < HZ/3 ∧
        if d.running && !p.isDead then
          peerTimerArmEffect entry pid p timer (baseDelay+jitter) final.wg
        else final.wg=entry.wg) := by
  intro g ambient value final after pre run
  obtain ⟨rfl,device⟩:=pre
  change g.dev=some d at device
  change (((callerJiffies callerSite).run g).run ambient >>= fun ((caller,current),inputs)=>
    ((do
      let jitter←jitterBelowRekeyTimeout jitterSite
      if ←modPeerTimerGuard pid then armTimer pid timer (baseDelay+jitter) caller
      : WG.M Unit).run current).run inputs) = _ at run
  cases read : ((callerJiffies callerSite).run g).run ambient with
  | error stop => rw [read] at run; cases run
  | ok out =>
    obtain ⟨⟨caller,current⟩,inputs⟩:=out
    obtain ⟨same,readMode,supplied⟩:=callerJiffies_input_effect callerSite g current ambient inputs caller read
    subst current
    rw [read] at run
    change (((jitterBelowRekeyTimeout jitterSite).run g).run inputs >>= fun ((jitter,current),drawn)=>
      ((do if ←modPeerTimerGuard pid then armTimer pid timer (baseDelay+jitter) caller
        : WG.M Unit).run current).run drawn) = _ at run
    cases draw : ((jitterBelowRekeyTimeout jitterSite).run g).run inputs with
    | error stop => rw [draw] at run; cases run
    | ok out =>
      obtain ⟨⟨jitter,current⟩,drawn⟩:=out
      obtain ⟨same,drawMode,bound⟩:=jitter_input_effect jitterSite g current inputs drawn jitter draw
      subst current
      rw [draw] at run
      change (((modPeerTimerGuard pid).run g).run drawn >>= fun ((allowed,current),checked)=>
        ((if allowed then armTimer pid timer (baseDelay+jitter) caller else pure ()
          : WG.M Unit).run current).run checked) = _ at run
      cases guard : ((modPeerTimerGuard pid).run g).run drawn with
      | error stop => rw [guard] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed,current⟩,checked⟩:=out
        obtain ⟨answer,same,guardMode⟩:=modPeerTimerGuard_input_effect pid d p resident
          g current drawn checked allowed device guard
        subst current
        rw [guard] at run
        have checkedMode : checked.armRecords=ambient.armRecords :=
          guardMode.trans (drawMode.trans readMode)
        refine ⟨jitter,bound,?_⟩
        cases allowed with
        | false =>
          cases run
          simp only [←answer,Bool.false_eq_true,ite_false]
          rfl
        | true =>
          change ((armTimer pid timer (baseDelay+jitter) caller).run g).run checked = _ at run
          cases value
          have native:=optional_arm_effect pid timer (baseDelay+jitter) caller g final checked after
            p (by simp [peerAt,device,resident]) (supplied.trans checkedMode.symm) run
          simp only [←answer,ite_true]
          unfold peerTimerArmEffect at native ⊢
          have modeProjection : (Campaign2.snapshot g checked).ambient.armRecords =
              (Campaign2.snapshot g ambient).ambient.armRecords := checkedMode
          rw [modeProjection] at native
          exact native

theorem handshakeInitiated_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersHandshakeInitiated pid)
      (fun s=>s=entry ∧ s.wg.device=some d)
      (fun _ final=>∃jitter, jitter < HZ/3 ∧
        if d.running && !p.isDead then
          peerTimerArmEffect entry pid p .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) final.wg
        else final.wg=entry.wg) := by
  rw [handshakeInitiated_source]
  exact jitteredArm_effect _ _ _ _ _ _ _ resident entry

theorem dataSent_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersDataSent pid)
      (fun s=>s=entry ∧ s.wg.device=some d)
      (fun _ final=>if p.timerPending .newHandshake then final.wg=entry.wg
        else ∃jitter, jitter < HZ/3 ∧
          if d.running && !p.isDead then
            peerTimerArmEffect entry pid p .newHandshake
              (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS+jitter) final.wg
          else final.wg=entry.wg) := by
  intro g ambient value final after pre run
  obtain ⟨rfl,device⟩:=pre
  change g.dev=some d at device
  let inputs : Ambient := {ambient with steps := ambient.steps.push {decision := .timersDataSentNotPending, outcome := !(p.timerPending .newHandshake), netRx := ambient.netRxSection}}
  have beforeArm : ((dataSentPrefix pid).run g).run ambient =
      .ok ((!p.timerPending .newHandshake,g),inputs) := by
    simp [dataSentPrefix,getPeer,getDev,device,resident,branch,AmbientM.branch,inputs]
    rfl
  rw [dataSent_source] at run
  change (((dataSentPrefix pid).run g).run ambient >>= fun ((ready,current),next)=>
    ((if ready then jitteredArm .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
      (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS) else pure () : WG.M Unit).run current).run next) = _ at run
  rw [beforeArm] at run
  cases pending : p.timerPending .newHandshake with
  | true =>
    simp only [pending,Bool.not_true] at run
    cases run
    simp only [ite_true]
    rfl
  | false =>
    simp only [pending,Bool.not_false] at run
    have effect := jitteredArm_effect .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
      (KEEPALIVE_TIMEOUT_TICKS+REKEY_TIMEOUT_TICKS) d p resident (Campaign2.snapshot g inputs)
      g inputs value final after ⟨rfl,device⟩ run
    simp only [Bool.false_eq_true,ite_false]
    obtain ⟨jitter,bound,effect⟩:=effect
    refine ⟨jitter,bound,?_⟩
    exact effect

end Leanux.Proofs.WG.TimerDiscipline
