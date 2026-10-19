import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
import Leanux.Proofs.WG.Config.GetterCleanupFrames
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

theorem wheel_metadata (g : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) :
    getterMetadata (wheelPlacementState g pid p timer expires clk)=getterMetadata g := by
  unfold wheelPlacementState
  split <;> simp only [getterMetadata,Option.map_map,Function.comp_def] <;> rfl
/-- Metadata projects the three already-proved exact timer effects. This
does not add readiness, mode, timer-presence or clock assumptions to the caller. -/
theorem arm_metadata (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : Option UInt64) (g final : WGWorld) (a b : Ambient) (p : Peer)
    (resident : peerAt g pid=some p)
    (run : ((armTimer pid timer delay caller).run g).run a=.ok (((),final),b)) :
    getterMetadata final=getterMetadata g := by
  cases mode : a.armRecords with
  | false =>
    rw [armTimer_off_effect pid timer delay caller g p resident a b final mode run]
    exact wheel_metadata _ _ _ _ _ _
  | true =>
    cases caller with
    | none =>
      have ambientRead : ((getAmbient : WG.M Ambient).run g).run a=.ok ((a,g),a) := rfl
      have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run a=
          ((AmbientM.hidden .modTimerArm).run a >>= fun (bytes,next)=>.ok ((bytes,g),next)) := rfl
      simp only [armTimer,StateT.run_bind,StateT.run_get,pure_bind] at run
      rw [ambientRead] at run
      simp only [bind,Except.bind,mode,Bool.not_true,Bool.false_eq_true,ite_false] at run
      change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run a >>= _) = _ at run
      rw [hiddenRead] at run
      cases read : (AmbientM.hidden .modTimerArm).run a with
      | error stop => rw [read] at run; cases run
      | ok out => rw [read] at run; cases out; cases run
    | some caller =>
      by_cases same : p.timer timer=some (caller+delay.toUInt64)
      · obtain ⟨now,unit,_,_,effect⟩ :=
          armTimer_sameExpiry_effect pid timer delay caller g p resident same a b final mode run
        rw [effect]
        rfl
      · obtain ⟨now,unit,clk,_,_,effect⟩ :=
          armTimer_changedExpiry_effect pid timer delay caller g p resident same a b final mode run
        rw [effect,wheel_metadata]
        rfl
theorem guarded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView getterMetadata (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  change (((modPeerTimerGuard pid).run g).run a >>= fun ((allowed,current),inputs)=>
    ((if allowed then armTimer pid timer delay caller else pure () : WG.M Unit).run current).run inputs)=_ at run
  cases device : g.dev with
  | none =>
    simp [modPeerTimerGuard,WG.andM,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peers[pid]? with
    | none =>
      simp [modPeerTimerGuard,WG.andM,getDev,getPeer,device,found,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases checked : ((modPeerTimerGuard pid).run g).run a with
      | error stop => rw [checked] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed,current⟩,inputs⟩ := out
        have same := (modPeerTimerGuard_input_effect pid d p found
          g current a inputs allowed device checked).2.1
        subst current
        rw [checked] at run
        cases allowed with
        | false => cases run; rfl
        | true =>
          cases result
          exact arm_metadata pid timer delay caller g final inputs b p
            (by simp [peerAt,device,found]) run
theorem initiated (pid : PeerId) : SameView getterMetadata (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  exact ((callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).factor getterMetadata).bind
    (fun caller=>((jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).factor getterMetadata).bind
      (fun jitter=>guarded_arm pid .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) caller))
def state_metadata (s : Campaign2.State) : GetterMetadata :=
  s.device.map fun d=>(sendConfiguration d,s.nlSock7,s.fixtureNetDevices)
theorem wheel_view_metadata (entry : Campaign2.State) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) :
    state_metadata (wheelPlacementView entry pid p timer expires clk) =
      state_metadata entry := by
  unfold wheelPlacementView
  split <;> simp only [state_metadata,Option.map_map,Function.comp_def] <;> rfl
theorem arm_effect_metadata (entry : Campaign2.Snapshot) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (delay : Nat) (final : Campaign2.State)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    state_metadata final=state_metadata entry.wg := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩ := effect
    split at effect
    · rw [effect]; rfl
    · obtain ⟨clk,effect⟩ := effect
      rw [effect,wheel_view_metadata]
      rfl
  · rw [effect,wheel_view_metadata]
theorem traversal (pid : PeerId) : SameView getterMetadata (timersTraversal pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases device : g.dev with
  | none =>
    simp [timersTraversal,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [timersTraversal,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := timersTraversal_effect pid d p resident (Campaign2.snapshot g a)
        g a result final b ⟨rfl,device⟩ run
      split at effect
      · exact arm_effect_metadata (Campaign2.snapshot g a) pid p .persistentKeepalive
          (p.persistentKeepaliveInterval*HZ) (Campaign2.snapshot final b).wg effect
      · exact congrArg state_metadata effect
theorem delete_timer (pid : PeerId) (timer : PeerTimer) :
    SameView getterMetadata (delTimer pid timer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
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
      have effect := delTimer_exact pid timer p (Campaign2.snapshot g a)
        g a result final b ⟨rfl,by change peerAt g pid=some p; simp [peerAt,device,resident]⟩ run
      have projected := congrArg getterMetadataObservation effect
      change getterMetadata final = _ at projected
      rw [projected]
      simp only [getterMetadataObservation,delTimerView,Campaign2.snapshot,Campaign2.core,getterMetadata,Option.map_map,Function.comp_def]
      rfl

end Leanux.Proofs.WG.Config.GetterCleanup
