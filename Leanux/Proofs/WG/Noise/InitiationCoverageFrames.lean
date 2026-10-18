import Leanux.Proofs.WG.Noise.InitiationCallerClaims
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames
import Leanux.Proofs.WG.Noise.TagCoverageModel
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG TimerDiscipline

/-- The pure projection of the existing exact wheel-placement effect. -/
theorem wheelPlacementState_tags (entry : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) (ambient : Ambient) (resident : peerAt entry pid = some p) :
    responseTagMap (wheelPlacementState entry pid p timer expires clk).dev =
      responseTagMap entry.dev := by
  cases device : entry.dev with
  | none => simp [peerAt,device] at resident
  | some d =>
    have found : d.peers[pid]? = some p := by simpa [peerAt,device] using resident
    have projection :
        (wheelPlacementState entry pid p timer expires clk).dev =
        (wheelPlacementView (Campaign2.snapshot entry ambient).wg pid p timer expires clk).device := by
      cases placed : TimerWheel.place p timer expires clk <;>
        simp only [wheelPlacementState,wheelPlacementView,placed] <;> rfl
    rw [projection]
    simpa only [Campaign2.snapshot,Campaign2.core,device] using
      ResponseSuffix.wheelPlacementView_tags (Campaign2.snapshot entry ambient).wg d pid p timer expires clk device found

theorem armTimer_tags_of_resident (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (g : WGWorld) (ambient : Ambient)
    (final : WGWorld) (after : Ambient) (p : Peer)
    (resident : peerAt g pid = some p)
    (run : ((armTimer pid timer delay caller).run g).run ambient = .ok (((),final),after)) :
    responseTagMap final.dev = responseTagMap g.dev := by
  cases mode : ambient.armRecords with
  | false =>
    rw [armTimer_off_effect pid timer delay caller g p resident ambient after final mode run]
    exact wheelPlacementState_tags g pid p timer _ _ ambient resident
  | true =>
    cases caller with
    | none =>
      have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient = .ok ((ambient,g),ambient) := rfl
      have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
          ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes,next) => .ok ((bytes,g),next)) := rfl
      simp only [armTimer,StateT.run_bind,StateT.run_get,pure_bind] at run
      rw [ambientRead] at run
      simp only [bind,Except.bind,mode,Bool.not_true,Bool.false_eq_true,ite_false] at run
      change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
      rw [hiddenRead] at run
      cases read : (AmbientM.hidden .modTimerArm).run ambient with
      | error stop => rw [read] at run; cases run
      | ok out => rw [read] at run; cases out; cases run
    | some caller =>
      by_cases same : p.timer timer = some (caller + delay.toUInt64)
      · obtain ⟨now,unit,_,_,effect⟩ := armTimer_sameExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        rfl
      · obtain ⟨now,unit,clk,_,_,effect⟩ := armTimer_changedExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        exact wheelPlacementState_tags _ pid p timer _ _ ambient resident

/-- The actual guard supplies residency and excludes malformed missing-peer
states before an arm. All three concrete arming effects preserve global tags. -/
theorem guardedArm_tag_frame (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (entry : Option Device) :
    Ensures (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  change (((modPeerTimerGuard pid).run g).run ambient >>= fun ((allowed,current),inputs) =>
    ((if allowed then armTimer pid timer delay caller else pure () : WG.M Unit).run current).run inputs) = _ at run
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
      cases checked : ((modPeerTimerGuard pid).run g).run ambient with
      | error stop => rw [checked] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed,current⟩,inputs⟩ := out
        have effect := modPeerTimerGuard_input_effect pid d p found
          g current ambient inputs allowed device checked
        have same := effect.2.1
        subst current
        rw [checked] at run
        cases allowed with
        | false => cases run; exact pre
        | true =>
          cases result
          exact (armTimer_tags_of_resident pid timer delay caller g inputs final after p
            (by simp [peerAt,device,found]) run).trans pre

theorem timersHandshakeInitiated_spec_tagMap_variant (pid : PeerId) (entry : Option Device) :
    Ensures (timersHandshakeInitiated pid)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  unfold timersHandshakeInitiated
  refine ensures_bind (Q := fun _ g => responseTagMap g.dev = responseTagMap entry) _ _ ?_ ?_
  · intro g ambient caller final after pre run
    rw [(callerJiffies_input_effect _ g final ambient after caller run).1]
    exact pre
  · intro caller
    refine ensures_bind _ _ (jitter_wg_spec
      (fun g => responseTagMap g.dev = responseTagMap entry) .retransmitJitter) ?_
    intro jitter
    exact guardedArm_tag_frame pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller entry

theorem initiationTraversalFinish_tag_frame (pid : PeerId) (message : List UInt8)
    (entry : Option Device) :
    Ensures (initiationTraversalFinish pid message)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  have source : initiationTraversalFinish pid message = (do
      timersAnyAuthenticatedPacketSent pid
      let now ← hiddenClock64 .initLastSentAgain
      (do let p ← getPeer pid; setPeer pid {p with lastSentHandshake := now})
      sendBufferToPeer pid message
      timersHandshakeInitiated pid) := by
    simp only [initiationTraversalFinish,bind_assoc]
  rw [source]
  refine ensures_bind _ _ (ResponseSuffix.delTimer_tag_frame pid .sendKeepalive entry) ?_
  intro u
  refine ensures_bind (Q := fun _ g => responseTagMap g.dev = responseTagMap entry) _ _ ?_ ?_
  · intro g ambient now final after pre run
    exact (ResponseCaller.clock_tag_frame _ g ambient now final after run).trans pre
  · intro now
    refine ensures_bind (Q := fun _ g => responseTagMap g.dev = responseTagMap entry) _ _ ?_ ?_
    · intro g ambient result final after pre run
      exact (ResponseCaller.lastSent_tag_frame pid now g ambient result final after run).trans pre
    · intro u
      refine ensures_bind _ _ (sendBufferToPeer_spec_tagMap_variant pid message entry) ?_
      intro u
      exact timersHandshakeInitiated_spec_tagMap_variant pid entry

theorem initiationTraversalSuffix_tag_frame (pid : PeerId) (message : Option (List UInt8))
    (entry : Option Device) :
    Ensures (initiationTraversalSuffix pid message)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  cases message with
  | none =>
    intro g ambient result final after pre run
    cases run
    exact pre
  | some message =>
    exact ensures_bind _ _ (ResponseSuffix.traversal_tag_frame pid entry)
      (fun _ => initiationTraversalFinish_tag_frame pid message entry)


end Leanux.Proofs.WG.Noise.InitiationCaller
