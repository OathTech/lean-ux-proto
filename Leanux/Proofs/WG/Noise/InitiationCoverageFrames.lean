import Leanux.Proofs.WG.Noise.InitiationArmRulesSource
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
    responseTagMap final.dev = responseTagMap g.dev :=
  armTimer_deviceView_of_resident responseTagMap pid timer
    (fun g p expires clk resident =>
      wheelPlacementState_tags g pid p timer expires clk ambient resident)
    delay caller g ambient final after p resident run

/-- The actual guard supplies residency and excludes malformed missing-peer
states before an arm. All three concrete arming effects preserve global tags. -/
theorem guardedArm_tag_frame (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (entry : Option Device) :
    Ensures (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  exact guardedArm_deviceView responseTagMap pid timer
    (fun g p expires clk resident =>
      wheelPlacementState_tags g pid p timer expires clk ambient resident)
    delay caller entry g ambient result final after pre run

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
