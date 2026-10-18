import Leanux.Proofs.WG.Roaming.HandshakeRemoteModel
import Leanux.Proofs.WG.Roaming.RemotePeerFrames
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Roaming.RemoteSetterFrames
import Leanux.Proofs.WG.Roaming.RemoteCreatorFrames
import Leanux.Proofs.WG.Roaming.RemoteTransportFrames
import Leanux.Proofs.WG.Roaming.InitiationRejectionFrames
import Leanux.Proofs.WG.Index.ResponseIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

theorem sendHandshakeResponse_remotes (pid : PeerId) :
    SameView destinationAt (sendHandshakeResponse pid) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  apply Index.sendResponse_preserves_source pid
    (fun g => destinationAt g = entry) (fun g => destinationAt g = entry)
  · exact fun _ pre => pre
  · intro now
    exact (ensures_iff _ _ _).mpr (modifyPeer_remotes pid (fun p => {p with lastSentHandshake := now}) (fun _ => rfl) entry)
  · exact (ensures_iff _ _ _).mpr (createResponse_remotes pid entry)
  · intro msg
    exact (ensures_iff _ _ _).mpr (addMacToPacket_spec_remotes_variant pid msg entry)
  · exact (ensures_iff _ _ _).mpr (beginSession_endpoints pid entry)
  · exact (ensures_iff _ _ _).mpr (derived_remotes pid entry)
  · exact (ensures_iff _ _ _).mpr (traversal_remotes pid entry)
  · exact (ensures_iff _ _ _).mpr (delTimer_remotes pid .sendKeepalive entry)
  · intro now
    exact (ensures_iff _ _ _).mpr (modifyPeer_remotes pid (fun p => {p with lastSentHandshake := now}) (fun _ => rfl) entry)
  · intro msg
    exact (ensures_iff _ _ _).mpr (sendBufferToPeer_spec_remotes_variant pid msg entry)

theorem retained_of_remote_frame {α : Type} (action : WG.M α)
    (frame : SameView destinationAt action) (entry : RemoteMap) :
    Ensures action (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  intro g ambient result final after pre run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp frame g ambient result final after run]
  exact pre

theorem receiveFinish_remotes (msg : List UInt8) (pid : PeerId) (entry : RemoteMap) :
    Ensures (do
      modifyPeer pid (fun p => {p with rxBytes := p.rxBytes + msg.length})
      modifyDev (rxStatsUpdate msg.length)
      timersAnyAuthenticatedPacketReceived pid
      timersTraversal pid
      peerPut (some pid)) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) :=
    ensures_bind _ _ (retained_of_remote_frame _ (modifyPeer_remotes pid (fun p => {p with rxBytes := p.rxBytes + msg.length}) (fun _ => rfl)) entry)
      (fun _ => ensures_bind _ _ (retained_of_remote_frame _
        (modifyDev_remotes (rxStatsUpdate msg.length) (fun _ => rfl)) entry) (fun _ =>
        ensures_bind _ _ (retained_of_remote_frame _ (delTimer_remotes pid .newHandshake) entry)
          (fun _ => ensures_bind _ _ (retained_of_remote_frame _ (traversal_remotes pid) entry)
            (fun _ => peerPut_remotes (some pid) entry))))


theorem receiveCheckedFinish_remotes (msg : List UInt8) (pid : PeerId) (entry : RemoteMap) :
    Ensures (do
      let peer := some pid
      if ← branch .hsWrongPacket peer.isNone then
        invariant "a wrong type of packet in the handshake queue"
      let some pid := peer | invariant "unreachable"
      let p ← getPeer pid
      setPeer pid {p with rxBytes := p.rxBytes + msg.length}
      modifyDev (rxStatsUpdate msg.length)
      timersAnyAuthenticatedPacketReceived pid
      timersTraversal pid
      peerPut peer) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  let P := fun g => RemoteRetained entry (destinationAt g)
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (Config.branch_state_spec P .hsWrongPacket false)) ?_
  intro value g ambient result final after pre run
  obtain ⟨rfl,kept⟩ := pre
  apply receiveFinish_remotes msg pid entry g ambient result final after kept
  simpa only [Bool.false_eq_true, ite_false, Queues.RxCredits.modifyPeer_source, bind_assoc] using run

theorem initiationAfterSetter_remotes (msg : List UInt8) (pid : PeerId) (entry : RemoteMap) :
    Ensures (initiationAfterSetter msg pid) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  unfold initiationAfterSetter
  exact ensures_bind _ _ (retained_of_remote_frame _ (sendHandshakeResponse_remotes pid) entry)
    (fun _ => receiveCheckedFinish_remotes msg pid entry)

theorem responseAfterSetter_remotes (msg : List UInt8) (pid : PeerId) (entry : RemoteMap) :
    Ensures (responseAfterSetter msg pid) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  let P := fun g => RemoteRetained entry (destinationAt g)
  unfold responseAfterSetter
  refine ensures_bind _ _ (retained_of_remote_frame _ (beginSession_endpoints pid) entry) ?_
  intro begun
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .hsRespSessionBegun begun) P)) ?_
  intro active
  cases active with
  | false => exact receiveCheckedFinish_remotes msg pid entry
  | true =>
    exact ensures_bind _ _ (retained_of_remote_frame _ (derived_remotes pid) entry)
      (fun _ => ensures_bind _ _ (retained_of_remote_frame _ (handshakeComplete_remotes pid _) entry)
        (fun _ => ensures_bind _ _ (sendKeepalive_remotes pid entry)
          (fun _ => receiveCheckedFinish_remotes msg pid entry)))

theorem remotes_frame_of_erasure {α β : Type} (observed : WG.M α) (action : WG.M β)
    (project : α → β) (erase : (do let result ← observed; pure (project result)) = action)
    (frame : SameView destinationAt action) : SameView destinationAt observed := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have erased : ((action.run g).run ambient) = .ok ((project result,final),after) := by
    rw [← erase]
    change (((observed.run g).run ambient) >>= fun ((value,current),inputs) =>
      .ok ((project value,current),inputs)) = _
    rw [run]
    rfl
  exact (ProjectedAction.iff_run_ambient _ _ _).mp frame g ambient (project result) final after erased

theorem responseWithLookup_remotes (msg : List UInt8) :
    SameView destinationAt (responseWithLookup msg) :=
  remotes_frame_of_erasure _ _ _ (responseWithLookup_erase msg)
    (endpoint_frame_remotes _ (consumeResponse_endpoints msg))

theorem initiationConsume_remotes (msg : List UInt8) :
    SameView destinationAt (initiationConsume msg) :=
  remotes_frame_of_erasure _ _ _ (initiationConsume_erase msg)
    (endpoint_frame_remotes _ (consumeInitiation_endpoints msg))

theorem responsePacketPrefix_remotes (msg : List UInt8) (src : SkbSource) (loaded : Bool) :
    SameView destinationAt (responsePacketPrefix msg src loaded) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  let P := fun g => destinationAt g = entry
  have pureF {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run; cases run; exact pre
  have branchF (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have stopF {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run; cases run
  have readF : Ensures Campaign2.read P (fun _ => P) := by
    intro g a result final after pre run; cases run; exact pre
  have cookieF := (ensures_iff _ _ _).mpr
    (sameCookie_remotes _ (cookieValidatePacket_sameCookie msg src loaded) entry)
  have replyF := (ensures_iff _ _ _).mpr (sendHandshakeCookie_remotes msg src entry)
  have consumeF := (ensures_iff _ _ _).mpr (responseWithLookup_remotes msg entry)
  unfold responsePacketPrefix
  simp only [WG.andM,WG.orM,bind_assoc,pure_bind]
  repeat' first
    | exact pureF _
    | exact branchF _ _
    | exact stopF _
    | exact readF
    | exact cookieF
    | exact replyF
    | exact consumeF
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | split

theorem initiationPacketPrefix_remotes (msg : List UInt8) (src : SkbSource) (loaded : Bool) :
    SameView destinationAt (initiationPacketPrefix msg src loaded) := by
  intro entry
  apply (ensures_iff _ _ _).mp
  let P := fun g => destinationAt g = entry
  have pureF {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run; cases run; exact pre
  have branchF (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have stopF {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run; cases run
  have readF : Ensures Campaign2.read P (fun _ => P) := by
    intro g a result final after pre run; cases run; exact pre
  have cookieF := (ensures_iff _ _ _).mpr
    (sameCookie_remotes _ (cookieValidatePacket_sameCookie msg src loaded) entry)
  have replyF := (ensures_iff _ _ _).mpr (sendHandshakeCookie_remotes msg src entry)
  have consumeF := (ensures_iff _ _ _).mpr (initiationConsume_remotes msg entry)
  unfold initiationPacketPrefix
  simp only [WG.andM,WG.orM,bind_assoc,pure_bind]
  repeat' first
    | exact pureF _
    | exact branchF _ _
    | exact stopF _
    | exact readF
    | exact cookieF
    | exact replyF
    | exact consumeF
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | split

theorem responseLoad_remotes : SameView destinationAt responseLoad := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have same := responseLoad_device g.dev g ambient result final after rfl run
  funext pid
  simp only [destinationAt,peerAt,same]

theorem responseCallPrefix_remotes (msg : List UInt8) (src : SkbSource) :
    SameView destinationAt (responseCallPrefix msg src) :=
  (show SameView destinationAt (branch .hsCookie false : WG.M Bool) from
    fun entry => hoare_liftAmbient (AmbientM.branch .hsCookie false)
      (fun g => destinationAt g = entry)).bind (fun _ =>
    responseLoad_remotes.bind (fun loaded => responsePacketPrefix_remotes msg src loaded))

theorem initiationCallPrefix_remotes (msg : List UInt8) (src : SkbSource) :
    SameView destinationAt (initiationCallPrefix msg src) :=
  (show SameView destinationAt (branch .hsCookie false : WG.M Bool) from
    fun entry => hoare_liftAmbient (AmbientM.branch .hsCookie false)
      (fun g => destinationAt g = entry)).bind (fun _ =>
    responseLoad_remotes.bind (fun loaded => initiationPacketPrefix_remotes msg src loaded))

theorem responseCallSuffix_remotes (msg : List UInt8) (src : SkbSource)
    (candidate : Option ResponseCallCut) (entry : RemoteMap) :
    Ensures (responseCallSuffix msg src candidate) (fun g => destinationAt g = entry)
      (fun _ g => match candidate with
        | none => destinationAt g = entry
        | some cut => RemoteRetained (updateRemote entry cut.consumed.input.pid
            (destination (sourceEndpoint src))) (destinationAt g)) := by
  cases candidate with
  | none => intro g a result final after pre run; cases run; exact pre
  | some cut =>
    refine ensures_bind _ _ (setPeerEndpointFromSkb_remotes cut.consumed.input.pid src entry) ?_
    intro _ g a result final after pre run
    exact responseAfterSetter_remotes msg cut.consumed.input.pid _ g a result final after
      (.of_eq pre) run

theorem initiationCallSuffix_remotes (msg : List UInt8) (src : SkbSource)
    (candidate : Option InitiationCallCut) (entry : RemoteMap) :
    Ensures (initiationCallSuffix msg src candidate) (fun g => destinationAt g = entry)
      (fun _ g => match candidate with
        | none => destinationAt g = entry
        | some cut => RemoteRetained (updateRemote entry cut.consumed.pid
            (destination (sourceEndpoint src))) (destinationAt g)) := by
  cases candidate with
  | none => intro g a result final after pre run; cases run; exact pre
  | some cut =>
    refine ensures_bind _ _ (setPeerEndpointFromSkb_remotes cut.consumed.pid src entry) ?_
    intro _ g a result final after pre run
    exact initiationAfterSetter_remotes msg cut.consumed.pid _ g a result final after
      (.of_eq pre) run


end Leanux.Proofs.WG.Roaming
