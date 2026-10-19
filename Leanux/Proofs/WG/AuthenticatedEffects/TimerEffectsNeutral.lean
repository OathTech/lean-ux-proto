import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsFrames

/-! Exact neutral specialization: callback factoring with native lifts is the
original native action lifted once, including its Stop and unchanged journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem eq_native_lift {g : WGPrefix E α} {native : WG.M α}
    (erases : ErasesStatePrefix g native) (quiet : StateHistoryFrame some g) :
    g = liftWGPrefix native := by
  funext w a h
  apply Prod.ext
  · exact erases w a h
  · change (runWGPrefix g w a h).2 = h
    simpa only [runWGPrefix,runStatePrefix,List.filterMap_some] using quiet w a h

theorem discard_lifted (action : WG.M α) :
    discard (liftWGPrefix action : WGPrefix E α) = liftWGPrefix (discard action) := by
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply eq_native_lift
  · exact erasesStatePrefix_bind (erasesStatePrefix_lift action) (fun _ => erasesStatePrefix_pure _)
  · apply StateHistoryFrame.bind
    · intro w a h; rfl
    · intro x w a h; rfl

theorem lifted_erases : Ops.Erases (lifted : Ops (WGPrefix E)) where
  step := erasesStatePrefix_lift
  arm := fun _ _ _ _ => erasesStatePrefix_lift _
  append := fun _ => erasesStatePrefix_lift _

theorem lifted_frames (ρ : E → Option F) : Ops.Frames ρ lifted where
  step := by intro α action w a h; rfl
  arm := by intro pid timer delay caller w a h; rfl
  append := by intro pid w a h; rfl

theorem modify_lifted (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    modifyWith (lifted : Ops (WGPrefix E)) site pid timer delay = liftWGPrefix (modPeerTimer site pid timer delay) :=
  eq_native_lift (modify_erases lifted_erases site pid timer delay) (modify_frame some (lifted_frames some) site pid timer delay)

theorem derived_lifted (pid : PeerId) :
    derivedWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (timersSessionDerived pid) :=
  eq_native_lift (derived_erases lifted_erases pid) (derived_frame some (lifted_frames some) pid)

theorem traversal_lifted (pid : PeerId) :
    traversalWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (timersTraversal pid) :=
  eq_native_lift (traversal_erases lifted_erases pid) (traversal_frame some (lifted_frames some) pid)

theorem dataSent_lifted (pid : PeerId) :
    dataSentWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (timersDataSent pid) :=
  eq_native_lift (dataSent_erases lifted_erases pid) (dataSent_frame some (lifted_frames some) pid)

theorem dataReceived_lifted (pid : PeerId) :
    dataReceivedWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (timersDataReceived pid) :=
  eq_native_lift (dataReceived_erases lifted_erases pid) (dataReceived_frame some (lifted_frames some) pid)

theorem initiated_lifted (pid : PeerId) :
    initiatedWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (timersHandshakeInitiated pid) :=
  eq_native_lift (initiated_erases lifted_erases pid) (initiated_frame some (lifted_frames some) pid)

theorem queued_lifted (pid : PeerId) (retry : Bool) :
    queuedWith (lifted : Ops (WGPrefix E)) pid retry = liftWGPrefix (sendQueuedHandshakeInitiation pid retry) :=
  eq_native_lift (queued_erases lifted_erases pid retry) (queued_frame some (lifted_frames some) pid retry)

theorem retransmit_lifted (pid : PeerId) :
    retransmitWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (expiredRetransmitHandshake pid) :=
  eq_native_lift (retransmit_erases lifted_erases pid) (retransmit_frame some (lifted_frames some) pid)

theorem expiredNew_lifted (pid : PeerId) :
    expiredNewWith (lifted : Ops (WGPrefix E)) pid = liftWGPrefix (expiredNewHandshake pid) :=
  eq_native_lift (expiredNew_erases lifted_erases pid) (expiredNew_frame some (lifted_frames some) pid)

theorem expiredKeepalive_lifted (keepalive : PeerId → WGPrefix E Unit) (pid : PeerId) :
    expiredKeepaliveWith lifted keepalive pid = (do
      keepalive pid
      if ← liftWGPrefix (branch .keepaliveNeedAnother (← liftWGPrefix (getPeer pid)).timerNeedAnotherKeepalive) then
        liftWGPrefix (setPeer pid { (← liftWGPrefix (getPeer pid)) with timerNeedAnotherKeepalive := false })
        liftWGPrefix (discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)) := by
  unfold expiredKeepaliveWith
  rw [modify_lifted,discard_lifted]
  rfl

theorem persistent_lifted (keepalive : PeerId → WGPrefix E Unit) (pid : PeerId) :
    persistentWith lifted keepalive pid = (do
      if ← liftWGPrefix (branch .persistentKeepaliveInterval ((← liftWGPrefix (getPeer pid)).persistentKeepaliveInterval != 0)) then
        keepalive pid) := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
