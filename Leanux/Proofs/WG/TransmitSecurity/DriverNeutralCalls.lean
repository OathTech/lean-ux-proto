import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleErasure
import Leanux.Proofs.WG.Queues.RoutingDispatchFrame

/-! Neutral callback factors recover the previous native worker and removal
calls exactly, including history and Stop. They support source refactoring
without weakening any earlier driver specialization. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem state_equal {g : WGPrefix E α} {native : WG.M α}
    (erase : ErasesStatePrefix g native) (frame : StateHistoryFrame some g) :
    g = liftWGPrefix native := by
  funext w a h
  change runWGPrefix g w a h = runWGPrefix (liftWGPrefix native) w a h
  rw [runWGPrefix_lift]
  apply Prod.ext (erase w a h)
  simpa only [List.filterMap_some,runWGPrefix,runStatePrefix,StateT.run] using frame w a h

private theorem product_equal {g : PrefixM E α} {native : Leanux.M α}
    (erase : ErasesPrefix g native) (frame : HistoryFrame some g) :
    g = liftPrefix native := by
  funext w h
  change runPrefix g w h = runPrefix (liftPrefix native) w h
  rw [runPrefix_lift]
  apply Prod.ext (erase w h)
  simpa only [List.filterMap_some] using frame w h

private theorem state_frame (action : WG.M α) : StateHistoryFrame some (liftWGPrefix action : WGPrefix E α) :=
  fun _ _ _ => rfl
private theorem state_pure (value : α) : StateHistoryFrame some (pure value : WGPrefix E α) :=
  fun _ _ _ => rfl
private theorem state_loop (xs : List α) (value : β) (f : α → β → WGPrefix E (ForInStep β))
    (keeps : ∀ x b, StateHistoryFrame some (f x b)) : StateHistoryFrame some (forIn xs value f) := by
  induction xs generalizing value with
  | nil => exact state_pure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateHistoryFrame.bind (keeps x value)
    intro step
    cases step with
    | done b => exact state_pure b
    | yield b => exact ih b

macro "neutral_call_frame" : tactic => `(tactic| first
  | with_reducible exact state_frame _
  | with_reducible exact state_pure _
  | with_reducible apply state_loop
  | with_reducible apply StateHistoryFrame.bind
  | contradiction
  | split
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem sendWorker_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    sendWorkerObserved hooks = liftPrefix Env.runOneSendWorker := by
  unfold sendWorkerObserved
  rw [neutral]
  apply product_equal
  · exact one_erases liftPrefix (fun _ => erasesPrefix_lift _) _
      (fun pid => liftWGObserver_erases (erasesStatePrefix_lift (runFlushedSendWork pid)))
  · unfold oneWith
    exact HistoryFrame.bind (HistoryFrame.lift some _)
      (fun _ => (state_frame _).liftWGObserver)

theorem sendDrain_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) (upTo : Option PeerId) :
    sendDrainObserved hooks upTo = liftWGPrefix (drainHandshakeSendWq upTo) := by
  unfold sendDrainObserved
  rw [neutral]
  apply state_equal
  · exact drain_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _) _ _
      (fun _ => erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_lift _) upTo
  · unfold drainWith
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    repeat' neutral_call_frame

private theorem afterDead_frame (pid : PeerId) :
    StateHistoryFrame some
      (afterDeadWith (fun {_} a => (liftWGPrefix a : WGPrefix E _))
        (fun upTo => liftWGPrefix (drainHandshakeSendWq upTo)) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' neutral_call_frame

theorem remove_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) (peer : Option PeerId) :
    removeObserved hooks peer = liftWGPrefix (peerRemove peer) := by
  unfold removeObserved
  have drains : sendDrainObserved hooks = fun upTo => liftWGPrefix (drainHandshakeSendWq upTo) :=
    funext (sendDrain_lift hooks neutral)
  rw [drains]
  apply state_equal
  · exact remove_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _) _
      (fun _ => erasesStatePrefix_lift _) peer
  · unfold removeWith Configuration.peerRemoveWith
    repeat' first | with_reducible exact afterDead_frame _ | neutral_call_frame
    all_goals simp_all only [Option.some.injEq]
    all_goals first | with_reducible exact afterDead_frame _ | contradiction

theorem removeAll_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    removeAllObserved hooks = liftWGPrefix peerRemoveAll := by
  unfold removeAllObserved
  have drains : sendDrainObserved hooks = fun upTo => liftWGPrefix (drainHandshakeSendWq upTo) :=
    funext (sendDrain_lift hooks neutral)
  rw [drains]
  apply state_equal
  · exact removeAll_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _) _
      (fun _ => erasesStatePrefix_lift _)
  · unfold removeAllWith Configuration.peerRemoveAllWith
    repeat' first | with_reducible exact afterDead_frame _ | neutral_call_frame

private theorem neutral_drains (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    sendDrainObserved hooks = fun upTo => liftWGPrefix (drainHandshakeSendWq upTo) :=
  funext (sendDrain_lift hooks neutral)

theorem down_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    downObserved hooks = liftWGPrefix wgDown := by
  unfold downObserved
  rw [neutral_drains hooks neutral]
  apply state_equal
  · exact down_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _) _
      (fun _ => erasesStatePrefix_lift _)
  · unfold downWith stopWith timersStopWith
    repeat' neutral_call_frame

theorem destruct_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    destructObserved hooks = liftWGPrefix wgDestruct := by
  unfold destructObserved
  rw [neutral_drains hooks neutral]
  apply state_equal
  · exact destruct_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _) _
      (fun _ => erasesStatePrefix_lift _)
  · unfold destructWith Configuration.destructWith removeAllWith Configuration.peerRemoveAllWith
    repeat' first | with_reducible exact afterDead_frame _ | neutral_call_frame

private theorem product_pure_frame (x : α) : HistoryFrame some (pure x : PrefixM E α) :=
  fun _ _ => rfl

macro "neutral_product_frame" : tactic => `(tactic| first
  | with_reducible exact (state_frame _).liftWGObserver
  | with_reducible exact HistoryFrame.lift some _
  | with_reducible exact product_pure_frame _
  | with_reducible apply HistoryFrame.bind
  | contradiction
  | split
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem envDown_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    envDownObserved hooks = liftPrefix Env.wgDown := by
  unfold envDownObserved
  rw [down_lift hooks neutral]
  apply product_equal
  · exact envDown_erases (liftWGObserver_erases (erasesStatePrefix_lift _))
  · unfold envDownWith
    repeat' neutral_product_frame

theorem envDelete_lift (hooks : Hooks E)
    (neutral : hooks.flushedSend = fun pid => liftWGPrefix (runFlushedSendWork pid)) :
    envDeleteObserved hooks = liftPrefix Env.wgDelete := by
  unfold envDeleteObserved
  rw [down_lift hooks neutral,destruct_lift hooks neutral]
  apply product_equal
  · exact envDelete_erases (liftWGObserver_erases (erasesStatePrefix_lift _))
      (liftWGObserver_erases (erasesStatePrefix_lift _))
  · unfold envDeleteWith Configuration.envDeleteWith
    repeat' neutral_product_frame

theorem socketCall_lift (fd : Nat) (body : Leanux.M Int) :
    Configuration.socketCallOnWith (fun {_} a => liftPrefix a) fd (liftPrefix body : PrefixM E Int) =
      liftPrefix (Leanux.socketCallOn fd body) := by
  apply product_equal
  · exact Configuration.socketCallOnWith_erases fd (erasesPrefix_lift body)
  · exact Configuration.socketCallOnWith_frame some fd (HistoryFrame.lift some body)

end Leanux.Proofs.WG.TransmitSecurity.Driver
