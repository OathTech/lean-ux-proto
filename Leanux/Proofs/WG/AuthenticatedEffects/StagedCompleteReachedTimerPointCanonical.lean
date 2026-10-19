import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointResidual

/-! The canonical callback witnesses use the actual saved peer branches.
Selection and finish retain their real event order and history clock. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

noncomputable def stateBindShape (body : WGPrefix Event α) (next : α → WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀ value, Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def updateThenShape (pid : PeerId) (f : Peer → Peer)
    (next : Unit → WGPrefix Event α)
    (fields : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ value, Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next)) := by
  rw [← bind_assoc,← Queued.lift_bind,liftWGObserver_bind]
  exact .bind (.work (.leaf (.native (.base (.update pid f fields))))) tail

noncomputable def clearEndpoint (pid : PeerId) : Consume.Leaf.Shape (Consume.Leaf.wg (clearPeerEndpointSrc pid)) := by
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | consume_leaf_update
    | consume_leaf_update_then
    | (consume_leaf_wg_head dstCacheReset; exact Consume.Leaf.cacheShape _)
    | consume_leaf_shape

noncomputable def newShape (pid : PeerId) : Shape (liftWGObserver (HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith effects peerRelease pid)) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith
  exact stateBindShape _ _ (.work (.leaf (clearEndpoint pid)))
    (fun _ => .work (WorkService.Points.queuedShape pid false))

noncomputable def retransmitShape (pid : PeerId) :
    Shape (liftWGObserver (HandshakeSecurity.StagedDisposal.Effects.retransmitWith effects peerRelease stagedPurge pid)) := by
  unfold HandshakeSecurity.StagedDisposal.Effects.retransmitWith
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.peer pid))))))
  intro peer
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.ambient (AmbientM.branchCmp
    .retransmitGiveUp (peer.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) peer.timerHandshakeAttempts MAX_TIMER_HANDSHAKES))))))
  intro exhausted
  split
  · apply stateBindShape _ _ (.work (.leaf (Consume.Leaf.deleteShape pid .sendKeepalive)))
    intro ignored
    apply stateBindShape _ _ (.child (.purge pid))
    intro ignored
    apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.peer pid))))))
    intro peer
    apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.branch
      .retransmitZeroKeyNotPending !(peer.timerPending .zeroKeyMaterial)))))))
    intro pending
    split
    · exact .work (.leaf (Consume.Leaf.discardShape _ (Consume.Leaf.modifyShape
        .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)))
    · exact .pure ()
  · apply updateThenShape pid (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    exact stateBindShape _ _ (.work (.leaf (clearEndpoint pid)))
      (fun _ => .work (WorkService.Points.queuedShape pid true))

noncomputable def keepaliveShape (pid : PeerId) :
    Shape (liftWGObserver (TimerEffects.expiredKeepaliveWith effects (Driver.keepaliveObserved hooks) pid)) := by
  unfold TimerEffects.expiredKeepaliveWith
  apply stateBindShape _ _ (.child (.keepalive pid))
  intro ignored
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.peer pid))))))
  intro peer
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.branch .keepaliveNeedAnother peer.timerNeedAnotherKeepalive))))))
  intro needed
  split
  · apply updateThenShape pid (fun p => {p with timerNeedAnotherKeepalive := false}) _ (fun _ => ⟨rfl,rfl,rfl⟩)
    intro ignored
    exact .work (.leaf (Consume.Leaf.discardShape _ (Consume.Leaf.modifyShape
      .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)))
  · exact .pure ()

noncomputable def persistentShape (pid : PeerId) :
    Shape (liftWGObserver (TimerEffects.persistentWith effects (Driver.keepaliveObserved hooks) pid)) := by
  unfold TimerEffects.persistentWith
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.peer pid))))))
  intro peer
  apply stateBindShape _ _ (.work (.leaf (.native (.base (.basic (.branch
    .persistentKeepaliveInterval (peer.persistentKeepaliveInterval != 0)))))))
  intro enabled
  split
  · exact .child (.keepalive pid)
  · exact .pure ()

noncomputable def callbackShape (pid : PeerId) (timer : PeerTimer) :
    Shape (liftWGObserver (Driver.timerObserved hooks pid timer)) := by
  apply Shape.marked (.callback pid timer)
  cases timer with
  | retransmitHandshake => exact retransmitShape pid
  | sendKeepalive => exact keepaliveShape pid
  | newHandshake => exact newShape pid
  | zeroKeyMaterial => exact .child (.zero pid)
  | persistentKeepalive => exact persistentShape pid

theorem selected_factor (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    hooks.timerSelected device bound pid timer entry = (do
      let w ← (Native.world).action
      (Native.selected ⟨device,bound,pid,timer,entry,w⟩).action
      let h ← (Native.history).action
      (Native.scope (.entered ⟨h.length,.timer bound pid timer entry⟩)).action
      pure h.length) := by
  funext w h
  rfl

noncomputable def selectedShape (device : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Shape (hooks.timerSelected device bound pid timer entry) := by
  apply Shape.marked (.selected device bound pid timer entry)
  rw [selected_factor]
  exact .bind (.native .world) fun w =>
    .bind (.native (.selected ⟨device,bound,pid,timer,entry,w⟩)) fun _ =>
    .bind (.native .history) fun h =>
    .bind (.native (.scope (.entered ⟨h.length,.timer bound pid timer entry⟩))) fun _ => .pure h.length

noncomputable def finishedShape (token : Nat) : Shape (hooks.timerFinished token) :=
  .marked (.finished token) (.native (.scope (.exited token)))
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
