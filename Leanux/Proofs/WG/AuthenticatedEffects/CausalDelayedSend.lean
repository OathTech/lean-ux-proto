import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.SendCallerContracts

/-! Live occurrence transport through the exact send worker and its dequeue.
Removing an absent item preserves the carrier but does not authorize the call;
selected-cause claims still require membership from the native caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open HandshakeSecurity TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem create (pid : PeerId) : StateSafe (liftWGPrefix (createInitiation pid)) := by
  apply state_framed
  · intro initial
    unfold createInitiation
    index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
    simp only [branch,hidden,invariant]
    repeat' timer_handshake_step initial
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    have frame := (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.createInitiation_frame) pid w)
      w a value v b (Queues.RxCredits.DurableHolders.Frame.refl w) run
    exact congrArg (fun q => q.getD []) frame.send

private theorem send_body (pid : PeerId) : StateSafe
    (SendExchange.workerWith (SendEffects.withEffects
      (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects) pid) := by
  unfold SendExchange.workerWith SendExchange.sendWith
  simp only [SendEffects.withEffects,ExchangeJoint.sendOps,StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (causal_delayed_head receiptWGObserved; apply state_receipt)
    | (causal_delayed_native_head createInitiation; exact create _)
    | (causal_delayed_head TimerEffects.traversalWith; exact traversal _)
    | (causal_delayed_head TimerEffects.initiatedWith; exact initiated _)
    | causal_delayed_handshake_native
    | causal_delayed_effect_step

theorem dequeue (pid : PeerId) : StateSafe
    (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
  intro h w a value v b hi run
  obtain ⟨timers,tickets,work⟩ := hi
  have same : QueuedOccurrences.queue v = (QueuedOccurrences.queue w).erase pid :=
    SendWorkCauses.native_erase pid w v a b (by cases value; exact run)
  have kept := timers.frame ((ProjectedAction.iff_run_ambient _ _ _).mp
    (DelayedEffects.queue_edit_timers (fun queue => queue.erase pid)) w a value v b run)
  refine ⟨kept,?_⟩
  by_cases present : pid ∈ QueuedOccurrences.queue w
  · obtain ⟨ticket,rest,selected⟩ := QueuedOccurrences.select_exists tickets pid (work.1 ▸ present)
    exact ⟨rest,(work.dequeue selected same).2⟩
  · exact ⟨tickets,work.frame (by simpa only [List.erase_of_not_mem present] using same)⟩

private def takenFrontWith [Monad m] (step : {α : Type} → WG.M α → m α) (pid : PeerId) : m Unit := do
  let p ← step (getPeer pid)
  if !p.handshakePending then step (invariant "queued work without a pending flag")
  let d ← step getDev
  step (setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid})
  discard <| step (hidden (.sectionStart .sendWorker))

private theorem taken_front_equal (pid : PeerId) :
    (takenFrontWith liftWGPrefix pid : WGPrefix Event Unit) = liftWGPrefix (takenFrontWith (fun {_} a => a) pid) := by
  apply TimerEffects.eq_native_lift
  · unfold takenFrontWith
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
      | split
      | (session_origin_intro_forall; try dsimp only)
  · unfold takenFrontWith
    simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' first
      | (change StateHistoryFrame some (liftWGPrefix _); exact fun _ _ _ => rfl)
      | (change StateHistoryFrame some (pure _); exact fun _ _ _ => rfl)
      | with_reducible apply StateHistoryFrame.bind
      | split
      | (session_origin_intro_forall; try dsimp only)

private theorem taken_front (pid : PeerId) : StateSafe (takenFrontWith liftWGPrefix pid) := by
  rw [taken_front_equal]
  apply state_framed
  · intro initial
    unfold takenFrontWith
    simp only [hidden,invariant,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' causal_delayed_timer_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => Queues.WorkQueueFrames.view w = initial) _
    unfold takenFrontWith
    simp only [hidden,invariant,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
    repeat' causal_delayed_queue_step initial

private theorem after_take (pid : PeerId) : StateSafe
    (SendExchange.afterTakeWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects)) pid) := by
  have factor : SendExchange.afterTakeWith liftWGPrefix (SendExchange.workerWith
      (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects)) pid =
      (do takenFrontWith liftWGPrefix pid
          SendExchange.workerWith (SendEffects.withEffects (ExchangeJoint.sendOps Event.exchange (StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal? (ProtocolSender.sendOps Event.protocolSocket scope?))) effects) pid
          discard <| liftWGPrefix (hidden (.sectionStop .sendWorker))) := by
    simp only [SendExchange.afterTakeWith,takenFrontWith,Functor.discard,map_const,
      Function.comp_apply,Function.const,map_eq_pure_bind,bind_assoc]
    congr 1
    funext p
    split <;> simp only [bind_assoc,pure_bind]
  rw [factor]
  apply state_bind (taken_front pid)
  intro _
  apply state_bind (send_body pid)
  intro _
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply state_bind
  · unfold hidden
    causal_delayed_native
  · intro _
    exact state_pure _

theorem flushed_send (pid : PeerId) : StateSafe (flushedSend pid) := by
  intro w a h hi
  apply state_scope (.sendWork pid (CausalSources.sendEntry pid w)) _ ?_ w a h hi
  exact state_bind (dequeue pid) (fun _ => after_take pid)

theorem send_worker : ProductSafe (TransmitSecurity.Driver.sendWorkerObserved hooks) :=
  SendCallers.one_preserves Inv (fun _ => True) (fun _ _ _ => True.intro) flushedSend
    (fun pid => (flushed_send pid).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
