import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSessionCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolPointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointPeerComposition

/-! Fixed flushed protocol-send source. Creation, MAC and socket atoms retain
their native boundary; their finer interiors remain a separate obligation.
The sender's actual binds, timer helpers and counted repayment are explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open HandshakeSecurity.SendExchange
abbrev History := List Event

inductive Native where
  | work (token : WorkService.Points.Native)
  | before (pid : PeerId)
  | create (pid : PeerId)
  | mac (pid : PeerId) (bytes : Key)
  | jitter (site : HiddenSite)
  | socket (pid : PeerId) (bytes : Key)
  | scope (event : CausalScope.Event Cause)
  | created (pid : PeerId) (receipt : WGRunWitness (Option Key))

def Native.Result : Native → Type
  | .work token=>token.Result
  | .create _=>Option Key
  | .mac _ _=>Key
  | .jitter _=>Nat
  | _=>Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .work token=>token.action
  | .before pid=>Consume.Leaf.wg (SendWorkerFrames.beforeWorker pid)
  | .create pid=>Consume.Leaf.wg (createInitiation pid)
  | .mac pid bytes=>Consume.Leaf.wg (addMacToPacket pid bytes)
  | .jitter site=>Consume.Leaf.wg (jitterBelowRekeyTimeout site)
  | .socket pid bytes=>liftWGObserver (ProtocolSocket.observed Event.protocolSocket scope? pid bytes)
  | .scope event=>emitPrefix (.scope event)
  | .created pid receipt=>emitPrefix (.exchange (.createInitiation pid receipt))

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | leaf (source : Consume.Leaf.Shape action) : Shape action
  | release (peer : Option PeerId) : Shape (liftWGObserver (peerRelease peer))
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def stateBindShape (body : WGPrefix Event α) (next : α → WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : WGPrefix Event α} (left : test → Shape (liftWGObserver yes))
    (right : ¬test → Shape (liftWGObserver no)) : Shape (liftWGObserver (if test then yes else no)) := by
  split
  · exact left ‹_›
  · exact right ‹_›

noncomputable def updateThenShape (pid : PeerId) (f : Peer → Peer)
    (next : Unit → WGPrefix Event α)
    (fields : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
    (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (liftWGPrefix (getPeer pid) >>= fun p=>liftWGPrefix (setPeer pid (f p)) >>= next)) := by
  rw [←bind_assoc,←Queued.lift_bind,liftWGObserver_bind]
  exact .bind (.leaf (.native (.base (.update pid f fields)))) tail


noncomputable def createShape (pid : PeerId) : Shape
    (liftWGObserver (receiptWGObserved (liftWGPrefix (createInitiation pid))
      (Event.exchange ∘ HandshakeSecurity.Exchange.Event.createInitiation pid))) := by
  rw [Consume.Points.wg_receipt_factor]
  exact .bind (.leaf (.native (.base (.basic .world)))) fun before=>
    .bind (.native (.create pid)) fun value=>
      .bind (.leaf (.native (.base (.basic .world)))) fun after=>
        .bind (.native (.created pid ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩))
          (fun _=>.pure value)

elab "protocol_source_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a protocol source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not an observed WG source"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "protocol_update_head" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a protocol source"
  let action := target.getAppArgs.back!.consumeMData
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not an observed source"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not a source bind"
  let args := body.getAppArgs
  let head := args[args.size-2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix && head.getAppArgs.back!.isAppOf ``getPeer do
    Lean.throwError "not a native peer read"
  let .lam _ _ tail _ := args.back!.consumeMData | Lean.throwError "not a source continuation"
  unless tail.isAppOf ``Bind.bind do Lean.throwError "not a write continuation"
  let args := tail.getAppArgs
  let head := args[args.size-2]!.consumeMData
  unless head.isAppOf ``liftWGPrefix && head.getAppArgs.back!.isAppOf ``setPeer do
    Lean.throwError "not a native peer write"

elab "protocol_wg_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a protocol source"
  let action := target.getAppArgs.back!.consumeMData
  unless action.isAppOf ``liftWGObserver do Lean.throwError "not an observed source"
  let body := action.getAppArgs.back!.consumeMData
  unless body.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
  let .const actual _ := body.getAppArgs.back!.consumeMData.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

noncomputable def initiatedShape (pid : PeerId) : Shape
    (liftWGObserver (TimerEffects.initiatedWith effects pid)) := by
  unfold TimerEffects.initiatedWith
  simp only [Consume.Leaf.effect_step]
  repeat' first
    | (protocol_wg_head callerJiffies; exact .leaf (Consume.Leaf.callerShape _))
    | (protocol_wg_head modPeerTimerGuard; exact .leaf (Consume.Leaf.guardShape _))
    | (protocol_wg_head jitterBelowRekeyTimeout; exact .native (.jitter _))
    | (protocol_source_head TimerEffects.Ops.arm; exact .leaf (Consume.Leaf.armShape _ _ _ _))
    | (protocol_source_head Bind.bind; apply stateBindShape)
    | (protocol_source_head ite; apply conditionalShape)
    | (protocol_source_head Pure.pure; exact .pure _)
    | intro value
    | (dsimp +failIfUnchanged only)

noncomputable def sendShape (pid : PeerId) : Shape (liftWGObserver (sendWith CompleteSend.ops pid)) := by
  unfold sendWith CompleteSend.ops
  simp only [SendEffects.withEffects,HandshakeSecurity.ExchangeJoint.sendOps,
    HandshakeSecurity.StagedDisposal.Decoration.send,ProtocolSender.sendOps,SendEffects.native]
  repeat' first
    | (protocol_update_head; apply updateThenShape; first | exact fun _=>⟨rfl,rfl,rfl⟩ | intro value)
    | (protocol_source_head receiptWGObserved; exact createShape _)
    | (protocol_source_head TimerEffects.traversalWith; exact .leaf (Consume.Leaf.traversalShape _))
    | (protocol_source_head TimerEffects.initiatedWith; exact initiatedShape _)
    | (protocol_source_head ProtocolSocket.observed; exact .native (.socket _ _))
    | (protocol_wg_head hiddenClock64; exact .leaf (.native (.base (.ambient (AmbientM.hiddenClock64 _)))))
    | (protocol_wg_head timersAnyAuthenticatedPacketSent; exact .leaf (by
        unfold timersAnyAuthenticatedPacketSent
        repeat' first
          | (consume_leaf_wg_head delTimer; exact Consume.Leaf.deleteShape _ _)
          | consume_leaf_shape))
    | (protocol_wg_head addMacToPacket; exact .native (.mac _ _))
    | (protocol_wg_head branchExpired; exact .native (.work (.expired _ _ _ _)))
    | (protocol_source_head liftWGPrefix; exact .leaf (by repeat' consume_leaf_shape))
    | (protocol_source_head Bind.bind; apply stateBindShape)
    | (protocol_source_head Pure.pure; exact .pure _)
    | (protocol_source_head ite; apply conditionalShape)
    | intro value
    | split
    | (dsimp +failIfUnchanged only)

noncomputable def workerShape (pid : PeerId) : Shape (liftWGObserver (workerWith CompleteSend.ops pid)) :=
  stateBindShape _ _ (sendShape pid) (fun _=>.release (some pid))

noncomputable def bodyShape (pid : PeerId) : Shape
    (liftWGObserver (flushedWith liftWGPrefix (workerWith CompleteSend.ops) pid)) := by
  unfold flushedWith
  refine stateBindShape _ _ (.native (.work (.change _ ?_))) ?_
  · intro w
    unfold StagedEntry.view Packets.epoch TransmitSecurity.Staged.stagedAt PacketMaterial.view
      Packets.snapshot Packets.deviceStore Queues.TxDisposition.txPackets RetirementSecurity.txQueueContents Queues.RxCredits.handoffTxView
    cases w.dev <;> rfl
  · intro ignored
    rw [SendWorkerFrames.after_factor]
    exact stateBindShape _ _ (.native (.before pid)) fun _=>
      stateBindShape _ _ (workerShape pid) fun _=>
        stateBindShape _ _ (.leaf (.native (.base (.ambient (AmbientM.hidden (.sectionStop .sendWorker))))))
          (fun _=>.pure ())

theorem flushed_source (pid : PeerId) : liftWGObserver (CausalJournal.flushedSend pid) = (do
    let w←liftPrefix (get : Leanux.M World)
    let h←Consume.Leaf.historyRead
    emitPrefix (.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w.wg)⟩))
    let value←liftWGObserver (flushedWith liftWGPrefix (workerWith CompleteSend.ops) pid)
    emitPrefix (.scope (.exited h.length))
    pure value) := by
  funext w h
  change runPrefix (liftWGObserver (CausalJournal.flushedSend pid)) w h = _
  rw [liftWGObserver_run]
  change _ = runPrefix (do
    let value←liftWGObserver (flushedWith liftWGPrefix (workerWith CompleteSend.ops) pid)
    emitPrefix (.scope (.exited h.length))
    pure value) w (h ++ [.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w.wg)⟩)])
  rw [CausalJournal.flushedSend,SendEffects.flushed,CausalSources.flushedWith,CausalSources.workScope_run]
  rw [runPrefix_bind,liftWGObserver_run]
  rw [←CompleteSend.ops]
  cases performed : runWGPrefix (flushedWith liftWGPrefix (workerWith CompleteSend.ops) pid) w.wg w.ambient
      (h ++ [.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w.wg)⟩)]) with
  | mk result last =>
    cases result with
    | error reason=>rfl
    | ok pair=>rcases pair with ⟨⟨value,v⟩,a⟩;rfl

noncomputable def source (pid : PeerId) : Shape (liftWGObserver (CausalJournal.flushedSend pid)) := by
  rw [flushed_source]
  exact .bind (.leaf (.native (.base (.basic .world)))) fun w=>
    .bind (.leaf (.native .history)) fun h=>
      .bind (.native (.scope (.entered ⟨h.length,.sendWork pid (CausalSources.sendEntry pid w.wg)⟩))) fun _=>
        .bind (bodyShape pid) fun value=>
          .bind (.native (.scope (.exited h.length))) (fun _=>.pure value)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
