import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointCounter

/-! Fixed receive-side maintenance, packet validation and routed release
source witnesses. No callback is erased when constructing a continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open RetirementSecurity

elab "consume_observer_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different observer head"

theorem observer_if (test : Prop) [Decidable test] (yes no : WGPrefix Event α) :
    liftWGObserver (if test then yes else no) =
      (if test then liftWGObserver yes else liftWGObserver no) := by split <;> rfl

noncomputable def statsShape (pid : PeerId) (len : Nat) : Shape (wg (updateRxStats pid len)) := by
  unfold updateRxStats
  rw [wg_bind]
  exact .bind (.native (.statsDevice len)) (fun _ => .native (.statsPeer pid len))

macro "consume_receive_shape" : tactic => `(tactic| first
  | (consume_wg_tail_head setPeer; exact .native (.freshWrite _))
  | (consume_wg_head updateRxStats; exact statsShape _ _)
  | (consume_wg_head dishonest; exact .native (.dishonest _))
  | (consume_wg_head inetEcnDecapsulate; exact .native (.ecn _ _ _))
  | (consume_wg_head setPeerEndpoint; exact .child (.endpoint _ _))
  | (consume_wg_head timersHandshakeComplete; exact .child (.handshakeTimer _))
  | (consume_wg_head timersAnyAuthenticatedPacketReceived; exact .child (.authenticated _))
  | (consume_wg_head lookupSrc; exact .child (.lookup _ _))
  | (consume_observer_head Driver.Hooks.confirmation; exact confirmationShape _ _)
  | (consume_observer_head Driver.Hooks.peerRelease; exact .child (.release _))
  | (consume_observer_head peerRelease; exact .child (.release _))
  | (consume_observer_head Driver.stagingObserved; exact .child (.staging _))
  | (consume_observer_head TimerEffects.traversalWith; exact .child (.traversal _))
  | (consume_observer_head TimerEffects.dataReceivedWith; exact .child (.received _))
  | (consume_observer_head HandshakeSecurity.StagedDisposal.Effects.queuedWith; exact .child (.queued _))
  | (consume_observer_head Bind.bind; rw [liftWGObserver_bind]; apply Shape.bind)
  | (consume_observer_head Pure.pure; exact .pure _)
  | (consume_observer_head ite; rw [observer_if]; apply conditionalShape)
  | consume_native_shape)

noncomputable def freshShape (pid : PeerId) : Shape
    (liftWGObserver (HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith effects peerRelease pid)) := by
  apply Shape.marked (.fresh pid)
  unfold HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith
  simp only [effects,CausalEffects.ops,TimerEffects.observed,WG.andM]
  repeat' consume_receive_shape

noncomputable def prepareShape (pid : PeerId) (packet : RxPacket) : Shape
    (liftWGObserver (HandshakeSecurity.StagedDisposal.PacketSource.prepareWith effects peerRelease pid packet)) := by
  apply Shape.marked (.prepare pid packet)
  unfold HandshakeSecurity.StagedDisposal.PacketSource.prepareWith
  simp only [effects,CausalEffects.ops,TimerEffects.observed,WG.andM,WG.orM]
  repeat' first
    | (consume_observer_head HandshakeSecurity.StagedDisposal.PacketSource.freshReceiveWith; exact freshShape _)
    | consume_receive_shape

noncomputable def finishShape (pid : PeerId) (ready : Packets.RxReady) : Shape
    (liftWGObserver (NestedPeerRelease.rxFinishWith (Driver.nestedOps hooks) pid ready)) := by
  apply Shape.marked (.finish pid ready)
  unfold NestedPeerRelease.rxFinishWith NestedPeerRelease.rxAfterLookupWith
  simp only [Driver.nestedOps]
  repeat' consume_receive_shape

noncomputable def consumeShape (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) : Shape
    (liftWGObserver (Driver.consumeObserved hooks pid packet endpoint)) := by
  apply Shape.marked (.consume pid packet endpoint)
  unfold Driver.consumeObserved Driver.receiveTailObserved
  simp only [Driver.effectOps]
  repeat' first
    | (consume_observer_head HandshakeSecurity.StagedDisposal.PacketSource.prepareWith; exact prepareShape _ _)
    | (consume_observer_head NestedPeerRelease.rxFinishWith; exact finishShape _ _)
    | consume_receive_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
