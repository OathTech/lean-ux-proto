import Leanux.Proofs.WG.Keypairs.Evolution.Operations
import Leanux.Proofs.WG.Keypairs.Frames.Env
import Leanux.Proofs.WG.Keypairs.Frames.Syscalls
import Leanux.Proofs.WG.Keypairs.Evolution.Runner

/-! Complete syscall composition. Nonreceive calls have a direct frame over
the original executable action; receive observers preserve the lifetime and
acceptance-history invariant through every dispatch and return-to-user branch. -/
namespace Leanux.Proofs.WG.Keypairs.SyscallObservers
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Observers SchedulerObservers OperationObservers
open Leanux.Proofs.Framing Std.Do
open WGFrames WGTransitions WGMore WGConfig EnvFrames SyscallFrames

set_option maxHeartbeats 500000
set_option pp.structureInstances false

open Lean Meta Elab Tactic

/-- Select a subsystem adapter by the lifted action's type before unification
can unfold that action's operational body. The resulting rule is kernel checked. -/
elab "syscall_lift_from " carrier:ident : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOf ``OrdinaryAction || target.isAppOf ``Lifetimes.ProjectedAction do
    throwError "expected an ordinary action"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``liftM || action.isAppOf ``MonadLift.monadLift ||
      action.isAppOf ``MonadLiftT.monadLift do
    throwError "expected a lifted action"
  let source := action.getAppArgs.back!
  let sourceType ← inferType source
  unless sourceType.isApp do throwError "expected an applied source monad"
  let name ← realizeGlobalConstNoOverloadWithInfo carrier
  let expected ← mkAppM name #[sourceType.getAppArgs.back!]
  unless ← withReducible (isDefEq sourceType expected) do
    throwError "different source monad"

macro "syscall_structure_step" : tactic => `(tactic|
  first
    | contradiction
    | keypairs_intro_forall
    | (unfold ProductOrdinaryAction)
    | env_product_join_let
    | env_product_join_use
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head Pure.pure; exact SameView.ordinary (SameView.pure _ _))
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head Functor.discard; refine ordinary_discard ?_)
    | (ordinary_head Functor.map; refine ordinary_map _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_range _ _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_forIn _ _ _ ?_)
    | (ordinary_head modify; refine ordinary_modify _ ?_; intro w; exact Ordinary.refl _)
    | ordinary_head_reduce
    | ordinary_head_match)

macro "syscall_component_step" : tactic => `(tactic|
  first
    | (ordinary_head Leanux.getCurrent; unfold Leanux.getCurrent)
    | (evolves_head Leanux.getCurrent; unfold Leanux.getCurrent)
    | (ordinary_head Leanux.liftFS; apply SameView.ordinary; intro initial;
       exact productFS_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
    | (ordinary_head Leanux.liftSeccomp; apply SameView.ordinary; intro initial;
       exact productSeccomp_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
    | (ordinary_head Leanux.liftTask; apply SameView.ordinary; intro initial;
       exact productTask_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ h => h))
    | (syscall_lift_from FS.M; apply SameView.ordinary; intro initial;
       exact productFS_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
    | (syscall_lift_from TaskM; apply SameView.ordinary; intro initial;
       exact productTask_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ h => h))
    | (syscall_lift_from Seccomp.M; apply SameView.ordinary; intro initial;
       exact productSeccomp_spec _ (fun w => snapshot w.wg = initial) (fun _ _ _ _ h => h))
    | (syscall_lift_from Net.M; apply SameView.ordinary; intro initial;
       exact productRouting_spec _ (fun s => snapshotOfWGStoreView s.2.2.2 = initial))
    | (syscall_lift_from WG.M; apply OrdinaryAction.liftWG))


macro "batch_evolution_step" : tactic => `(tactic|
  first
    | (ordinary_head Env.runOneSendWorker; exact SameView.ordinary runOneSendWorker_sameSnapshot)
    | (ordinary_head Env.peekNextSite; exact SameView.ordinary peekNextSite_sameSnapshot)
    | (ordinary_head Env.xmitPackets; exact SameView.ordinary (xmitPackets_sameSnapshot _ _ _ _))
    | (ordinary_head Env.xmitMulticastLoop; exact SameView.ordinary (xmitMulticastLoop_sameSnapshot _ _))
    | (ordinary_head WG.wgXmit; exact WGDevice.wgXmit_ordinary _ _ _ _)
    | syscall_component_step
    | operation_step)

theorem afterBatchLogged_evolves : Evolves afterBatchLogged :=
  OperationObservers.afterBatchLogged_evolves

theorem batchLogged_evolves (items : List BatchItem) : Evolves (batchLogged items) := by
  unfold batchLogged
  repeat' first
    | (evolves_head afterBatchLogged; exact afterBatchLogged_evolves)
    | (evolves_head pollScheduledInlineLogged; exact pollScheduledInlineLogged_evolves)
    | batch_evolution_step

theorem socketCallOnLogged_evolves (fd : Nat) (body : GhostM Int)
    (hb : Evolves body) : Evolves (socketCallOnLogged fd body) := by
  unfold socketCallOnLogged
  repeat' first
    | syscall_component_step
    | operation_structure_step
    | operation_step

/-- Original dispatch bodies which cannot commit receive validation. A call's
return-to-user work is classified separately below. -/
def NoReceiveDispatch : Syscall → Prop
  | .wgInject .. | .wgFlood .. | .wgBatch .. | .wgObserve => False
  | _ => True

/-- Whole syscalls which cannot commit receive validation, without a condition
on the input World. The updated scheduler also runs in send and timer waits.
The predecessor classification and its counterexample are recorded in the report. -/
def NoReceiveCall : Syscall → Prop
  | .wgInject .. | .wgFlood .. | .wgBatch .. | .wgObserve
  | .wgSet .. | .wgUp | .wgXmit .. | .wgAdvance .. => False
  | _ => True

macro "syscall_ordinary_step" : tactic => `(tactic|
  first
    | syscall_component_step
    | (ordinary_head Leanux.netnsClose; exact SameView.ordinary netnsClose_sameSnapshot)
    | (ordinary_head Leanux.socketCallOn; refine socketCallOn_ordinary _ _ ?_)
    | (ordinary_head Leanux.netlinkRequest; refine netlinkRequest_ordinary _ ?_)
    | (ordinary_head Leanux.rtnetlinkRequest; refine rtnetlinkRequest_ordinary _ ?_)
    | (ordinary_head WG.wgSetDevice; exact wgSetDevice_ordinary _)
    | (ordinary_head WG.wgGetDevice; exact SameView.ordinary (wgGetDevice_sameSnapshot _))
    | (ordinary_head WG.getNlSock; exact SameView.ordinary (getNlSock_sameSnapshot _))
    | (ordinary_head WG.setNlSock; exact SameView.ordinary (setNlSock_sameSnapshot _ _))
    | (ordinary_head WG.netlinkDumpStart; exact SameView.ordinary (netlinkDumpStart_sameSnapshot _ _))
    | (ordinary_head WG.netlinkRecvmsg; exact SameView.ordinary (netlinkRecvmsg_sameSnapshot _))
    | (ordinary_head Leanux.skipCut; unfold Leanux.skipCut)
    | (ordinary_head Leanux.skipCutExactly; unfold Leanux.skipCutExactly)
    | (ordinary_head WG.wgCreate; exact WGDevice.wgCreate_ordinary)
    | (ordinary_head WG.wgXmit; exact WGDevice.wgXmit_ordinary _ _ _ _)
    | (ordinary_head Env.wgUp; exact EnvFrames.wgUp_ordinary)
    | (ordinary_head Env.wgDown; exact EnvFrames.wgDown_ordinary)
    | (ordinary_head Env.wgDelete; exact EnvFrames.wgDelete_ordinary)
    | (ordinary_head Env.setMtu; exact SameView.ordinary (EnvFrames.setMtu_sameSnapshot _))
    | (ordinary_head Env.wgDeladdr; exact SameView.ordinary (wgDeladdr_sameSnapshot _))
    | (ordinary_head Env.wgDelroute; unfold Env.wgDelroute)
    | (ordinary_head Env.wgAddroute; unfold Env.wgAddroute)
    | (ordinary_head Env.wgAddaddr; unfold Env.wgAddaddr)
    | (ordinary_head Leanux.getRouting; unfold Leanux.getRouting)
    | (ordinary_head Leanux.modifyRouting; unfold Leanux.modifyRouting)
    | (ordinary_head Env.advance; exact SameView.ordinary (advance_sameSnapshot _))
    | (ordinary_head Env.routeIntoWg0; exact SameView.ordinary routeIntoWg0_sameSnapshot)
    | (ordinary_head Env.netnsCleanup; exact SameView.ordinary netnsCleanup_sameSnapshot)
    | (ordinary_head Env.fixtureSend; exact SameView.ordinary fixtureSend_sameSnapshot)
    | (ordinary_head Env.xmitPackets; exact SameView.ordinary (xmitPackets_sameSnapshot _ _ _ _))
    | (ordinary_head Env.xmitMulticastLoop; exact SameView.ordinary (xmitMulticastLoop_sameSnapshot _ _))
    | operation_leaf_step
    | env_product_step)

theorem dispatch_noReceive_ordinary (call : Syscall) (hc : NoReceiveDispatch call) :
    ProductOrdinaryAction (Leanux.dispatch call) := by
  cases call <;> simp only [NoReceiveDispatch] at hc
  all_goals simp only [Leanux.dispatch]
  all_goals repeat' first | syscall_structure_step | syscall_ordinary_step

/-- Ordinary dispatch and an ordinary return-to-user branch compose. -/
theorem syscall_ordinary_of_dispatch (call : Syscall) (hc : NoReceiveCall call)
    (hd : ProductOrdinaryAction (Leanux.dispatch call)) : ProductOrdinaryAction (Leanux.syscall call) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  have dispatchSpec := hd.wp P hp
  have fsSpec {α : Type} (a : FS.M α) :=
    productFS_spec a (fun w => P (snapshot w.wg)) (fun _ _ _ _ h => h)
  have seccompSpec {α : Type} (a : Seccomp.M α) :
      Hoare (liftSeccomp a) (fun w => P (snapshot w.wg)) (fun _ w => P (snapshot w.wg)) :=
    productSeccomp_spec a (fun w => P (snapshot w.wg)) (fun _ _ _ _ h => h)
  have taskSpec {α : Type} (a : TaskM α) :=
    productTask_spec a (fun w => P (snapshot w.wg)) (fun _ _ _ h => h)
  have ambientSpec {α : Type} (a : AmbientM α) :=
    productAmbient_spec a (fun w => P (snapshot w.wg)) (fun _ _ h => h)
  have routingSpec {α : Type} (a : Net.M α) :=
    productRouting_spec a (fun s => P (snapshotOfWGStoreView s.2.2.2))
  have queuedSpec :
      ⦃fun w : World => ⌜P (snapshot w.wg)⌝⦄
        (modifyWG fun g => {g with queuedThisCall := []} : Leanux.M Unit)
      ⦃⇓? _ w => ⌜P (snapshot w.wg)⌝⦄ := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hw hr
    cases hr
    exact hw
  have cleanupSpec := netnsCleanup_spec P
  unfold Hoare at fsSpec seccompSpec taskSpec ambientSpec routingSpec
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.syscall,
    Leanux.modifyAmbient, Leanux.getRouting, Leanux.getCurrent, unsupported,
    dispatchSpec, fsSpec, seccompSpec, taskSpec, ambientSpec, routingSpec, queuedSpec, cleanupSpec]
  all_goals try exact (⇓? _ w => ⌜P (snapshot w.wg)⌝)
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [NoReceiveCall]

theorem syscall_noReceive_ordinary (call : Syscall) (hc : NoReceiveCall call) :
    ProductOrdinaryAction (Leanux.syscall call) := by
  have hd : NoReceiveDispatch call := by cases call <;> simp_all [NoReceiveCall, NoReceiveDispatch]
  exact syscall_ordinary_of_dispatch call hc (dispatch_noReceive_ordinary call hd)

theorem dispatchLogged_evolves (call : Syscall) : Evolves (dispatchLogged call) := by
  cases call <;> simp only [dispatchLogged]
  all_goals first
    | (evolves_head socketCallOnLogged
       exact socketCallOnLogged_evolves _ _ (injectLogged_evolves _ _ _ _ _ _))
    | (evolves_head floodLogged; exact floodLogged_evolves _ _ _ _)
    | (evolves_head batchLogged; exact batchLogged_evolves _)
    | (evolves_head liftM; exact evolves_liftM (dispatch_noReceive_ordinary _ trivial))
    | (repeat' first
        | (evolves_head observeLogged; exact observeLogged_evolves)
        | syscall_ordinary_step
        | evolves_step)

theorem syscallLogged_evolves (call : Syscall) : Evolves (syscallLogged call) := by
  unfold syscallLogged
  repeat' first
    | operation_structure_step
    | syscall_structure_step
    | (evolves_head dispatchLogged; exact dispatchLogged_evolves _)
    | operation_step
    | syscall_ordinary_step
    | evolves_step

/-- The concrete syscall contracts discharge the outer runner's last premise. -/
theorem executeTraceLogged_nodup (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (json : Lean.Json) (history : History)
    (hr : (executeTraceLogged trace placeholders).run [] = .ok (json, history)) :
    history.Nodup :=
  RunnerProof.executeTraceLogged_nodup_of_calls syscallLogged_evolves
    trace placeholders json history hr

/-- Every successful original runner execution has its exact observer history,
and that acceptance history has no repeated lifetime/nonce pair. -/
theorem executeTrace_accepted_nodup (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (json : Lean.Json) (hr : Leanux.Runner.executeTrace trace placeholders = .ok json) :
    ∃ history, (executeTraceLogged trace placeholders).run [] = .ok (json, history) ∧
      history.Nodup := by
  obtain ⟨history, hh⟩ := (executeTraceLogged_success_iff trace placeholders json []).mp hr
  exact ⟨history, hh, executeTraceLogged_nodup trace placeholders json history hh⟩

end Leanux.Proofs.WG.Keypairs.SyscallObservers
