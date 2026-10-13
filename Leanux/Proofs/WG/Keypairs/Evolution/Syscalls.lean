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
open KernelFrames WGFrames WGTransitions WGMore WGConfig EnvFrames FSFrames SyscallFrames

set_option maxHeartbeats 500000
set_option pp.structureInstances false

macro "batch_evolution_step" : tactic => `(tactic|
  first
    | (ordinary_head Env.runOneSendWorker; exact runOneSendWorker_sameSnapshot.ordinary)
    | (ordinary_head Env.peekNextSite; exact peekNextSite_sameSnapshot.ordinary)
    | (ordinary_head Env.xmitPackets; exact (xmitPackets_sameSnapshot _ _ _ _).ordinary)
    | (ordinary_head Env.xmitMulticastLoop; exact (xmitMulticastLoop_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.routeLookup; exact (routeLookup_sameSnapshot _ _ _).ordinary)
    | (ordinary_head WG.wgXmit; exact WGDevice.wgXmit_ordinary _ _ _ _)
    | operation_step)

theorem afterBatchLogged_evolves : Evolves afterBatchLogged := by
  unfold afterBatchLogged
  repeat' batch_evolution_step

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
    | (ordinary_head Leanux.fdget; exact (fdget_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.fdput; exact (fdput_sameSnapshot _).ordinary)
    | evolves_step

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
    | (ordinary_head Leanux.sysEventfd2; exact (sysEventfd2_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.sysDup; exact (sysDup_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.ksysDup3; exact (ksysDup3_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Leanux.sysClose; exact (sysClose_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.ksysRead; exact (ksysRead_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.ksysWrite; exact (ksysWrite_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Leanux.sysPipe2; exact (sysPipe2_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.sysFcntl; exact (sysFcntl_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Leanux.fdget; exact (fdget_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.fdput; exact (fdput_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.taskWorkRun; exact taskWorkRun_sameSnapshot.ordinary)
    | (ordinary_head Leanux.netnsClose; exact netnsClose_sameSnapshot.ordinary)
    | (ordinary_head Leanux.socketCallOn; refine socketCallOn_ordinary _ _ ?_)
    | (ordinary_head Leanux.netlinkRequest; refine netlinkRequest_ordinary _ ?_)
    | (ordinary_head Leanux.rtnetlinkRequest; refine rtnetlinkRequest_ordinary _ ?_)
    | (ordinary_head WG.wgSetDevice; exact wgSetDevice_ordinary _)
    | (ordinary_head WG.wgGetDevice; exact (wgGetDevice_sameSnapshot _).ordinary)
    | (ordinary_head WG.getNlSock; exact (getNlSock_sameSnapshot _).ordinary)
    | (ordinary_head WG.setNlSock; exact (setNlSock_sameSnapshot _ _).ordinary)
    | (ordinary_head WG.netlinkDumpStart; exact (netlinkDumpStart_sameSnapshot _ _).ordinary)
    | (ordinary_head WG.netlinkRecvmsg; exact (netlinkRecvmsg_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.skipCut; exact (skipCut_sameSnapshot _).ordinary)
    | (ordinary_head Leanux.skipCutExactly; exact (skipCutExactly_sameSnapshot _ _ _).ordinary)
    | (ordinary_head WG.wgCreate; exact WGDevice.wgCreate_ordinary)
    | (ordinary_head WG.wgXmit; exact WGDevice.wgXmit_ordinary _ _ _ _)
    | (ordinary_head Env.wgUp; exact EnvFrames.wgUp_ordinary)
    | (ordinary_head Env.wgDown; exact EnvFrames.wgDown_ordinary)
    | (ordinary_head Env.wgDelete; exact EnvFrames.wgDelete_ordinary)
    | (ordinary_head Env.setMtu; exact (EnvFrames.setMtu_sameSnapshot _).ordinary)
    | (ordinary_head Env.wgDeladdr; exact (wgDeladdr_sameSnapshot _).ordinary)
    | (ordinary_head Env.wgDelroute; exact (wgDelroute_sameSnapshot _).ordinary)
    | (ordinary_head Env.advance; exact (advance_sameSnapshot _).ordinary)
    | (ordinary_head Env.routeIntoWg0; exact routeIntoWg0_sameSnapshot.ordinary)
    | (ordinary_head Env.netnsCleanup; exact netnsCleanup_sameSnapshot.ordinary)
    | (ordinary_head Env.fixtureSend; exact fixtureSend_sameSnapshot.ordinary)
    | (ordinary_head Env.xmitPackets; exact (xmitPackets_sameSnapshot _ _ _ _).ordinary)
    | (ordinary_head Env.xmitMulticastLoop; exact (xmitMulticastLoop_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.routeLookup; exact (routeLookup_sameSnapshot _ _ _).ordinary)
    | (ordinary_head Leanux.getK; exact getK_sameSnapshot.ordinary)
    | observer_ordinary_leaf
    | ordinary_strict_step)

theorem dispatch_noReceive_ordinary (call : Syscall) (hc : NoReceiveDispatch call) :
    OrdinaryAction (Leanux.dispatch call) := by
  cases call <;> simp only [NoReceiveDispatch] at hc
  all_goals simp only [Leanux.dispatch]
  all_goals repeat' syscall_ordinary_step

/-- Ordinary dispatch and an ordinary return-to-user branch compose. -/
theorem syscall_ordinary_of_dispatch (call : Syscall) (hc : NoReceiveCall call)
    (hd : OrdinaryAction (Leanux.dispatch call)) : OrdinaryAction (Leanux.syscall call) := by
  cases call <;> simp only [NoReceiveCall] at hc
  all_goals unfold Leanux.syscall
  all_goals repeat' first
    | (ordinary_head Leanux.dispatch; exact hd)
    | syscall_ordinary_step

theorem syscall_noReceive_ordinary (call : Syscall) (hc : NoReceiveCall call) :
    OrdinaryAction (Leanux.syscall call) := by
  have hd : NoReceiveDispatch call := by cases call <;> simp_all [NoReceiveCall, NoReceiveDispatch]
  exact syscall_ordinary_of_dispatch call hc (dispatch_noReceive_ordinary call hd)

theorem dispatchLogged_evolves (call : Syscall) : Evolves (dispatchLogged call) := by
  cases call <;> simp only [dispatchLogged]
  all_goals first
    | (evolves_head socketCallOnLogged
       exact socketCallOnLogged_evolves _ _ (injectLogged_evolves _ _ _ _ _ _))
    | (evolves_head floodLogged; exact floodLogged_evolves _ _ _)
    | (evolves_head batchLogged; exact batchLogged_evolves _)
    | (evolves_head liftM; exact evolves_liftM (dispatch_noReceive_ordinary _ trivial))
    | (repeat' first
        | (evolves_head observeLogged; exact observeLogged_evolves)
        | syscall_ordinary_step
        | evolves_step)

theorem syscallLogged_evolves (call : Syscall) : Evolves (syscallLogged call) := by
  unfold syscallLogged
  repeat' first
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
