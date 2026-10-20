import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointPoll

/-! Original scheduled, inline and IRQ-exit NAPI sources. The pending list
is captured once, and original placement/section guards keep their order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

macro "napi_dispatch_shape" : tactic => `(tactic| first
  | (napi_shape_head Driver.nativePollObserved; exact pollShape _ _)
  | (napi_wg_head RxNapi.pendingSource; exact .native (.metadata _ NapiMetadata.pendingShape))
  | (napi_wg_head RxNapi.scheduledSource; exact .native (.metadata _ NapiMetadata.scheduledShape))
  | (napi_native_head getAmbient; exact .native .ambient)
  | (napi_native_head peekHiddenSite; exact .native .hiddenSite)
  | (napi_native_head chooseNapiHere; exact .native .choose)
  | (napi_native_head hidden; first | exact .native .start | exact .native .stop)
  | (napi_native_head modifyAmbient; first | exact .native .netEnter | exact .native .netLeave)
  | (napi_shape_head runWorkerPrefix; unfold runWorkerPrefix)
  | napi_poll_shape
  | napi_stack_shape)

noncomputable def softirqShape : Shape (Driver.softirqObserved hooks) := by
  apply Shape.marked .softirq
  unfold Driver.softirqObserved RxNapi.softirqWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' napi_dispatch_shape

noncomputable def inlineShape : Shape (Driver.inlinePollObserved hooks) := by
  apply Shape.marked .inlinePoll
  unfold Driver.inlinePollObserved RxNapi.inlineWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' napi_dispatch_shape

noncomputable def irqShape : Shape (Driver.irqExitObserved hooks) := by
  apply Shape.marked .irqExit
  unfold Driver.irqExitObserved RxNapi.irqExitWith
  repeat' first
    | (napi_shape_head Driver.softirqObserved; exact softirqShape)
    | napi_dispatch_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
