import Leanux.Proofs.WG.Index.TimerProductRulesSource
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.PendingTimerFrames
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.TimerProduct
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
def Retained (entry : TagMap) (w : World) : Prop := TagsRetained entry (tagView w.wg)

theorem native {α : Type} (entry : TagMap) (action : WG.M α)
    (normal : Preserves (fun g => TagsRetained entry (tagView g)) action) :
    Preserves (Retained entry) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value final hi original
  rw [liftWG_run] at original
  cases run : (action.run w.wg).run w.ambient with
  | error stop => simp [run,Except.map] at original
  | ok result =>
    rcases result with ⟨⟨value,g⟩,after⟩
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at original
    obtain ⟨rfl,rfl⟩ := original
    exact (hoare_iff_run_ambient _ _ _).mp normal w.wg w.ambient value g after hi run

theorem stored {α : Type} (entry : TagMap) (action : Leanux.M α)
    (frame : SameProductStore action) : Preserves (Retained entry) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value final hi run
  have same := congrArg (fun s : ProductStore43 => responseTagMap s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp frame w value final run)
  change TagsRetained entry (tagView final.wg)
  change tagView final.wg = tagView w.wg at same
  rw [same]; exact hi

theorem timerSection (entry : TagMap) (worker : Worker) (body : Leanux.M Unit)
    (normal : Preserves (Retained entry) body) :
    Preserves (Retained entry) (Env.runTimerSection worker body) :=
  TimerDiscipline.runTimerSection_kernel_contract worker body
    (fun wg _ _ _ => TagsRetained entry (tagView wg))
    (fun wg _ _ _ => TagsRetained entry (tagView wg)) normal

private theorem ambient {α : Type} (entry : TagMap) (action : AmbientM α) :
    Preserves (Retained entry) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

macro "driver_timer_product_step " entry:term : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored $entry _ (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stored $entry _ (PendingScheduler.requireStepComplete_store _))
  | (rx_retention_head getWG; exact stored $entry _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head modifyWG; exact stored $entry _ (fun initial =>
      productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient $entry _)
  | rx_retention_step)

theorem dispatch (entry : TagMap)
    (callback : ∀ pid timer, Preserves (fun g => TagsRetained entry (tagView g)) (timerCallback pid timer))
    (del : ∀ pid timer, Preserves (fun g => TagsRetained entry (tagView g)) (delTimer pid timer))
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    Preserves (Retained entry) (timerDispatchUnit worker pid timer wheel prior) :=
  Index.TimerProductRules.dispatch _ (fun {_}=>stored entry) (timerSection entry)
    (fun p t=>native entry _ (callback p t)) (fun p t=>native entry _ (del p t))
    worker pid timer wheel prior

theorem placeholder (entry : TagMap)
    (callback : ∀ pid timer, Preserves (fun g => TagsRetained entry (tagView g)) (timerCallback pid timer))
    (del : ∀ pid timer, Preserves (fun g => TagsRetained entry (tagView g)) (delTimer pid timer))
    (j : UInt64) :
    Preserves (Retained entry) (RxHistory.placeholderTimerPassSource j) :=
  Index.TimerProductRules.placeholder _ (fun {_}=>stored entry) (timerSection entry)
    (fun p t=>native entry _ (callback p t)) (fun p t=>native entry _ (del p t)) j

end Leanux.Proofs.WG.Noise.DriverTags.TimerProduct

