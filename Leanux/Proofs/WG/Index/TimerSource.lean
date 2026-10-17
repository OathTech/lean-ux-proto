import Leanux.Proofs.WG.Index.CallbackSource
import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The current wheel dispatch unit preserves the table invariant on every
normal return, with its actual worker/unit/step checks and concrete callback.
This corrects the removed horizon-based `Env.fireTimer` interface: due selection
belongs to the surrounding `runTimers_wheel_source`, not this unit contract. -/
theorem fireTimer_tables (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (step : Option UInt64) :
    Noise.Product.Ensures (TimerDiscipline.timerDispatchUnit_variant worker pid timer entry step)
      (fun w => TablesSafeWG w.wg) (fun _ w => TablesSafeWG w.wg) := by
  let P : World → Prop := fun w => TablesSafeWG w.wg
  change Noise.Product.Ensures _ P (fun _ => P)
  have lifted {α : Type} (action : WG.M α)
      (contract : Ensures action TablesSafeWG (fun _ => TablesSafeWG)) :
      Noise.Product.Ensures (liftWG action) P (fun _ => P) := by
    intro w result final pre run
    change (((action.run w.wg).run w.ambient) >>= fun ((value, current), inputs) =>
      .ok (value, {w with wg := current, ambient := inputs})) = _ at run
    cases executed : (action.run w.wg).run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, current⟩, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact contract w.wg w.ambient _ current inputs pre executed
  have ambient {α : Type} (action : AmbientM α) :
      Noise.Product.Ensures (liftAmbient action) P (fun _ => P) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (value, inputs) =>
      .ok (value, {w with ambient := inputs})) = _ at run
    cases executed : action.run w.ambient with
    | error stop => rw [executed] at run; cases run
    | ok pair =>
      obtain ⟨value, inputs⟩ := pair
      rw [executed] at run
      cases run
      exact pre
  have ambientWrite (f : Ambient → Ambient) :
      Noise.Product.Ensures (modifyAmbient f : Leanux.M Unit) P (fun _ => P) :=
    ambient (modify f : AmbientM Unit)
  have inv {α : Type} (what : String) :
      Noise.Product.Ensures (invariant what : Leanux.M α) P (fun _ => P) :=
    ambient (AmbientM.invariant what)
  have pureValue {α : Type} (value : α) :
      Noise.Product.Ensures (pure value : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have stop {α : Type} (reason : Stop) :
      Noise.Product.Ensures (throw reason : Leanux.M α) P (fun _ => P) := by
    intro w result final pre run
    cases run
  have read : Noise.Product.Ensures (getWG : Leanux.M WGWorld) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have device : Noise.Product.Ensures (getDev : Leanux.M Device) P (fun _ => P) := by
    apply lifted
    intro g inputs result final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, hd] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have pass (value : Option UInt64) : Noise.Product.Ensures
      (modifyWG fun g => {g with timerPassStep := value} : Leanux.M Unit) P (fun _ => P) := by
    intro w result final pre run
    cases run
    exact pre
  have checkStep (b : UInt64) : Noise.Product.Ensures (Env.requireStepComplete b) P (fun _ => P) := by
    unfold Env.requireStepComplete
    refine Noise.Product.ensures_bind _ _ device ?_
    intro d
    split
    · exact stop _
    · exact pureValue ()
  have callbackSection : Noise.Product.Ensures
      (Env.runTimerSection worker (timerCallback pid timer)) P (fun _ => P) := by
    unfold Env.runTimerSection Env.runWorker
    repeat' first
      | exact pureValue _
      | exact ambientWrite _
      | exact inv _
      | exact lifted _ (timerCallback_tables pid timer)
      | exact ambient _
      | (refine Noise.Product.ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | split
  unfold TimerDiscipline.timerDispatchUnit_variant Env.timerWorker
  repeat' first
    | exact pureValue _
    | exact stop _
    | exact read
    | exact pass _
    | exact checkStep _
    | exact callbackSection
    | exact lifted _ ((ensures_iff _ _ _).mpr (delTimer_tables pid timer))
    | exact ambient _
    | (refine Noise.Product.ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | split

end Leanux.Proofs.WG.Index
