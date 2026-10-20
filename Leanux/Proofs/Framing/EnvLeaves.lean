import Leanux.Env
import Leanux.Proofs.Framing.Product

/-! Frames over the original 43-field product observation for environment
bookkeeping. These make no source-access claim and retain the actual Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem deliverSent_sameKernel : SameProductStore Env.deliverSent := by
  have hg : SameProductStore getWG := fun k => productGetWG_spec (fun v => v = k)
  have hr : SameProductStore getRouting := fun k => productRouting_spec
    ((fun (r : Net.State) => r.toRouting) <$> (get : Net.M Net.State)) (fun v => v = k)
  have edit (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have stop {α : Type} (why : String) : SameProductStore (unsupported why : Leanux.M α) :=
    fun k => productAmbient_spec (AmbientM.unsupported why)
      (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Env.deliverSent
  apply SameView.bind hg
  intro w
  apply SameView.bind
  · intro k
    apply list_view_spec productStoreView (fun v => v = k)
    intro dg accumulator
    apply preserves_bind (hr k)
    intro route
    dsimp only
    split
    · exact preserves_bind (edit _ k) (fun _ => preserves_pure _)
    · split
      · exact preserves_bind (edit _ k) (fun _ => preserves_pure _)
      · exact preserves_bind (edit _ k) (fun _ => preserves_pure _)
      · split
        · exact preserves_bind (stop "a datagram routed back into wg0" k) (fun _ => preserves_pure _)
        · exact preserves_pure _
  intro _
  exact fun k => productModifyWG_spec (fun v => v = k) (fun w => {w with sent := []}) (fun _ => rfl)

/-- The pending-unit test the namespace close and cleanup make (2026-10-20,
the namespace-pin fix): an ambient read, then a pure answer. -/
theorem pendingDevice_sameKernel (w : Worker) (queued : Bool) :
    SameProductStore (Env.pendingDevice w queued) := by
  have read : SameProductStore getAmbient := fun k => productAmbient_spec
    (get : AmbientM Ambient) (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Env.pendingDevice
  exact SameView.bind read (fun _ => SameView.pure _ _)

theorem peekNextSite_sameKernel : SameProductStore Env.peekNextSite := by
  have read : SameProductStore getAmbient := fun k => productAmbient_spec
    (get : AmbientM Ambient) (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Env.peekNextSite
  apply SameView.bind read
  intro ambient
  split <;> exact SameView.pure _ _

theorem requireNoCryptWork_sameKernel : SameProductStore Env.requireNoCryptWork := by
  have read : SameProductStore getWG := fun k => productGetWG_spec (fun v => v = k)
  unfold Env.requireNoCryptWork
  apply SameView.bind read
  intro w
  split
  · split
    · exact fun k => productAmbient_spec
        (AmbientM.unsupported "crypt work queued in a system call (its worker's timing)")
        (fun w => productStoreView w = k) (fun _ _ h => h)
    · exact SameView.pure _ _
  · exact SameView.pure _ _

theorem timerWorker_sameKernel (t : PeerTimer) : SameProductStore (Env.timerWorker t) := by
  unfold Env.timerWorker
  split
  · exact SameView.pure _ _
  · exact fun k => productAmbient_spec (AmbientM.invariant "a peer timer without a callback unit")
      (fun w => productStoreView w = k) (fun _ _ h => h)

theorem advance_sameKernel (ticks : Nat) : SameProductStore (Env.advance ticks) := by
  have hg : SameProductStore getWG := fun k => productGetWG_spec (fun v => v = k)
  have ha {α : Type} (a : AmbientM α) : SameProductStore (monadLift a : Leanux.M α) :=
    fun k => productAmbient_spec a (fun w => productStoreView w = k) (fun _ _ h => h)
  have edit (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  have stopped {α : Type} (e : Stop) : SameProductStore (throw e : Leanux.M α) := by
    apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
  have finish (j0 j1 : UInt64) : SameProductStore (do
      if j1 - j0 != ticks.toUInt64 then
        throw (.hidden s!"the advance moved jiffies from {j0} to {j1}, not by {ticks}")
      modifyWG fun w => {w with jiffiesLast := some j1}
      modifyEnv fun e => {e with lastAdvance := some (j0, j1)}
      pure 0 : Leanux.M Int) := by
    have tail : SameProductStore (do
        modifyWG fun w => {w with jiffiesLast := some j1}
        modifyEnv fun e => {e with lastAdvance := some (j0, j1)}
        pure 0 : Leanux.M Int) := by
      apply SameView.bind (fun k => productModifyWG_spec (fun v => v = k)
        (fun w => {w with jiffiesLast := some j1}) (fun _ => rfl))
      intro _
      exact SameView.bind (edit (fun e => {e with lastAdvance := some (j0, j1)}))
        (fun _ => SameView.pure _ _)
    dsimp only
    split
    · exact SameView.bind (stopped _) (fun _ => tail)
    · exact tail
  unfold Env.advance
  apply SameView.bind hg
  intro w
  apply SameView.bind (ha (get : AmbientM Ambient))
  intro ambient
  dsimp only
  split
  · simp only [pure_bind]
    exact finish _ _
  · split
    · exact SameView.bind
        (ha (AmbientM.unsupported "a time advance without arm records (the timers' expiries are unknown)") :
          SameProductStore (unsupported "a time advance without arm records (the timers' expiries are unknown)" : Leanux.M Unit))
        (fun _ => SameView.bind (ha (AmbientM.hidden .timeAdvance)) (fun bs => by
          simpa only [pure_bind] using finish (WG.recordWord64 bs 0) (WG.recordWord64 bs 1)))
    · exact SameView.bind (ha (AmbientM.hidden .timeAdvance)) (fun bs => by
        simpa only [pure_bind] using finish (WG.recordWord64 bs 0) (WG.recordWord64 bs 1))

end Leanux.Proofs.Framing
