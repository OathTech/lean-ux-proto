import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

/-- Frame of the actual validation prefix for an already selected wheel unit, over the original joint subsystem predicate. -/
theorem timerSelection_kernel_spec
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop)
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) (step : Option UInt64) :
    ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ timerDispatchPrefix_variant worker pid timer we step
      ⦃⇓? _ w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  have complete (b : UInt64) : Noise.Product.Ensures (requireStepComplete b)
      (fun w => P w.wg w.fs w.tasks w.seccomp) (fun _ w => P w.wg w.fs w.tasks w.seccomp) := by
    intro entry value final pre run
    cases device : entry.wg.dev with
    | none =>
      change (((liftWG getDev).run entry) >>= _) = _ at run
      have native : ((getDev).run entry.wg).run entry.ambient =
          .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp only [getDev, StateT.run_bind, StateT.run_get, pure_bind, device]
        rfl
      have absent : (liftWG getDev).run entry = .error (.invariant "no WireGuard device in this trace's fixture") := by
        change (((getDev).run entry.wg).run entry.ambient >>= fun ((value, current), inputs) =>
          Except.ok (value, {entry with wg := current, ambient := inputs})) = _
        rw [native]
        rfl
      rw [absent] at run
      cases run
    | some d =>
      change (((liftWG getDev).run entry) >>= _) = _ at run
      have native : ((getDev).run entry.wg).run entry.ambient = .ok ((d, entry.wg), entry.ambient) := by
        simp only [getDev, StateT.run_bind, StateT.run_get, pure_bind, device]
        rfl
      have present : (liftWG getDev).run entry = .ok (d, entry) := by
        change (((getDev).run entry.wg).run entry.ambient >>= fun ((value, current), inputs) =>
          Except.ok (value, {entry with wg := current, ambient := inputs})) = _
        rw [native]
        rfl
      rw [present] at run
      dsimp only [Bind.bind, Except.bind] at run
      cases pending : TimerWheel.anotherAtStep d b with
      | none => rw [pending] at run; cases run; exact pre
      | some pair =>
        obtain ⟨picked, kind⟩ := pair
        rw [pending] at run
        cases run
  have tail : Noise.Product.Ensures
      (if let some b := step then if b != we.bucketExpiry then requireStepComplete b else pure () else pure () : Leanux.M Unit)
      (fun w => P w.wg w.fs w.tasks w.seccomp) (fun _ w => P w.wg w.fs w.tasks w.seccomp) := by
    cases step with
    | none => intro entry value final pre run; cases run; exact pre
    | some b =>
      by_cases same : b != we.bucketExpiry
      · simpa only [same, ite_true] using complete b
      · simp only [same, Bool.false_eq_true, ite_false]
        intro entry value final pre run; cases run; exact pre
  have peek : Noise.Product.Ensures (peekUnit worker : Leanux.M (Option Nat))
      (fun w => P w.wg w.fs w.tasks w.seccomp) (fun _ w => P w.wg w.fs w.tasks w.seccomp) := by
    intro entry value final pre run
    change ((AmbientM.peekUnit worker).run entry.ambient >>= _) = _ at run
    cases actual : (AmbientM.peekUnit worker).run entry.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair => rw [actual] at run; cases run; exact pre
  let expected : Worker := match timer with
    | .retransmitHandshake => .timerRetransmit
    | .sendKeepalive => .timerSendKeepalive
    | .newHandshake => .timerNewHandshake
    | .zeroKeyMaterial => .timerZeroKey
    | .persistentKeepalive => .timerPersistentKeepalive
  have workerRun : timerWorker timer = pure expected := by cases timer <;> rfl
  unfold timerDispatchPrefix_variant
  rw [workerRun]
  simp only [pure_bind]
  by_cases wrong : worker != expected
  · simp only [wrong, ite_true]
    intro entry value final pre run
    cases run
  · simp only [wrong, Bool.false_eq_true, ite_false]
    refine Noise.Product.ensures_bind (Q := fun _ w => P w.wg w.fs w.tasks w.seccomp) _ _ peek ?_
    intro named
    cases named with
    | none =>
      cases step <;> simpa only [timerDispatchPrefix_variant.match_6] using tail
    | some unit =>
      intro entry value final pre run
      simp only [StateT.run_bind] at run
      have readWG : (getWG : Leanux.M WGWorld).run entry = .ok (entry.wg, entry) := rfl
      rw [readWG] at run
      dsimp only [Bind.bind, Except.bind] at run
      cases found : entry.wg.timerUnits.find? (·.1 == unit) with
      | none => rw [found] at run; cases run
      | some triple =>
        obtain ⟨address, picked, kind⟩ := triple
        rw [found] at run
        by_cases mismatch : picked != pid || kind != timer
        · simp only [mismatch, ite_true] at run
          cases run
        · simp only [mismatch, Bool.false_eq_true, ite_false] at run
          exact tail entry value final pre run

end Leanux.Proofs.WG.TimerDiscipline
