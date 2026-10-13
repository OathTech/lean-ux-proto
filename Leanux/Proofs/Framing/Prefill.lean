import Leanux.Proofs.Framing.Tools
import Leanux.Seccomp.Prefill

/-! The pre-window fixture changes only filter and task state. The translated
program remains an arbitrary pure result; no large translation is evaluated. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

private theorem foldl_view {α β σ : Type} (view : β → σ) (f : β → α → β)
    (hf : ∀ b x, view (f b x) = view b) (xs : List α) (b : β) :
    view (xs.foldl f b) = view b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons, ih] using hf b x

private theorem forIn_ok {α β : Type} (xs : List α) (f : α → β → β) (b : β) :
    (forIn xs b (fun x b => Except.ok (.yield (f x b))) : Except String β) =
      .ok (xs.foldl (fun b x => f x b) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp only [List.forIn_cons, List.foldl_cons, Bind.bind, Except.bind, ih]

theorem prefill_wgKernel (n : Nat) (k k' : Kernel)
    (hr : Seccomp.Prefill.apply n k = .ok k') :
    WGKernelView.ofKernel k' = WGKernelView.ofKernel k := by
  unfold Seccomp.Prefill.apply at hr
  split at hr
  · contradiction
  · generalize Seccomp.Prefill.translated = result at hr
    cases result with
    | error e => contradiction
    | ok prog =>
      simp only [Std.Legacy.Range.forIn_eq_forIn_range',
        Bind.bind, Except.bind, pure, Except.pure] at hr
      simp only [forIn_ok] at hr
      injection hr with heq
      subst k'
      change WGKernelView.ofKernel ((List.foldl _ _ _ : Kernel × Option FilterId).1) = WGKernelView.ofKernel k
      exact foldl_view (fun p : Kernel × Option FilterId => WGKernelView.ofKernel p.1)
        _ (by intros; rfl) _ (k, none)

end Leanux.Proofs.Framing
