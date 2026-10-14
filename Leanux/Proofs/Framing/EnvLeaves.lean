import Leanux.Proofs.Framing.Control
import Leanux.Proofs.Framing.KernelEffects
import Leanux.Env

/-! Complete Kernel frames for environment bookkeeping leaves. Source inspection
is separate: these actions inspect scalar/container metadata and records, not
resolved peer, keypair or packet objects. Stops remain the original Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem deliverSent_sameKernel : SameKernel Env.deliverSent := by
  apply sameKernel_of_wp
  intro k
  have hl (α β : Type) := list_view_spec (fun w : World => w.k) (α := α) (β := β) (fun s => s = k)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, Env.deliverSent, hl, unsupported]

theorem peekNextSite_sameKernel : SameKernel Env.peekNextSite := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.peekNextSite]

theorem requireNoCryptWork_sameKernel : SameKernel Env.requireNoCryptWork := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.requireNoCryptWork, getK, unsupported]

theorem timerWorker_sameKernel (t : PeerTimer) : SameKernel (Env.timerWorker t) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.timerWorker, invariant]

theorem advance_sameKernel (ticks : Nat) : SameKernel (Env.advance ticks) := by
  apply sameKernel_of_wp
  intro k
  have hh := sameKernel_wp _ (hidden_sameKernel .timeAdvance) (fun s => s = k)
  mvcgen [Env.advance, hh, unsupported]

end Leanux.Proofs.Framing
