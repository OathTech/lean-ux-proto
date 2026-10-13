import Leanux.Proofs.Framing.WP
import Leanux.Env.Stack

/-! Access-free original stack leaves, framed over the complete Kernel. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.Env Std.Do

theorem stackExcluded_failure (row : String) (w : World) :
    ∃ e, (Stack.excluded row).run w = .error e := ⟨_, rfl⟩

theorem stackExcluded_sameKernel (row : String) : SameKernel (Stack.excluded row) := by
  intro w a v hr
  obtain ⟨e, he⟩ := stackExcluded_failure row w
  rw [he] at hr
  contradiction

/-- IPv6 inspects packet bytes and device scalar fields, and may append to the
sender inbox; it performs no resident-store lookup or update. -/
theorem stackReceive6_sameKernel (pkt : List UInt8) : SameKernel (Stack.receive6 pkt) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Stack.receive6, Stack.excluded, getK, invariant, unsupported]

end Leanux.Proofs.Framing
