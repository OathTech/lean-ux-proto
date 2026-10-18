import Leanux.Proofs.WG.Index.ReachedIndexBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.Reached
open Lean Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Queues Queues.RxCredits

/-- The outer source may return its own actual remaining ledger. -/
def AnyEntry (history : List RxHistory.Event) (w : World) : Prop :=
  ∃ cs, Entry cs [] history w

theorem anyEntry_safe (h : List RxHistory.Event) (w : World)
    (entry : AnyEntry h w) : OwnerChecks.Safe h := by
  obtain ⟨cs,entry⟩ := entry
  exact entry.1.2.safe
end Leanux.Proofs.WG.Index.Reached
