import Leanux.Proofs.WG.Origins.CurrentPoll
import Leanux.Proofs.WG.Origins.CurrentStack

/-! Concrete poll transport on the original persistent RX journal. The stack
callback is the actual fixture stack, including its WireGuard reply path. -/
namespace Leanux.Proofs.WG.CurrentPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues
open Origins.HistorySupport (sessions sessionEvent sensitive)

/-- Every promotion is a poll access/cut/stack event, never a session,
decrypt or copied-trial probe. The old history is kept verbatim. -/
private theorem observed_frame {E : Type} (projection : RxHistory.Event → Option E)
    (quiet : ∀ e, projection (RxHistory.promote e) = none) (pid : PeerId) (budget : Nat) :
    HistoryFrame projection (RxHistory.observePoll pid budget) := by
  intro w h
  change (h ++ _).filterMap projection = h.filterMap projection
  rw [List.filterMap_append,filterMap_disjoint RxHistory.promote projection quiet,List.append_nil]

theorem actual (pid : PeerId) (budget : Nat) (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => CurrentLifecycle.Inv history w.wg)
      (rxPoll pid budget (fun bytes => bytes.forM Env.deliverInner)) :=
  poll pid budget _ CurrentStack.stackForM_preserves history

theorem history (pid : PeerId) (budget : Nat) :
    CurrentHistory.Preserves (RxHistory.observePoll pid budget) := by
  apply CurrentHistory.erased _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) _ (actual pid budget)
  exact observed_frame sessionEvent (by intro e; cases e <;> rfl) pid budget

/-- The actual poll retains prior positional checks and material support,
including Stop prefixes. This remains a supplied-invariant contract. -/
theorem checked (pid : PeerId) (budget : Nat) :
    CurrentChecks.Preserves (RxHistory.observePoll pid budget) :=
  CurrentChecks.quiet _ (RxHistory.observePoll_appends pid budget)
    (observed_frame sensitive (by intro e; cases e <;> rfl) pid budget)
    (Origins.HistorySupport.poll pid budget) (history pid budget)

end Leanux.Proofs.WG.CurrentPoll
