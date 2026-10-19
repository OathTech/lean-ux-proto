import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerCallbackFrames
import Leanux.Proofs.WG.Queues.HolderNapi

/-! The strengthened account occupies C1's existing receive-removal spine.
No new observer or independent upper-bound holder existential is introduced.
Native actor and poll transport of this stronger boundary is still required
before it may be asserted at an initialized destruction cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Queues Queues.RxCredits

/-- Keep the original fixed RX ledger and remove exactly the packets named
by its actual history suffix, as in `HolderNapi.At`. Both reference bounds are
proved on the same remaining carriers and the same durable holders. -/
def ExactAt (initial : RxCredits.Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (w : World) : Prop :=
  ∃ suffix, history = before ++ suffix ∧
    ExactBoundary (remaining initial (NapiCarrier.removedPackets suffix)) loans w.wg

theorem ExactAt.start (account : ExactBoundary carriers loans w.wg)
    (history : List RxHistory.Event) : ExactAt carriers loans history history w := by
  refine ⟨[],by simp,?_⟩
  have empty : remaining carriers [] = carriers := List.filter_eq_self.mpr (fun _ _ => rfl)
  simpa only [NapiCarrier.removedPackets,List.filterMap_nil,empty] using account

theorem ExactAt.lower (account : ExactAt initial loans before history w) :
    HolderNapi.At initial loans before history w := by
  obtain ⟨suffix,history,account⟩ := account
  exact ⟨suffix,history,account.lower⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
