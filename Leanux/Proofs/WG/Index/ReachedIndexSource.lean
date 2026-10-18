import Leanux.Proofs.WG.Index.ReachedIndexFrames
import Leanux.Proofs.WG.Index.ReachedIndexClaims
import Leanux.Proofs.WG.Queues.BaseCoherenceHandshake

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace Reached
open Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

/-- Pair the existing all-outcome account with facts about the identical
normal execution. Errors retain only its actual safe journal. -/
theorem aux_pair {α : Type} (action : RxHistory.Obs α)
    (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (account : PrefixPreserves (HolderAuxiliary.Inv initial loans before)
      OwnerChecks.Safe action)
    (normal : ∀ w h, Aux initial loans before h w → ∀ result v,
      (runPrefix action w h).1 = .ok (result,v) →
        BaseCoherence.Inv v.wg ∧ Core v.wg) :
    PrefixPreserves (Aux initial loans before) OwnerChecks.Safe action := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := account w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error stop => trivial
  | ok pair =>
    rw [run] at post
    exact ⟨post,normal w h entry pair.1 pair.2 run⟩

/-- The original session observer carries the existing complete account,
index component and base relation over one identical execution. Its Stop
branch retains only the existing owner-safe journal. -/
theorem session_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Aux initial loans before) OwnerChecks.Safe
      (Origins.HistoryAdapters.session pid) := by
  apply aux_pair _ initial loans before (HolderAuxiliary.session_preserves initial loans before pid)
  intro w h entry result v run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    (beginSession pid) w v result
    ((Origins.HistoryAdapters.session_erases pid w h).symm.trans run)
  have base := BaseCoherence.transport entry.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.beginSession_view pid)
      w.wg w.ambient result v.wg v.ambient native)
  exact ⟨base,session_core pid w.wg w.ambient result v.wg v.ambient
    (aux_projection entry) native⟩
end Reached
end Leanux.Proofs.WG.Index
