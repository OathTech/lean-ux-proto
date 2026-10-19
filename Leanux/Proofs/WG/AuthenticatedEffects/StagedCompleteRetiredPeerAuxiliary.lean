import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerEnvironment
import Leanux.Proofs.WG.Queues.HolderAuxiliary

/-! The original auxiliary invariant and exact peer account describe one
execution and the same RX-removal history. Both retain their own stronger
state facts; no independent erased histories are joined. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Auxiliary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

def Inv (initial : Ledger) (loans : Reservations) (before h : List RxHistory.Event)
    (w : World) : Prop :=
  HolderAuxiliary.Inv initial loans before h w ∧ ExactAt initial loans before h w

theorem Inv.safe (hi : Inv initial loans before h w) : OwnerChecks.Safe h := hi.1.2.1.safe

theorem Inv.entry (hi : Inv initial loans before h w) :
    ConfiguredIdentity.Inv w.wg ∧ OwnerBounds.Carrier w.wg ∧
      CurrentSlots.Inv w.wg ∧ Packets.Inv w.wg := HolderAuxiliary.entry hi.1

theorem Inv.residual (hi : Inv initial loans before h w)
    (suffix : h = before ++ removed) :
    ExactBoundary (remaining initial (NapiCarrier.removedPackets removed)) loans w.wg := by
  obtain ⟨other,history,account⟩ := hi.2
  have same : other = removed := List.append_cancel_left (history.symm.trans suffix)
  simpa only [same] using account

theorem store (hi : Inv initial loans before h w)
    (same : productStoreView v = productStoreView w) : Inv initial loans before h v :=
  ⟨HolderAuxiliary.store hi.1 same,ExactAt.store hi.2 same⟩

/-- Actor obligations may use the full auxiliary entry, but their result
must refer to this exact observer's returned world and actual history. -/
def ExactPost (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (action : RxHistory.Obs α) : Prop :=
  ∀ w h, Inv initial loans before h w → ∀ x v,
    (runPrefix action w h).1 = .ok (x,v) →
    ExactAt initial loans before (runPrefix action w h).2 v

theorem exact_post (keeps : PrefixPreserves (ExactAt initial loans before) (fun _ => True) action) :
    ExactPost initial loans before action := by
  intro w h hi x v run
  have post := (keeps w h hi.2).choose_spec.2.2
  simpa only [run] using post

theorem pair (action : RxHistory.Obs α)
    (old : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (account : ExactPost initial loans before action) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe action := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := old w h hi.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [run] using post,account w h hi out.1 out.2 run⟩

theorem pair_preserves (action : RxHistory.Obs α)
    (old : PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (account : PrefixPreserves (ExactAt initial loans before) (fun _ => True) action) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe action :=
  pair action old (exact_post account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Auxiliary
