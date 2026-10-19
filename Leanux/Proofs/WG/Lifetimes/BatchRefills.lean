import Leanux.Proofs.WG.Lifetimes.SavedPeers
import Leanux.Proofs.Framing.BatchRefills
import Leanux.Proofs.Logged.PrefixBatch

/-! The landed refill budget reads every saved peer's NAPI flag. Its lifetime
observer records those reads before counting them; the budget consumes no
records and leaves the native state unchanged. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def activationRefillsPrefix : PrefixM LifetimeEvent Nat := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  let polls ← liftWGObserver (savedPeerFilterMap
    (fun _ p => if p.napiScheduled then some () else none) d.peers.toList)
  let left ← liftPrefix recordsLeft
  return left + polls.length * NAPI_POLL_WEIGHT

private theorem poll_count (xs : List (PeerId × Peer)) :
    (xs.filterMap (fun x => if x.2.napiScheduled then some () else none)).length =
      xs.countP (·.2.napiScheduled) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : x.2.napiScheduled <;> simp [hp, ih]

theorem activationRefillsPrefix_erases :
    ErasesPrefix activationRefillsPrefix Env.Activation.refills := by
  unfold activationRefillsPrefix Env.Activation.refills
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
  intro d
  apply erasesPrefix_bind_pure
    (by simpa only [liftWG_pure] using liftWGObserver_erases (savedPeerFilterMap_erases (fun _ p => if p.napiScheduled then some () else none) d.peers.toList))
  rw [poll_count]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro left
  exact erasesPrefix_pure _

theorem activationRefillsPrefix_preserves (c : ProductAmbientContracts I) :
    PrefixPreserves I LifetimeEvent.Safe activationRefillsPrefix := by
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  unfold activationRefillsPrefix
  apply PrefixEnsures.bind (getDev_saved_spec_product c (fun _ => True))
  intro d
  apply PrefixEnsures.bind (savedPeerFilterMap_spec_product c (fun _ => True) _ _)
  intro polls
  apply PrefixEnsures.bind (c.ambient (fun _ => True) AmbientM.recordsLeft)
  intro left
  exact c.pure (fun _ => True) _

end Leanux.Proofs.WG.Lifetimes
