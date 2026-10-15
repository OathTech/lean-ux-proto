import Leanux.Proofs.WG.Index.SessionAllocationFrames
import Leanux.Proofs.WG.Index.ReleaseBounds
import Leanux.Proofs.WG.Noise.SessionModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem clearPut_store_bounded {key : Option KeypairId} {d final : Device}
    (run : ClearPut key d final) (bound : KeypairStoreBounded d) :
    KeypairStoreBounded final := by
  cases run with
  | null => exact bound
  | present d id k resident live word =>
    exact released_store_bounded d id k true resident bound

theorem rotationRun_store_bounded {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (run : RotationRun pid d actions final)
    (bound : KeypairStoreBounded d) : KeypairStoreBounded final := by
  induction run with
  | nil => exact bound
  | write d final change p rest resident tail ih => exact ih bound
  | put d middle final key rest release tail ih =>
    exact ih (clearPut_store_bounded release bound)

/-- The actual ordered allocation and derivation writes preserve the resident
store bound. No claim is made that rotation retains the newly allocated key. -/
theorem sessionPrepared_store_bounded (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (bound : KeypairStoreBounded d) :
    KeypairStoreBounded (sessionPrepared pid d p counter birth) := by
  intro id k found
  by_cases same : d.nextKeypairId = id
  · subst id
    exact Nat.lt_succ_self _
  · have old : d.keypairs[id]? = some k := by
      simpa [sessionPrepared, sessionDerivedDevice, createdDevice,
        Std.TreeMap.getElem?_insert, same] using found
    exact Nat.lt_succ_of_lt (bound _ _ old)

theorem sessionEffect_allocation (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (ok : Bool) (final : Device)
    (bound : KeypairStoreBounded d)
    (effect : SessionEffect pid d p counter ok final finalCounter) :
    KeypairStoreBounded final ∧
    final.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) := by
  cases ok with
  | false =>
    obtain ⟨rfl, _⟩ := effect
    exact ⟨bound, by simp⟩
  | true =>
    obtain ⟨_, _, _, _, birth, rotated, rotation, _, rfl⟩ := effect
    have bounded := rotationRun_store_bounded rotation
      (sessionPrepared_store_bounded pid d p counter birth bound)
    have cursor := rotationRun_allocation_cursor rotation
    exact ⟨bounded, cursor⟩

end Leanux.Proofs.WG.Index
