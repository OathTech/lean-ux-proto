import Leanux.Proofs.WG.Index.AipRemovalFrames
import Leanux.Proofs.WG.Index.FlushSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original removal path preserves numeric and embedded-owner uniqueness
and the hashed-keypair allocation bound, with only the table invariant at entry. -/
theorem removeByPeer_tables (pid : PeerId) :
    Campaign2.Ensures (removeByPeer pid) View.TablesSafe (fun _ s => View.TablesSafe s) := by
  change Ensures (removeByPeer pid) TablesSafeWG (fun _ => TablesSafeWG)
  intro g a result final after safe run
  exact tablesSafe_of_cursor g final
    (removeByPeer_spec_tableCursor_variant pid _ g a result final after rfl run) safe

/-- Outer removal includes the NULL branch, dead-marking, actual worker flushes
and final release. This normal-return contract asserts no totality or owner
residency and does not constrain the ambient records. -/
theorem peerRemove_tables (peer : Option PeerId) :
    Campaign2.Ensures (peerRemove peer) View.TablesSafe (fun _ s => View.TablesSafe s) := by
  change Ensures (peerRemove peer) TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hdead (pid : PeerId) : Ensures (peerMakeDead pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a result final after safe run
    exact tablesSafe_of_cursor g final
      (peerMakeDead_spec_tableCursor_variant pid _ g a result final after rfl run) safe
  cases peer with
  | none =>
    unfold peerRemove
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro isNull
    cases isNull with
    | true => exact hpure ()
    | false =>
      exact (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.invariant "unreachable") TablesSafeWG)
  | some pid =>
    unfold peerRemove
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro isNull
    cases isNull with
    | true => exact hpure ()
    | false => exact ensures_bind _ _ (hdead pid) (fun _ => peerRemoveAfterDead_tables pid)

end Leanux.Proofs.WG.Index
