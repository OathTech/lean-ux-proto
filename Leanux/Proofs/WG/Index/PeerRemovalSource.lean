import Leanux.Proofs.WG.Index.FlushSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original optional peer removal, including its NULL decision and
actual dead-marking and drain sequence. Callbacks concern concrete actions. -/
theorem peerRemove_preserves (P : WGWorld → Prop)
    (dead : ∀ pid, Ensures (peerMakeDead pid) P (fun _ => P))
    (afterDead : ∀ pid, Ensures (peerRemoveAfterDead pid) P (fun _ => P))
    (peer : Option PeerId) : Ensures (peerRemove peer) P (fun _ => P) := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  cases peer with
  | none =>
    unfold peerRemove
    refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
    intro isNull
    cases isNull with
    | true => exact hpure ()
    | false =>
      exact (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.invariant "unreachable") P)
  | some pid =>
    unfold peerRemove
    refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
    intro isNull
    cases isNull with
    | true => exact hpure ()
    | false => exact ensures_bind _ _ (dead pid) (fun _ => afterDead pid)

end Leanux.Proofs.WG.Index
