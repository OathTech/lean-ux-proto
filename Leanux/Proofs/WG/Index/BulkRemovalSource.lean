import Leanux.Proofs.WG.Index.PeerRemovalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Both actual saved-peer loops and their record guards remain operational. -/
theorem peerRemoveAll_preserves (P : WGWorld → Prop)
    (free : Ensures WG.free P (fun _ => P))
    (dead : ∀ pid, Ensures (peerMakeDead pid) P (fun _ => P))
    (afterDead : ∀ pid, Ensures (peerRemoveAfterDead pid) P (fun _ => P)) :
    Ensures peerRemoveAll P (fun _ => P) := by
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) P (fun _ => P)) :
      Ensures (forIn xs initial body) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr
      (Framing.list_view_spec id P xs initial body
        (fun x b => (ensures_iff _ _ _).mp (step x b)))
  unfold peerRemoveAll
  refine ensures_bind _ _ free (fun _ => ?_)
  refine ensures_bind _ _ hdev (fun d => ?_)
  refine ensures_bind _ _ (hlist _ _ _ ?_) ?_
  · intro pid acc
    refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
    exact ensures_bind _ _ (dead pid) (fun _ => hpure _)
  · intro _
    refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
    refine ensures_bind _ _ (hlist _ _ _ ?_) ?_
    · intro pid acc
      refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
      exact ensures_bind _ _ (afterDead pid) (fun _ => hpure _)
    · intro _
      exact ensures_bind _ _ (hbranch _ _) (fun _ => hpure ())

end Leanux.Proofs.WG.Index
