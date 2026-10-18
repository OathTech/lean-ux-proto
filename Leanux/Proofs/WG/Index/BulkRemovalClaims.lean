import Leanux.Proofs.WG.Index.BulkRemovalFrames
import Leanux.Proofs.WG.Index.PeerRemovalClaims

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Bulk removal preserves numeric and embedded-owner uniqueness and the
hashed-keypair allocation bound on normal return. Both saved-peer loops and
their real cleanup run; no residency, trie shape, queue or readiness premise
is imposed, and successful completion is not asserted. -/
theorem peerRemoveAll_tables :
    Campaign2.Ensures peerRemoveAll View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures peerRemoveAll TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hfree : Ensures WG.free TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after safe run
    exact tablesSafe_of_cursor g final
      (free_spec_tableCursor_variant _ g ambient result final after rfl run) safe
  have hdead (pid : PeerId) :
      Ensures (peerMakeDead pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after safe run
    exact tablesSafe_of_cursor g final
      (peerMakeDead_spec_tableCursor_variant pid _ g ambient result final after rfl run) safe
  have hlist {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs initial body) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr
      (Framing.list_view_spec id TablesSafeWG xs initial body
        (fun x b => (ensures_iff _ _ _).mp (step x b)))
  unfold peerRemoveAll
  refine ensures_bind _ _ hfree (fun _ => ?_)
  refine ensures_bind _ _ hdev (fun d => ?_)
  refine ensures_bind _ _ (hlist _ _ _ ?_) ?_
  · intro pid acc
    refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
    exact ensures_bind _ _ (hdead pid) (fun _ => hpure _)
  · intro _
    refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
    refine ensures_bind _ _ (hlist _ _ _ ?_) ?_
    · intro pid acc
      refine ensures_bind _ _ (hbranch _ _) (fun _ => ?_)
      exact ensures_bind _ _ (peerRemoveAfterDead_tables pid) (fun _ => hpure _)
    · intro _
      exact ensures_bind _ _ (hbranch _ _) (fun _ => hpure ())

end Leanux.Proofs.WG.Index
