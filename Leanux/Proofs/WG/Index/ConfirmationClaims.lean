import Leanux.Proofs.WG.Index.ClearFrames
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Confirmation's actual double check, slot writes and immediate release preserve
numeric-index uniqueness, owner uniqueness and the hashed allocation bound.
The optional-device domain has no residency, distinct-slot or reference premise;
this concerns normal returns and does not assert successful confirmation. -/
theorem receivedWithKeypair_tables (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.TablesSafe
      (fun _ s => View.TablesSafe s) := by
  change Ensures (receivedWithKeypair pid received) TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (x : α) :
      Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    cases run
    exact pre
  have hread (id : PeerId) : Ensures (getPeer id) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec id TablesSafeWG)
      g a r final after pre run).1
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  unfold receivedWithKeypair
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hread _
    | with_reducible exact hbranch _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (modifyPeer_tables _ _)
    | with_reducible exact (ensures_iff _ _ _).mpr (keypairPut_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

end Leanux.Proofs.WG.Index
