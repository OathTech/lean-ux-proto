import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Peer

/-! Native index reads preserve their own table. Outer-state separation follows
from the actual index adapter in `Framing.Lift`, including its device guard. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

macro "index_unfold " n:ident : tactic =>
  `(tactic| unfold $(Lean.mkCIdent (normalizePinnedName n.getId)))

theorem indexBucket_sameTable (index : Nat) :
    SameView (id : List IndexEntry → List IndexEntry) (indexBucket index) := by
  apply SameView.of_wp
  intro table
  unfold indexBucket
  apply preserves_bind (hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  intro entries
  exact preserves_pure _

theorem bucketHas_sameTable (walk collide : Decision) (index : Nat) :
    SameView (id : List IndexEntry → List IndexEntry)
      ((pinned_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index) := by
  apply SameView.of_wp
  intro table
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas
  apply preserves_bind ((indexBucket_sameTable index).wp (fun s => s = table))
  intro entries
  apply preserves_bind
  · apply list_view_spec id (fun s => s = table)
    intro entry acc
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch walk true) (fun s => s = table))
    intro _
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch collide _) (fun s => s = table))
    intro same
    split <;> exact preserves_pure _
  · intro result
    dsimp only
    split
    · exact preserves_pure _
    · exact preserves_bind (hoare_liftAmbient (AmbientM.branch walk false) (fun s => s = table))
        (fun _ => preserves_pure _)

end Leanux.Proofs.Framing
