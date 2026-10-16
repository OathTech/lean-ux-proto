import Leanux.Proofs.Framing.Tools
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
  mvcgen [indexBucket]

theorem bucketHas_sameTable (walk collide : Decision) (index : Nat) :
    SameView (id : List IndexEntry → List IndexEntry)
      ((pinned_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index) := by
  apply SameView.of_wp
  intro table
  have hb := (indexBucket_sameTable index).wp (fun s => s = table)
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas
  mvcgen [hb, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ s => ⌜s = table⌝) :
    PostCond _ (.arg (List IndexEntry) (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.Framing
