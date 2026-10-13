import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.KernelEffects

/-! Original scalar index operations. The canonical frame omits only the index
entries; device presence, every resident value and all allocation counters stay
in the view. The source still fails on a missing device and exhausted records. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

macro "index_unfold " n:ident : tactic =>
  `(tactic| unfold $(Lean.mkCIdent (normalizePinnedName n.getId)))

def indexKernel (k : Kernel) : Kernel :=
  {k with wg := k.wg.map fun d => {d with indexTable := []}}

def indexKernelView (w : World) : Kernel := indexKernel w.k

theorem indexBucket_sameKernel (index : Nat) : SameKernel (indexBucket index) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [indexBucket, getDev, getK, invariant]

theorem bucketHas_sameKernel (walk collide : Decision) (index : Nat) :
    SameKernel ((pinned_const _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas) walk collide index) := by
  apply sameKernel_of_wp
  intro k
  have hb := sameKernel_wp _ (indexBucket_sameKernel index) (fun s => s = k)
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.bucketHas
  mvcgen [hb, branch]
  all_goals try exact ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem modifyDev_index_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, {f d with indexTable := []} = {d with indexTable := []}) :
    ⦃fun w => ⌜P (indexKernelView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (indexKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [indexKernelView, indexKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem indexInsert_sameIndexKernel (pid : PeerId) (kind : IndexKind) :
    SameView indexKernelView (indexInsert pid kind) := by
  apply SameView.of_wp
  intro initial
  have hh := fun site => (SameView.of_sameKernel indexKernel (hidden_sameKernel site)).wp (fun s => s = initial)
  have hb := (SameView.of_sameKernel indexKernel recordBudget_sameKernel).wp (fun s => s = initial)
  have he := (SameView.of_sameKernel indexKernel (budgetExhausted_sameKernel (α := Nat) "index draws")).wp (fun s => s = initial)
  have hbucket := fun walk collide i => (SameView.of_sameKernel indexKernel (bucketHas_sameKernel walk collide i)).wp (fun s => s = initial)
  have hm := modifyDev_index_spec (fun s => s = initial)
  unfold indexInsert
  index_unfold _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
  mvcgen [getDev, getK, branch, invariant, unsupported, hh, hb, he, hbucket, hm]
  all_goals try exact ((⇓? _ w => ⌜indexKernelView w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [indexKernelView, indexKernel]
  all_goals trivial

end Leanux.Proofs.Framing
