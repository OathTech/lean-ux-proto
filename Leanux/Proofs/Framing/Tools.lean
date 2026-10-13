import Leanux.Proofs.Framing.WGKernel

/-! Projection-parametric loop and map rules, and verification-condition setup
for the full WireGuard kernel view. Unsolved conditions stay ordinary goals. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def normalizePinnedName : Lean.Name → Lean.Name
  | .str p "0" => .num (normalizePinnedName p) 0
  | .str p s => .str (normalizePinnedName p) s
  | .num p n => .num (normalizePinnedName p) n
  | .anonymous => .anonymous

/-- A checked reference to a constant in the pinned mirror, including its
private numeric name component. It introduces no new definition or assumption. -/
macro "pinned_const " n:ident : term =>
  pure (Lean.mkCIdent (normalizePinnedName n.getId))

theorem list_view_spec (view : World → σ) (P : σ → Prop) {α β : Type}
    (xs : List α) (init : β) (f : α → β → M (ForInStep β))
    (hf : ∀ x b, ⦃fun w => ⌜P (view w)⌝⦄ f x b
      ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ forIn xs init f
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  let inv : PostCond β (.arg World (.except Stop .pure)) :=
    (⇓? _ w => ⌜P (view w)⌝)
  change Triple (forIn xs init f) (inv.1 init) inv
  refine Std.Do.Spec.forIn_list_const_inv (inv := inv) ?_
  intro x b
  apply Triple.entails_wp_of_post (hf x b)
  constructor
  · intro r
    cases r <;> exact .rfl
  · exact .rfl

theorem map_view_spec (view : World → σ) (P : σ → Prop) {α β : Type}
    (f : α → β) (a : M α)
    (ha : ⦃fun w => ⌜P (view w)⌝⦄ a ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ StateT.map f a
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w b w' hp hr
  change (a.run w >>= fun out => pure (f out.1, out.2)) = .ok (b, w') at hr
  cases he : a.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨x, t⟩
    simp [he] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact (hoare_iff_triple _ _ _).mpr ha w x t hp he

theorem discard_view_spec (view : World → σ) (P : σ → Prop) {α : Type} (a : M α)
    (ha : ⦃fun w => ⌜P (view w)⌝⦄ a ⦃⇓? _ w => ⌜P (view w)⌝⦄) :
    ⦃fun w => ⌜P (view w)⌝⦄ discard a
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := map_view_spec view P (fun _ => ()) a ha


macro "frame_wg" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
  let wrap (term : Lean.Syntax) : Lean.TSyntax [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] :=
    ⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, term]⟩
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"frame_spec_{i}")
  let basics := #[``Leanux.getK, ``Leanux.modifyK, ``Leanux.getFiles,
    ``Leanux.modifyFiles, ``Leanux.modifyFdt, ``Leanux.branch, ``Leanux.branchCmp,
    ``Leanux.branchCmpExcluded, ``Leanux.unsupported, ``Leanux.invariant,
    ``Leanux.WG.andM, ``Leanux.WG.orM]
  let lemmas := (fs.getElems.map fun f => wrap (if f.getId.toString.startsWith "_private." then
      (Lean.mkCIdent (normalizePinnedName f.getId)).raw else f.raw)) ++
    (basics.map fun n => wrap (Lean.mkIdent n).raw) ++ (names.map fun f => wrap f.raw)
  let mut body ← `(tactic|
    (have frame_list (α β : Type) := list_view_spec wgKernelView (α := α) (β := β) (fun s => s = initial)
     have frame_map (α β : Type) := map_view_spec wgKernelView (α := α) (β := β) (fun s => s = initial)
     have frame_discard (α : Type) := discard_view_spec wgKernelView (α := α) (fun s => s = initial)
     mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
       frame_list, frame_map, frame_discard, $lemmas,*]
     all_goals try exact ((⇓? _ w => ⌜wgKernelView w = initial⌝) :
       PostCond _ (.arg World (.except Stop .pure)))
     all_goals try dsimp +zetaDelta only at *
     all_goals try simp_all [wgKernelView, WGKernelView.ofKernel, Option.bind_map, Function.comp_def]
     all_goals try trivial))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (apply SameView.of_wp; intro initial; $body))

end Leanux.Proofs.Framing
