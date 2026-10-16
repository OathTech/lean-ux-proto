import Leanux.Proofs.WG.Keypairs.OrdinaryHot
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.Proofs.Framing.WGKernel

/-! Reusable verification-condition setup for helpers that preserve the
receive-state projection. Unsolved conditions remain ordinary Lean goals. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

/-- Receive lifetime state is a pure projection of the seven-field store view. -/
def snapshotOfWGStoreView (v : WGStoreView) : Snapshot :=
  ⟨v.keypairCounter, fun i => (v.dev.bind fun d => d.keypairs[i]?).map cell⟩

theorem sameSnapshot_of_sameWGStore (h : SameWGStore a) : SameSnapshot a :=
  h.of_factor snapshotOfWGStoreView snapshot (fun _ => rfl)

theorem modifyDev_snapshot_spec (P : Snapshot → Prop) (f : Device → Device)
    (hf : ∀ d, (f d).keypairs = d.keypairs) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [snapshot, modifyDev, Option.bind_map, Function.comp_def, hf] using hp

theorem list_snapshot_spec (P : Snapshot → Prop) {α β : Type}
    (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β))
    (hf : ∀ x b, ⦃fun w => ⌜P (snapshot w)⌝⦄ f x b
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ forIn xs init f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  list_view_spec snapshot P xs init f hf

theorem map_snapshot_spec (P : Snapshot → Prop) {α β : Type}
    (f : α → β) (a : WG.M α)
    (ha : ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ StateT.map f a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  map_view_spec snapshot P f a ha

theorem discard_snapshot_spec (P : Snapshot → Prop) {α : Type} (a : WG.M α)
    (ha : ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ discard a
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := discard_view_spec snapshot P a ha


macro "frame_same" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
  let wrap (term : Lean.Syntax) : Lean.TSyntax [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] :=
    ⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, term]⟩
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"frame_spec_{i}")
  let basics := #[``Leanux.branch, ``Leanux.branchCmp,
    ``Leanux.branchCmpExcluded, ``Leanux.unsupported, ``Leanux.invariant,
    ``Leanux.hidden, ``Leanux.hiddenU64, ``Leanux.hiddenClock,
    ``Leanux.hiddenClock64, ``Leanux.hiddenJiffies, ``Leanux.hiddenAlloc,
    ``Leanux.peekHiddenSite, ``Leanux.skipCut, ``Leanux.skipCutExactly,
    ``Leanux.getAmbient, ``Leanux.modifyAmbient, ``Leanux.getRouting,
    ``Leanux.refcountDecAndTest, ``Leanux.refcountInc,
    ``Leanux.refcountIncGuestWide, ``Leanux.refcountIncNotZero,
    ``Leanux.WG.AipNode.bitAt, ``Leanux.WG.choose,
    ``Leanux.WG.commonBits, ``Leanux.WG.prefixMatches,
    ``Leanux.WG.newTxSkb, ``Leanux.WG.getTxSkb,
    ``Leanux.WG.setTxSkb, ``Leanux.WG.freeTxSkb,
    ``Leanux.WG.newRxSkb, ``Leanux.WG.getRxSkb,
    ``Leanux.WG.setRxSkb, ``Leanux.WG.freeRxSkb,
    ``Leanux.WG.andM, ``Leanux.WG.orM]
  let lemmas := (fs.getElems.map fun f => wrap (if f.getId.toString.startsWith "_private." then
      (Lean.mkCIdent (normalizePinnedName f.getId)).raw else f.raw)) ++
    (basics.map fun n => wrap (Lean.mkIdent n).raw) ++ (names.map fun f => wrap f.raw)
  let mut body ← `(tactic|
    (have frame_modify := modifyDev_snapshot_spec (fun s => s = initial)
     have frame_list (α β : Type) := list_snapshot_spec (α := α) (β := β) (fun s => s = initial)
     have frame_map (α β : Type) := map_snapshot_spec (α := α) (β := β) (fun s => s = initial)
     have frame_discard (α : Type) := discard_snapshot_spec (α := α) (fun s => s = initial)
     have frame_ambient (α : Type) (a : AmbientM α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ :=
       hoare_liftAmbient a (fun w => snapshot w = initial)
     have frame_aip (α : Type) (a : AipM α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ := by
       apply hoare_liftAip a (fun w => snapshot w = initial)
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have frame_skb (α : Type) (a : SkbM α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ := by
       apply hoare_liftSkb a (fun w => snapshot w = initial)
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have frame_skb_explicit (α : Type) (a : SkbM α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ liftSkb a
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ := frame_skb α a
     have frame_index (α : Type) (a : IndexM α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ := by
       apply hoare_liftIndex a (fun w => snapshot w = initial)
       intro g d table hg hd
       simpa [snapshot, hd] using hg
     have frame_routing (α : Type) (a : Net.M α) :
         ⦃fun w => ⌜snapshot w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜snapshot w = initial⌝⦄ :=
       hoare_liftRouting a (fun w => snapshot w = initial) (fun _ _ hg => hg)
     mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
       -Std.Do.Spec.monadLift_StateT,
       frame_modify, frame_list, frame_map, frame_discard,
       frame_ambient, frame_aip, frame_skb, frame_skb_explicit, frame_index, frame_routing, $lemmas,*]
     all_goals try exact ((⇓? _ w => ⌜snapshot w = initial⌝) :
       PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
     all_goals try dsimp +zetaDelta only at *
     all_goals try simp_all [snapshot, cell, Option.bind_map, Function.comp_def]
     all_goals try trivial))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (apply sameSnapshot_of_wp; intro initial; $body))

theorem keypairGet_snapshot_spec (P : Snapshot → Prop) (kp : Option KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ keypairGet kp ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (keypairGet_sameSnapshot kp).wp P

theorem keypairPut_ordinary_spec (P : Snapshot → Prop) (hp : Stable P)
    (kp : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ keypairPut kp now ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (keypairPut_ordinary kp now).wp P hp

theorem keypairCreate_ordinary_spec (P : Snapshot → Prop) (hp : Stable P)
    (pid : Option PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ keypairCreate pid ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (keypairCreate_ordinary pid).wp P hp

theorem getKeypair_live_spec (P : Snapshot → Prop) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getKeypair i
    ⦃⇓? k w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ :=
  getKeypair_snapshot_wp i P

theorem setKeypair_live_spec (P : Snapshot → Prop) (i : Nat) (k : Keypair) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ setKeypair i k
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := setKeypair_snapshot_wp i k P

macro "frame_ordinary" "[" fs:ident,* "]" "using" "[" specs:ident,* "]"
    "ordinary" "[" ords:ident,* "]" : tactic => do
  let wrap (term : Lean.Syntax) : Lean.TSyntax [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] :=
    ⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, term]⟩
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"frame_spec_{i}")
  let ordnames := ords.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"frame_ord_{i}")
  let basics := #[``Leanux.branch, ``Leanux.branchCmp,
    ``Leanux.branchCmpExcluded, ``Leanux.unsupported, ``Leanux.invariant,
    ``Leanux.hidden, ``Leanux.hiddenU64, ``Leanux.hiddenClock,
    ``Leanux.hiddenClock64, ``Leanux.hiddenJiffies, ``Leanux.hiddenAlloc,
    ``Leanux.peekHiddenSite, ``Leanux.skipCut, ``Leanux.skipCutExactly,
    ``Leanux.getAmbient, ``Leanux.modifyAmbient, ``Leanux.getRouting,
    ``Leanux.refcountDecAndTest, ``Leanux.refcountInc,
    ``Leanux.refcountIncGuestWide, ``Leanux.refcountIncNotZero,
    ``Leanux.WG.AipNode.bitAt, ``Leanux.WG.choose,
    ``Leanux.WG.commonBits, ``Leanux.WG.prefixMatches,
    ``Leanux.WG.newTxSkb, ``Leanux.WG.getTxSkb,
    ``Leanux.WG.setTxSkb, ``Leanux.WG.freeTxSkb,
    ``Leanux.WG.newRxSkb, ``Leanux.WG.getRxSkb,
    ``Leanux.WG.setRxSkb, ``Leanux.WG.freeRxSkb,
    ``Leanux.WG.andM, ``Leanux.WG.orM]
  let lemmas := (fs.getElems.map fun f => wrap (if f.getId.toString.startsWith "_private." then
      (Lean.mkCIdent (normalizePinnedName f.getId)).raw else f.raw)) ++
    (basics.map fun n => wrap (Lean.mkIdent n).raw) ++
    ((names ++ ordnames).map fun f => wrap f.raw)
  let mut body ← `(tactic|
    (have frame_modify := modifyDev_snapshot_spec P
     have frame_list (α β : Type) := list_snapshot_spec (α := α) (β := β) P
     have frame_map (α β : Type) := map_snapshot_spec (α := α) (β := β) P
     have frame_discard (α : Type) := discard_snapshot_spec (α := α) P
     have frame_ambient (α : Type) (a : AmbientM α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
       hoare_liftAmbient a (fun w => P (snapshot w))
     have frame_aip (α : Type) (a : AipM α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
       apply hoare_liftAip a (fun w => P (snapshot w))
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have frame_skb (α : Type) (a : SkbM α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
       apply hoare_liftSkb a (fun w => P (snapshot w))
       intro g d store hg hd
       simpa [snapshot, hd] using hg
     have frame_skb_explicit (α : Type) (a : SkbM α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ liftSkb a
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := frame_skb α a
     have frame_index (α : Type) (a : IndexM α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
       apply hoare_liftIndex a (fun w => P (snapshot w))
       intro g d table hg hd
       simpa [snapshot, hd] using hg
     have frame_routing (α : Type) (a : Net.M α) :
         ⦃fun w => ⌜P (snapshot w)⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
       hoare_liftRouting a (fun w => P (snapshot w)) (fun _ _ hg => hg)
     mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list,
       -Std.Do.Spec.monadLift_StateT,
       frame_modify, frame_list, frame_map, frame_discard,
       frame_ambient, frame_aip, frame_skb, frame_skb_explicit, frame_index, frame_routing, $lemmas,*]
     all_goals try exact ((⇓? _ w => ⌜P (snapshot w)⌝) :
       PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
     all_goals try dsimp +zetaDelta only at *
     all_goals try simp_all [snapshot, cell, Option.bind_map, Function.comp_def]
     all_goals try trivial))
  for (name, spec) in (ordnames.zip ords.getElems).reverse do
    body ← `(tactic| (have $name := @$spec P hp; $body))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec P; $body))
  `(tactic| (apply (ordinaryAction_iff_wp _).mpr; intro P hp; $body))

end Leanux.Proofs.WG.Keypairs
