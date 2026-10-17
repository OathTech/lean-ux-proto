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

theorem sameSnapshot_of_sameWGStore
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => snapshot (project s)) a :=
  h.of_factor snapshotOfWGStoreView (fun s => snapshot (project s)) (fun _ => rfl)

theorem modifyDev_snapshot_spec (P : Snapshot → Prop) (f : Device → Device)
    (hf : ∀ d, (f d).keypairs = d.keypairs) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [snapshot, modifyDev, Option.bind_map, Function.comp_def, hf] using hp

theorem list_snapshot_spec (P : Snapshot → Prop)
    {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {α β : Type}
    (xs : List α) (init : β) (f : α → β → StateT S m (ForInStep β))
    (hf : ∀ x b, ⦃fun w => ⌜P (project w)⌝⦄ f x b
      ⦃⇓? _ w => ⌜P (project w)⌝⦄) :
    ⦃fun w => ⌜P (project w)⌝⦄ forIn xs init f
    ⦃⇓? _ w => ⌜P (project w)⌝⦄ :=
  list_view_spec project P xs init f hf

theorem map_snapshot_spec (P : Snapshot → Prop)
    {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {α β : Type}
    (f : α → β) (a : StateT S m α)
    (ha : ⦃fun w => ⌜P (project w)⌝⦄ a ⦃⇓? _ w => ⌜P (project w)⌝⦄) :
    ⦃fun w => ⌜P (project w)⌝⦄ StateT.map f a
    ⦃⇓? _ w => ⌜P (project w)⌝⦄ :=
  map_view_spec project P f a ha

theorem discard_snapshot_spec (P : Snapshot → Prop)
    {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {α : Type} (a : StateT S m α)
    (ha : ⦃fun w => ⌜P (project w)⌝⦄ a ⦃⇓? _ w => ⌜P (project w)⌝⦄) :
    ⦃fun w => ⌜P (project w)⌝⦄ discard a
    ⦃⇓? _ w => ⌜P (project w)⌝⦄ := discard_view_spec project P a ha


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

end Leanux.Proofs.WG.Keypairs
