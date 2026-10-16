import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Lift
import Leanux.Proofs.Framing.Tools

/-! Pure observations of the original 43 store fields and the incoming 47
fields. These are projections of the actual product, never execution states.
The original observation excludes file-layer user outputs and the four later
routing/timer fields; the larger observation factors onto it. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do Leanux.Proofs.WG.Lifetimes

def fsStoreView (s : FSWorld) : FSWorld := {s with userOut := none, userFds := none}

abbrev ProductStore43 :=
  FSWorld × TaskWorld × (Std.TreeMap FilterId SeccompFilter × FilterId) × WGStoreView

abbrev ProductOwned47 :=
  FSWorld × TaskWorld × (Std.TreeMap FilterId SeccompFilter × FilterId) × WGOwnedView

def productStoreView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), wgStoreView w.wg)

def productOwnedView (w : World) : ProductOwned47 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), wgOwnedView w.wg)

def productOwnedStore (v : ProductOwned47) : ProductStore43 :=
  (v.1, v.2.1, v.2.2.1, v.2.2.2.toWGStoreView)

theorem productStoreView_factor (w : World) :
    productStoreView w = productOwnedStore (productOwnedView w) := rfl

abbrev SameProductStore (a : Leanux.M α) := SameView productStoreView a
abbrev SameProductOwned (a : Leanux.M α) := SameView productOwnedView a

theorem SameProductOwned.store (h : SameProductOwned a) : SameProductStore a :=
  h.of_factor productOwnedStore productStoreView productStoreView_factor

/-- The product adapter preserves any predicate stable under replacing only
the actual Ambient component, including on every possible successful result. -/
theorem productAmbient_spec (a : AmbientM α) (P : World → Prop)
    (stable : ∀ w ambient, P w → P {w with ambient}) :
    Hoare (MonadLift.monadLift a : Leanux.M α) P (fun _ => P) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' hp hr
  change (liftAmbient a).run w = .ok (x, w') at hr
  rw [liftAmbient_run] at hr
  cases he : a.run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨y, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact stable w ambient hp

/-- A native WG observation transports through the actual product adapter.
The premise states exactly how the chosen product observation factors. -/
theorem sameView_liftWG (view : World → σ) (native : WGWorld → τ)
    (a : WG.M α) (h : SameView native a)
    (factor : ∀ w g ambient, native g = native w.wg →
      view {w with wg := g, ambient} = view w) :
    SameView view (MonadLift.monadLift a : Leanux.M α) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  change (liftWG a).run w = .ok (x, w') at hr
  rw [liftWG_run] at hr
  cases he : (a.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact factor w g ambient ((ProjectedAction.iff_run_ambient _ _ _).mp h _ _ _ _ _ he)

theorem liftWG_sameProductStore (a : WG.M α) (h : SameWGStore a) :
    SameProductStore (MonadLift.monadLift a : Leanux.M α) := by
  apply sameView_liftWG productStoreView wgStoreView a h
  intro w g ambient hg
  simp only [productStoreView, hg]

/-- Routing is outside the original seven WG store observations. The adapter
still executes the actual routing action with its device inputs and Stops. -/
theorem liftRouting_sameWGStore (a : Net.M α) :
    SameWGStore (MonadLift.monadLift a : WG.M α) := by
  intro initial
  apply hoare_liftRouting a (fun g => wgStoreView g = initial)
  intro g routing hg
  exact hg

theorem productRouting_spec (a : Net.M α) (P : ProductStore43 → Prop) :
    Hoare (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α)
      (fun w => P (productStoreView w)) (fun _ w => P (productStoreView w)) :=
  (liftWG_sameProductStore (liftRouting a) (liftRouting_sameWGStore a)).wp P

theorem productGetWG_spec (P : ProductStore43 → Prop) :
    Hoare (getWG : Leanux.M WGWorld)
      (fun w => P (productStoreView w)) (fun _ w => P (productStoreView w)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' hp hr
  cases hr
  exact hp

/-- The guarded native getter retains the full store observation through its
actual product lift; the missing-device outcome remains a Stop. -/
theorem productGetDev_spec (P : ProductStore43 → Prop) :
    Hoare (MonadLift.monadLift WG.getDev : Leanux.M WG.Device)
      (fun w => P (productStoreView w)) (fun _ w => P (productStoreView w)) := by
  have h : SameWGStore WG.getDev := by
    intro initial
    unfold Hoare
    mvcgen [WG.getDev, invariant, AmbientM.invariant]
  exact (liftWG_sameProductStore WG.getDev h).wp P

theorem productModifyWG_spec (P : ProductStore43 → Prop) (f : WGWorld → WGWorld)
    (hf : ∀ g, wgStoreView (f g) = wgStoreView g) :
    Hoare (modifyWG f : Leanux.M Unit)
      (fun w => P (productStoreView w)) (fun _ w => P (productStoreView w)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' hp hr
  cases hr
  simpa only [productStoreView, hf] using hp

/-- The task adapter changes the shared task store and Ambient only.
Predicates about other product components transfer through this one rule. -/
theorem productTask_spec (a : TaskM α) (P : World → Prop)
    (stable : ∀ w tasks ambient, P w → P {w with tasks, ambient}) :
    Hoare (MonadLift.monadLift a : Leanux.M α) P (fun _ => P) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' hp hr
  change (liftTask a).run w = .ok (x, w') at hr
  rw [liftTask_run] at hr
  cases he : (a.run w.tasks).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨y, tasks⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact stable w tasks ambient hp

/-- The file adapter changes only its own store, tasks and Ambient.
A stable product predicate needs no per-operation filesystem frame. -/
theorem productFS_spec (a : FS.M α) (P : World → Prop)
    (stable : ∀ w fs tasks ambient, P w → P {w with fs, tasks, ambient}) :
    Hoare (MonadLift.monadLift a : Leanux.M α) P (fun _ => P) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' hp hr
  change (liftFS a).run w = .ok (x, w') at hr
  rw [liftFS_run] at hr
  cases he : ((a.run w.fs).run w.tasks).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨⟨y, fs⟩, tasks⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact stable w fs tasks ambient hp


end Leanux.Proofs.Framing
