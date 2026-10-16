import Leanux.Proofs.Framing.Hoare
import Leanux.WG.State

/-! The actual subsystem adapters, including their ambient results and exact
Stops. Structural separation is established once here, not once per leaf. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do

theorem liftAmbient_run (a : AmbientM α) (w : World) :
    (liftAmbient a).run w = (a.run w.ambient).map (fun (x, ambient) => (x, {w with ambient})) := by
  change (a.run w.ambient >>= fun (x, ambient) =>
    Except.ok (x, {w with ambient})) = _
  cases a.run w.ambient <;> rfl

theorem liftWG_run (a : WG.M α) (w : World) :
    (liftWG a).run w = ((a.run w.wg).run w.ambient).map
      (fun ((x, wg), ambient) => (x, {w with wg, ambient})) := by
  unfold liftWG StateT.run
  cases a w.wg w.ambient <;> rfl

theorem liftTask_run (a : TaskM α) (w : World) :
    (liftTask a).run w = ((a.run w.tasks).run w.ambient).map
      (fun ((x, tasks), ambient) => (x, {w with tasks, ambient})) := by
  unfold liftTask StateT.run
  cases a w.tasks w.ambient <;> rfl

theorem liftFS_run (a : FS.M α) (w : World) :
    (liftFS a).run w = (((a.run w.fs).run w.tasks).run w.ambient).map
      (fun (((x, fs), tasks), ambient) => (x, {w with fs, tasks, ambient})) := by
  unfold liftFS StateT.run
  cases a w.fs w.tasks w.ambient <;> rfl

theorem liftSeccomp_run (a : Seccomp.M α) (w : World) :
    (liftSeccomp a).run w = (((a.run w.seccomp).run w.tasks).run w.ambient).map
      (fun (((x, seccomp), tasks), ambient) => (x, {w with seccomp, tasks, ambient})) := by
  unfold liftSeccomp StateT.run
  cases a w.seccomp w.tasks w.ambient <;> rfl

theorem stateLiftAmbient_run (a : AmbientM α) (s : σ) (ambient : Ambient) :
    (((StateT.lift a : StateT σ AmbientM α).run s).run ambient) =
      (a.run ambient).map (fun (x, ambient') => ((x, s), ambient')) := by
  unfold StateT.run StateT.lift
  change (a ambient >>= fun (x, b) => Except.ok ((x, s), b)) = _
  cases a ambient <;> rfl

theorem hoare_liftAmbient (a : AmbientM α) (P : σ → Prop) :
    Hoare (StateT.lift a : StateT σ AmbientM α) P (fun _ => P) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro s ambient x s' ambient' hp hr
  rw [stateLiftAmbient_run] at hr
  cases ha : a.run ambient with
  | error e => simp [ha, Except.map] at hr
  | ok out =>
    rcases out with ⟨y, b⟩
    simp [ha, Except.map] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp

/-- The index adapter retains its device guard, performs the actual table
computation, and writes back only the table. Ambient failures have no endpoint. -/
theorem liftIndex_run (a : WG.IndexM α) (g : WGWorld) (ambient : Ambient) :
    ((WG.liftIndex a).run g).run ambient =
      match g.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => ((a.run d.indexTable).run ambient).map
          (fun ((x, table), ambient') =>
            ((x, {g with dev := some {d with indexTable := table}}), ambient')) := by
  cases hd : g.dev with
  | none =>
    simp [WG.liftIndex, WG.getDev, hd, invariant, AmbientM.invariant]
    rfl
  | some d =>
    simp only [WG.liftIndex, WG.getDev, hd, StateT.run_bind, StateT.run_pure,
      StateT.run_lift]
    cases ha : (a.run d.indexTable).run ambient <;>
      simp [WG.modifyDev, hd, ha] <;> rfl

/-- A local index action preserves any outer predicate stable under replacing
only the device's index table. Its ambient input and output stay unrestricted. -/
theorem hoare_liftIndex (a : WG.IndexM α) (P : WGWorld → Prop)
    (stable : ∀ g d table, P g → g.dev = some d →
      P {g with dev := some {d with indexTable := table}}) :
    Hoare (WG.liftIndex a) P (fun _ => P) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient x g' ambient' hp hr
  rw [liftIndex_run] at hr
  cases hd : g.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd] at hr
    cases ha : (a.run d.indexTable).run ambient with
    | error e => simp [ha, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨y, table⟩, b⟩
      simp [ha, Except.map] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact stable g d table hp hd

end Leanux.Proofs.Framing
