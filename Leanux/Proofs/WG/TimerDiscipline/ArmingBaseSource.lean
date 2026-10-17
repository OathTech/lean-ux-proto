import Leanux.Proofs.WG.Noise.Execution
import Leanux.WG.Timers
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original flat state/error map rule, still including product computations. -/
theorem map_result_spec {σ α β : Type} (f : α → β) (a : StateT σ (Except Stop) α)
    (P : σ → Prop) (Q : α → σ → Prop)
    (ha : ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? x w => ⌜Q x w⌝⦄) :
    ⦃fun w => ⌜P w⌝⦄ StateT.map f a
    ⦃⇓? b w => ⌜∃ x, b = f x ∧ Q x w⌝⦄ := by
  apply (Noise.Product.ensures_iff _ _ _).mp
  intro w b w' hp hr
  change (a.run w >>= fun out => pure (f out.1, out.2)) = .ok (b, w') at hr
  cases he : a.run w with
  | error e => rw [he] at hr; cases hr
  | ok out =>
    rcases out with ⟨x, t⟩
    simp [he] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ⟨x, rfl, (Noise.Product.ensures_iff _ _ _).mpr ha w x t hp he⟩

/-- Native companion: the outer state is observed and Ambient stays quantified. -/
theorem map_result_native_spec {σ α β : Type} (f : α → β) (a : StateT σ AmbientM α)
    (P : σ → Prop) (Q : α → σ → Prop)
    (ha : ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? x w => ⌜Q x w⌝⦄) :
    ⦃fun w => ⌜P w⌝⦄ StateT.map f a
    ⦃⇓? b w => ⌜∃ x, b = f x ∧ Q x w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result g' ambient' hp hr
  change ((a.run g).run ambient >>= fun ((x, t), after) =>
    Except.ok ((f x, t), after)) = .ok ((result, g'), ambient') at hr
  cases he : (a.run g).run ambient with
  | error e => rw [he] at hr; cases hr
  | ok out =>
    rcases out with ⟨⟨x, t⟩, after⟩
    simp [he] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨x, rfl, (ensures_iff _ _ _).mpr ha g ambient x t after hp he⟩

theorem modPeerTimerGuard_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimerGuard pid) (fun g => g.dev = some d)
      (fun ok g => ok = (d.running && !p.isDead) ∧ g.dev = some d) := by
  intro g ambient result g' ambient' device run
  cases running : d.running <;> cases dead : p.isDead
  all_goals simp [modPeerTimerGuard, Leanux.WG.andM, branch, AmbientM.branch,
    getDev, getPeer, device, resident, running, dead] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, device⟩

end Leanux.Proofs.WG.TimerDiscipline
