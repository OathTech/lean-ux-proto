import Leanux.Proofs.Framing.Lift

/-! Transport predicates on the actual Ambient state through nested state
computations. The subsystem premises include their real ambient endpoints. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.AmbientRetention
open Leanux Leanux.Proofs.Framing

theorem stateT_bind {σ α β : Type} (P : Ambient → Prop)
    (action : StateT σ AmbientM α) (next : α → StateT σ AmbientM β)
    (first : ∀ state, Preserves P (action.run state))
    (rest : ∀ value state, Preserves P ((next value).run state)) :
    ∀ state, Preserves P ((action >>= next).run state) := by
  intro state
  rw [StateT.run_bind]
  exact preserves_bind (first state) (fun out => rest out.1 out.2)

theorem stateT_lift {σ α : Type} (P : Ambient → Prop) (action : AmbientM α)
    (keeps : Preserves P action) :
    ∀ state, Preserves P ((StateT.lift action : StateT σ AmbientM α).run state) := by
  intro state
  change Preserves P (action >>= fun value => pure (value,state))
  exact preserves_bind keeps (fun _ => preserves_pure _)

theorem liftFS {α : Type} (P : Ambient → Prop) (action : FS.M α)
    (keeps : ∀ fs tasks, Preserves P ((action.run fs).run tasks)) :
    Preserves (fun w : World => P w.ambient) (Leanux.liftFS action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  rw [liftFS_run] at run
  cases inner : ((action.run before.fs).run before.tasks).run before.ambient with
  | error stop => simp only [inner,Except.map] at run; cases run
  | ok out =>
    obtain ⟨⟨⟨result,fs⟩,tasks⟩,ambient⟩ := out
    simp only [inner,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact (hoare_iff_run _ _ _).mp (keeps before.fs before.tasks)
      before.ambient ((result,fs),tasks) ambient pre inner

theorem liftSeccomp {α : Type} (P : Ambient → Prop) (action : Seccomp.M α)
    (keeps : ∀ seccomp tasks, Preserves P ((action.run seccomp).run tasks)) :
    Preserves (fun w : World => P w.ambient) (Leanux.liftSeccomp action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  rw [liftSeccomp_run] at run
  cases inner : ((action.run before.seccomp).run before.tasks).run before.ambient with
  | error stop => simp only [inner,Except.map] at run; cases run
  | ok out =>
    obtain ⟨⟨⟨result,seccomp⟩,tasks⟩,ambient⟩ := out
    simp only [inner,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact (hoare_iff_run _ _ _).mp (keeps before.seccomp before.tasks)
      before.ambient ((result,seccomp),tasks) ambient pre inner

end Leanux.Proofs.WG.Progress.AmbientRetention
