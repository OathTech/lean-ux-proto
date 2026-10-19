import Leanux.Proofs.WG.RetirementSecurity.TxActorDeferredWorkers

/-! Source metadata frames for the service carrier retain the actual
suspended records as well as the WG store. A product-store frame alone is
not sufficient for this carrier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem At.store (before : At (Covered locals crypt) crypt active w)
    (same : wgStoreView v.wg=wgStoreView w.wg)
    (suspended : v.ambient.suspended=w.ambient.suspended) : At (Covered locals crypt) crypt active v := by
  have kept:=serving_store_transport same before
  simpa only [At,Serving,suspended] using kept

theorem actor_store {action : Leanux.M α}
    (frame : SameView (fun w:World=>(wgStoreView w.wg,w.ambient.suspended)) action) :
    Preserves (At (Covered locals crypt) crypt active) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have same:=(ProjectedAction.iff_run _ _ _).mp frame w result v run
  exact before.store (congrArg Prod.fst same) (congrArg Prod.snd same)

theorem actor_product_store {action : Leanux.M α} (store : SameProductStore action)
    (suspension : SameView TxSuspension.suspended action) :
    Preserves (At (Covered locals crypt) crypt active) action := by
  apply actor_store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  exact Prod.ext (congrArg (fun s:ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp store w result v run))
    ((ProjectedAction.iff_run _ _ _).mp suspension w result v run)

theorem actor_wg_modify (f : WGWorld→WGWorld) (same : ∀w,wgStoreView (f w)=wgStoreView w) :
    Preserves (At (Covered locals crypt) crypt active) (modifyWG f : Leanux.M Unit) := by
  apply actor_store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  exact Prod.ext (same w.wg) rfl

theorem actor_env_modify (f : EnvWorld→EnvWorld) : Preserves (At P crypt active) (modifyEnv f) := by
  apply at_frame
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem actor_ambient_modify (f : Ambient→Ambient) (same : ∀a,(f a).suspended=a.suspended) :
    Preserves (At P crypt active) (modifyAmbient f : Leanux.M Unit) := by
  apply at_frame
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  exact Prod.ext rfl (same w.ambient)

theorem actor_ambient {action : AmbientM α} (same : SameView Ambient.suspended action) :
    Preserves (At P crypt active) (liftAmbient action) := at_frame (TxActorFrames.lift_ambient same)

theorem actor_invariant (why : String) : Preserves (At P crypt active) (Leanux.invariant why : Leanux.M α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

theorem actor_unsupported (why : String) : Preserves (At P crypt active) (Leanux.unsupported why : Leanux.M α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

theorem actor_exhausted (why : String) : Preserves (At P crypt active) (budgetExhausted why : Leanux.M α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  unfold budgetExhausted at run
  change (liftAmbient (AmbientM.budgetExhausted why)).run w=.ok (result,v) at run
  rw [liftAmbient_run] at run
  have failed:∃stop,(AmbientM.budgetExhausted why : AmbientM α).run w.ambient=.error stop := by
    unfold AmbientM.budgetExhausted
    cases hidden:w.ambient.hidden <;> exact ⟨_,by simp [hidden,AmbientM.invariant,AmbientM.unsupported]; rfl⟩
  obtain ⟨stop,failed⟩:=failed
  rw [failed] at run
  cases run


macro "actor_neutral_step" : tactic => `(tactic| first
  | (rx_retention_head getWG; apply at_world; apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl)
  | (rx_retention_head getEnv; apply at_world; apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl)
  | (rx_retention_head getAmbient; apply at_world; apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl)
  | (rx_retention_head modifyWG; apply actor_wg_modify; intro w; rfl)
  | (rx_retention_head modifyEnv; exact actor_env_modify _)
  | (rx_retention_head modifyAmbient; apply actor_ambient_modify; intro a; rfl)
  | (rx_retention_head Leanux.hidden; exact actor_ambient (TxActorFrames.hidden _))
  | (rx_retention_head recordBudget; exact actor_ambient TxActorFrames.budget)
  | (rx_retention_head peekHiddenSite; exact actor_ambient TxActorFrames.peek_site)
  | (rx_retention_head peekUnit; exact actor_ambient (TxActorFrames.peek_unit _))
  | (rx_retention_head resolveUnit; exact actor_ambient (TxActorFrames.resolve _ _ _))
  | (rx_retention_head invariant; exact actor_invariant _)
  | (rx_retention_head unsupported; exact actor_unsupported _)
  | (rx_retention_head budgetExhausted; exact actor_exhausted _)
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from WG.M; first
      | exact at_world TxActorFrames.device
      | exact at_world (TxActorFrames.peer _))
  | (rx_retention_head ForIn.forIn
     first
     | (apply list_view_spec id _; intro item state; change Preserves _ _)
     | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | rxstack_preserves_join
  | rx_retention_step)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
