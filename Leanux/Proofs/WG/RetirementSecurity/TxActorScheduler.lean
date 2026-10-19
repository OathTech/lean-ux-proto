import Leanux.Proofs.WG.RetirementSecurity.TxActorDispatch

/-! Original scheduler composition with its real suspended records and
copied consistency trials. Iteration and NAPI contracts remain visible
native caller obligations, rather than an assumed initialized invariant. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem At.resume (before : At P crypt [] w) (act : Activation)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended.filter (· != act)} : Leanux.M Unit).run w=
      .ok ((),v)) : At P crypt (actor act).toList v := by
  have service:=TxWork.resume before.1 act run
  cases run
  exact ⟨service,before.2⟩

theorem resumed_service (iteration : IterationContract P crypt) (act : Activation) :
    Preserves (At P crypt []) (do
      modifyAmbient fun s=>{s with suspended:=s.suspended.filter (· != act)}
      Env.Activation.run act) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,resumed,activated⟩:=run
  cases result
  exact activation_service iteration (before.resume act resumed) activated

theorem resumed_bind (iteration : IterationContract P crypt) (act : Activation)
    (next : Unit→Leanux.M α) (after : ∀x,Preserves (At P crypt []) (next x)) :
    Preserves (At P crypt [])
      (modifyAmbient (fun s=>{s with suspended:=s.suspended.filter (· != act)}) >>=
        fun _=>Env.Activation.run act >>= next) := by
  simpa only [bind_assoc] using preserves_bind (resumed_service iteration act) after

theorem at_frame {action : Leanux.M α}
    (frame : SameView (fun w : World=>(w.wg,w.ambient.suspended)) action) :
    Preserves (At P crypt active) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact before.frame ((ProjectedAction.iff_run _ _ _).mp frame w result v run)

theorem at_world {action : Leanux.M α} (frame : SameView id action) :
    Preserves (At P crypt active) action := at_frame (frame.factor fun w=>(w.wg,w.ambient.suspended))

theorem scheduler_service
    (work : ∀pid,Preserves P (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}))
    (iteration : IterationContract P crypt)
    (napi : Preserves (At P crypt []) Env.napiSoftirq) (stack : Option Worker) :
    Preserves (At P crypt []) (Env.schedule stack) := by
  have dispatch (worker : Worker) : Preserves (At P crypt []) (Env.dispatch worker) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact dispatch_service work iteration before worker run
  have resume {α : Type} (act : Activation) (next : Unit→Leanux.M α)
      (after : ∀x,Preserves (At P crypt []) (next x)) :
      Preserves (At P crypt [])
        (modifyAmbient (fun s=>{s with suspended:=s.suspended.filter (· != act)}) >>=
          fun _=>Env.Activation.run act >>= next) := resumed_bind iteration act next after
  have device : Preserves (At P crypt []) (monadLift getDev : Leanux.M Device) := at_world TxActorFrames.device
  have ambient : Preserves (At P crypt []) (getAmbient : Leanux.M Ambient) :=
    at_frame (TxActorFrames.lift_ambient (action:=(get : AmbientM Ambient)) (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w result v run
      cases run
      rfl))
  have budget : Preserves (At P crypt []) (recordBudget : Leanux.M Nat) :=
    at_frame (TxActorFrames.lift_ambient TxActorFrames.budget)
  have peek : Preserves (At P crypt []) (peekHiddenSite : Leanux.M (Option Nat)) :=
    at_frame (TxActorFrames.lift_ambient TxActorFrames.peek_site)
  have hasWork (act : Activation) : Preserves (At P crypt []) (Env.Activation.hasWork act) :=
    at_world (TxActorFrames.has_work act)
  have filter (xs : List Activation) : Preserves (At P crypt []) (xs.filterM Env.Activation.consistent) :=
    at_world (filterM_sameKernel id _ TxActorFrames.consistent xs)
  have stopped {α : Type} (action : AmbientM α)
      (never : ∀w,∃stop,action.run w=.error stop) : Preserves (At P crypt []) (monadLift action : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    obtain ⟨stop,failed⟩:=never w.ambient
    change (liftAmbient action).run w=.ok (result,v) at run
    rw [liftAmbient_run,failed] at run
    cases run
  have invariant {α : Type} (message : String) : Preserves (At P crypt []) (Leanux.invariant message : Leanux.M α) :=
    stopped (AmbientM.invariant message) (fun _=>⟨_,rfl⟩)
  have unsupported {α : Type} (message : String) : Preserves (At P crypt []) (Leanux.unsupported message : Leanux.M α) :=
    stopped (AmbientM.unsupported message) (fun _=>⟨_,rfl⟩)
  have exhausted {α : Type} (message : String) : Preserves (At P crypt []) (budgetExhausted message : Leanux.M α) :=
    stopped (AmbientM.budgetExhausted message) (by
      intro w
      unfold AmbientM.budgetExhausted
      cases hidden:w.hidden <;> exact ⟨_,by simp [hidden,AmbientM.invariant,AmbientM.unsupported]; rfl⟩)
  routing_tx_source [Env.schedule] using
    [resume,dispatch,device,ambient,budget,peek,hasWork,filter,napi,invariant,unsupported,exhausted]

end Leanux.Proofs.WG.RetirementSecurity.TxWork
