import Leanux.Proofs.WG.RetirementSecurity.TxActorAmbientFrames

/-! The original activation loop transfers TX service from its selected actor
to the actual suspended list at yield, and discharges it only on native end.
Its iteration contract remains explicit until the native worker callers are
joined; this is not an initialized scheduler assumption. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def At (P : WGWorld→Prop) (crypt : List (List SkbId)) (active : List PeerId) (w : World) : Prop :=
  Obligations crypt (active++actors w.ambient.suspended) w.wg ∧ P w.wg

theorem At.frame (before : At P crypt active w)
    (same : (v.wg,v.ambient.suspended)=(w.wg,w.ambient.suspended)) : At P crypt active v := by
  rcases Prod.mk.inj same with ⟨world,suspended⟩
  simpa only [At,world,suspended] using before

theorem At.suspend (before : At P crypt (actor act).toList w)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended++[{act with iterations:=act.iterations+1}]} :
      Leanux.M Unit).run w=.ok ((),v)) : At P crypt [] v := by
  have service:=TxWork.suspend before.1 run
  cases run
  exact ⟨service,before.2⟩

def IterationContract (P : WGWorld→Prop) (crypt : List (List SkbId)) : Prop :=
  ∀act w result v,At P crypt (actor act).toList w→
    (Env.Activation.iter act).run w=.ok (result,v)→
    At P crypt (if result=.ended then [] else (actor act).toList) v

def StepPost (P : WGWorld→Prop) (crypt : List (List SkbId))
    (step : ForInStep (Option Unit × Activation)) (w : World) : Prop :=
  match step with
  | .done state=>state.1=some () ∧ At P crypt [] w
  | .yield state=>state.1=none ∧ At P crypt (actor state.2).toList w

theorem body_service (iteration : IterationContract P crypt)
    (before : At P crypt (actor act).toList w)
    (run : (TxDisposition.DispatchCuts.body (none,act)).run w=.ok (step,v)) :
    StepPost P crypt step v := by
  unfold TxDisposition.DispatchCuts.body at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨result,u,iterated,tail⟩:=run
  have kept:=iteration act w result u before iterated
  cases result with
  | ended=>
    simp only [ite_true] at kept
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,t,closed,returned⟩:=tail
    cases returned
    exact ⟨rfl,kept.frame ((ProjectedAction.iff_run _ _ _).mp
      (TxActorFrames.hidden_product (.sectionStop act.worker)) u _ v closed)⟩
  | continued=>
    cases tail
    exact ⟨rfl,by simpa only [reduceCtorEq,ite_false,actor_increment] using kept⟩
  | yielded=>
    rw [MaterialOrigin.bind_ok] at tail
    obtain ⟨_,t,suspended,returned⟩:=tail
    cases returned
    exact ⟨rfl,(show At P crypt (actor act).toList u from kept).suspend suspended⟩

def LoopPost (P : WGWorld→Prop) (crypt : List (List SkbId))
    (state : Option Unit × Activation) (w : World) : Prop :=
  match state.1 with
  | some _=>At P crypt [] w
  | none=>At P crypt (actor state.2).toList w

theorem loop_service (iteration : IterationContract P crypt) (xs : List Nat)
    (before : At P crypt (actor act).toList w)
    (run : (forIn xs (none,act) (fun _ state=>TxDisposition.DispatchCuts.body state)).run w=
      .ok (state,v)) : LoopPost P crypt state v := by
  induction xs generalizing act w with
  | nil=>simp only [List.forIn_nil] at run; cases run; exact before
  | cons x xs ih=>
    rw [List.forIn_cons,MaterialOrigin.bind_ok] at run
    obtain ⟨step,u,body,tail⟩:=run
    have transferred:=body_service iteration before body
    cases step with
    | done next=>
      cases tail
      simp only [StepPost] at transferred
      simp only [LoopPost,transferred.1]
      exact transferred.2
    | yield next=>
      obtain ⟨marker,selected⟩:=next
      have empty:marker=none := transferred.1
      subst marker
      exact ih transferred.2 tail

theorem activation_service (iteration : IterationContract P crypt)
    (before : At P crypt (actor act).toList w)
    (run : (Env.Activation.run act).run w=.ok ((),v)) : At P crypt [] v := by
  rw [TxDisposition.DispatchCuts.run_factor] at run
  unfold TxDisposition.DispatchCuts.run at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨capacity,u,counted,run⟩:=run
  have same:u=w := (ProjectedAction.iff_run _ _ _).mp (TxActorFrames.occupancy act) w capacity u counted
  subst u
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨state,t,loop,tail⟩:=run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at loop
  have kept:=loop_service iteration _ before loop
  obtain ⟨marker,selected⟩:=state
  cases marker with
  | none=>cases tail
  | some value=>cases value; cases tail; exact kept

end Leanux.Proofs.WG.RetirementSecurity.TxWork
