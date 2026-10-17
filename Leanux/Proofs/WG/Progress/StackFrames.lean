import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Std.Do

theorem hasWork_world (a : Activation) (initial : World) :
    Product.Ensures (Activation.hasWork a) (fun w => w = initial) (fun _ w => w = initial) := by
  have hdev : Product.Ensures (liftWG getDev) (fun w => w = initial)
      (fun _ w => w = initial) := by
    intro w value final pre run
    subst w
    change ((getDev.run initial.wg).run initial.ambient >>= fun ((x, g), ambient) =>
      Except.ok (x, {initial with wg := g, ambient})) = _ at run
    cases hd : initial.wg.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨rfl, rfl⟩; rfl
  have hpeer (pid : PeerId) : Product.Ensures (liftWG (getPeer pid))
      (fun w => w = initial) (fun _ w => w = initial) := by
    intro w value final pre run
    subst w
    change (((getPeer pid).run initial.wg).run initial.ambient >>= fun ((x, g), ambient) =>
      Except.ok (x, {initial with wg := g, ambient})) = _ at run
    cases hd : initial.wg.dev with
    | none => simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      cases hp : d.peers[pid]? with
      | none => simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at run; cases run
      | some p => simp [getPeer, getDev, hd, hp] at run; rcases run with ⟨rfl, rfl⟩; rfl
  have hskb (id : SkbId) : Product.Ensures (liftWG (getTxSkb id))
      (fun w => w = initial) (fun _ w => w = initial) := by
    intro w value final pre run
    subst w
    change (((getTxSkb id).run initial.wg).run initial.ambient >>= fun ((x, g), ambient) =>
      Except.ok (x, {initial with wg := g, ambient})) = _ at run
    cases hd : initial.wg.dev with
    | none => simp [getTxSkb, liftSkb, getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      cases hp : d.txSkbs[id]? with
      | none =>
        simp [getTxSkb, liftSkb, getDev, hd, SkbStore.getTx, hp, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        simp [getTxSkb, liftSkb, getDev, hd, SkbStore.getTx, hp, modifyDev] at run
        rcases run with ⟨rfl, rfl⟩
        have same : {initial.wg with dev := some d} = initial.wg := by rw [← hd]
        change {initial with wg := {initial.wg with dev := some d}} = initial
        rw [same]
  have hpure (value : Bool) : Product.Ensures (pure value : Leanux.M Bool)
      (fun w => w = initial) (fun _ w => w = initial) := by
    intro w value final pre run
    cases run
    exact pre
  have hfail (message : String) : Product.Ensures (invariant message : Leanux.M Bool)
      (fun w => w = initial) (fun _ w => w = initial) := by
    intro w value final _ run
    cases run
  unfold Activation.hasWork
  refine Product.ensures_bind _ _ hdev ?_
  intro d
  cases a.worker
  all_goals try exact hpure _
  all_goals try exact hfail _
  cases a.pid with
  | none => exact hfail _
  | some pid =>
    refine Product.ensures_bind _ _ (hpeer pid) ?_
    intro p
    cases p.txQueue.all.head? with
    | none => exact hpure false
    | some item =>
      dsimp only
      cases item.head? with
      | none => exact hfail _
      | some id => exact Product.ensures_bind _ _ (hskb id) (fun _ => hpure _)

end Leanux.Proofs.WG.Progress
