import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical

/-! Packet-store adapter cuts follow its read, component execution, and single write-back. The component has only Ambient state until the adapter installs its result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SkbAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def input (device : Device) : SkbStore :=
  {txSkbs:=device.txSkbs,rxSkbs:=device.rxSkbs,nextSkb:=device.nextSkb}

def finish (value : α) (store : SkbStore) : WG.M α := do
  modifyDev fun d=>{d with txSkbs:=store.txSkbs,rxSkbs:=store.rxSkbs,nextSkb:=store.nextSkb}
  pure value

def afterRead (action : SkbM α) (device : Device) : WG.M α := do
  let (value,store) ← action.run (input device)
  finish value store

theorem source (action : SkbM α) : liftSkb action=(getDev >>= afterRead action) := rfl

noncomputable def readShape : Access.Shape getDev := by
  simp only [getDev,invariant]
  repeat' access_source_step

inductive Point (action : SkbM α) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | read (point : Access.Point readShape w a v b) : Point action w a v b
  | component (device : w.dev=some d)
      (performed : (action.run (input d)).run a=.ok ((value,store),b)) : Point action w a w b
  | returned (performed : ((liftSkb action).run w).run a=.ok ((value,v),b)) : Point action w a v b

theorem Point.remaining (point : Point (α:=α) action w a v b) :
    ∃remaining : WG.M α,((liftSkb action).run w).run a=(remaining.run v).run b := by
  cases point with
  | read point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= afterRead action,by rw [source];simp only [StateT.run_bind,same]⟩
  | @component d a value store b w device performed=>
      refine ⟨finish value store,?_⟩
      rw [liftSkb_run,device]
      change Except.map _ ((action.run (input d)).run a)=_
      rw [performed]
      simp [finish,modifyDev,device,Except.map]
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point (α:=α) action w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E α,runPrefix (liftWGObserver (liftWGPrefix (liftSkb action))) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SkbAccess
