import Leanux.Proofs.WG.Queues.RxPollStampSafety
import Leanux.Proofs.WG.Progress.RxPrimitiveSuffixSource
import Leanux.Proofs.WG.Queues.GroPreservation

/-! Record-suffix transport through exact original append-only observations. History safety is True; no fabricated journal is used to assert original execution. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem product_observed {E α : Type} (records : List HiddenRecord)
    (observed : PrefixM E α) (action : Leanux.M α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (keep : Preserves (fun w : World=>Tail records w.ambient.hidden) action) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) observed := by
  intro w h pre
  obtain ⟨suffix,append⟩:=appends w h
  refine ⟨suffix,append,True.intro,?_⟩
  cases run:(runPrefix observed w h).1 with
  | error e=>trivial
  | ok out=>
    exact (hoare_iff_run _ _ _).mp keep w out.1 out.2 pre
      ((erases w h).symm.trans run)

theorem observed_product {E α : Type} (records : List HiddenRecord)
    (observed : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observed action)
    (keep : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) observed) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v pre run
  obtain ⟨_,_,_,normal⟩:=keep w [] pre
  rw [erases w [],run] at normal
  exact normal

theorem joint_native_retains {α : Type} (records : List HiddenRecord)
    (g : MixedM α) (a : WG.M α) (erases : ErasesStatePrefix g a)
    (keep : NativeKeeps records a) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxJoint.access (liftWGObserver g)) :=
  product_observed records _ _ (RxJoint.access_appends _)
    (RxJoint.access_erases (liftWGObserver_erases erases)) (native_product records a keep)

theorem suffix_emitted {E : Type} (records : List HiddenRecord) (e : E) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (emitPrefix e) :=
  RxJoint.GroSource.emit_preserves (fun _ _ _=>True.intro) e (fun _ _ hi=>hi)

theorem suffix_receipt {E α : Type} (records : List HiddenRecord)
    (a : PrefixM E α) (event : RunWitness α→E)
    (keep : PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) a) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (receiptObserved a event) :=
  RxJoint.GroSource.receipt_preserves (fun _ _ _=>True.intro) a event keep
    (fun _ _ _ _ _ _ _ hi=>hi)

theorem product_lift_retains {E α : Type} (records : List HiddenRecord) (action : Leanux.M α)
    (keep : Preserves (fun w : World=>Tail records w.ambient.hidden) action) :
    PrefixPreserves (fun (_ : List E) w=>Tail records w.ambient.hidden) (fun _=>True)
      (liftPrefix action) :=
  product_observed records _ _ (Appends.lift _) (erasesPrefix_lift _) keep
end Leanux.Proofs.WG.Progress.RecordSuffix
