import Leanux.Proofs.WG.Roaming.RemoteChronologyJournalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E F State α : Type}

theorem focused_retained
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (inert : ∀ event pid, effect (encode event) pid = none)
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (retained : ∀ w value final, action.run w = .ok (value,final) →
      RemoteRetained (before w) (after value final)) :
    PrefixEnsures (fun h w => Inv effect entry valid h (before w))
      (RemoteHistoryValid valid) (focusPrefix encode decode observed)
      (fun value h final => Inv effect entry valid h (after value final)) := by
  apply focused_retained_inert effect entry valid encode decode encoded before after
    observed action ?_ appends erases retained
  intro w h pid
  have all : (fun f : F => effect (encode f) pid) = (fun _ => none) :=
    funext (fun f => inert f pid)
  rw [all]
  exact (List.filterMap_eq_nil_iff.mpr (by intro f _; rfl)).trans
    (List.filterMap_eq_nil_iff.mpr (by intro f _; rfl)).symm

theorem focused_receipt
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (inert : ∀ event pid, effect (encode event) pid = none)
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (receiptEvent : StateRunWitness State α → E)
    (checked : ∀ r, r.Valid action → valid (receiptEvent r))
    (changed : ∀ r, r.Valid action →
      RemoteRetained (applyEffect effect (receiptEvent r) (before r.before)) (after r.value r.after)) :
    PrefixEnsures (fun h w => Inv effect entry valid h (before w))
      (RemoteHistoryValid valid) (receiptObserved (focusPrefix encode decode observed) receiptEvent)
      (fun value h final => Inv effect entry valid h (after value final)) := by
  apply focused_receipt_inert effect entry valid encode decode encoded before after
    observed action ?_ appends erases receiptEvent checked changed
  intro w h pid
  have all : (fun f : F => effect (encode f) pid) = (fun _ => none) :=
    funext (fun f => inert f pid)
  rw [all]
  exact (List.filterMap_eq_nil_iff.mpr (by intro f _; rfl)).trans
    (List.filterMap_eq_nil_iff.mpr (by intro f _; rfl)).symm

theorem native_focused_retained
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (inert : ∀ event pid, effect (encode event) pid = none)
    (view : WGWorld → RemoteMap) (observed : WGPrefix F α) (action : WG.M α)
    (appends : StateAppends observed) (erases : ErasesStatePrefix observed action)
    (retained : ∀ g a value final b, (action.run g).run a = .ok ((value,final),b) →
      RemoteRetained (view g) (view final)) :
    StatePrefixPreserves (fun h g _ => Inv effect entry valid h (view g))
      (RemoteHistoryValid valid) (focusStatePrefix encode decode observed) :=
  fun g => focused_retained effect entry valid encode decode encoded inert
    (fun _ => view g) (fun (out : α × WGWorld) (_ : Ambient) => view out.2)
    (observed.run g) (action.run g) (appends g) (erases g)
    (fun a out b run => retained g a out.1 out.2 b run)

end Leanux.Proofs.WG.Roaming.RemoteChronology
