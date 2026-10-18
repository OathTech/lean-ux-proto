import Leanux.Proofs.WG.Roaming.RemoteOriginModel
import Leanux.Proofs.Logged.NativeCapture

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E F State α : Type}

def Inv (entry : RemoteMap) (cause : E → PeerId → Nat × Nat × Nat × Nat → Prop)
    (valid : E → Prop) (history : List E) (current : RemoteMap) : Prop :=
  RemoteCovered entry cause history current ∧ RemoteHistoryValid valid history

theorem focused_retained
    (entry : RemoteMap) (cause : E → PeerId → Nat × Nat × Nat × Nat → Prop)
    (valid : E → Prop) (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (retained : ∀ w value final, action.run w = .ok (value,final) →
      RemoteRetained (before w) (after value final)) :
    PrefixEnsures (fun h w => Inv entry cause valid h (before w))
      (RemoteHistoryValid valid) (focusPrefix encode decode observed)
      (fun value h final => Inv entry cause valid h (after value final)) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap decode)
  have actual := focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl appended)
  have safe : RemoteHistoryValid valid (h ++ suffix.map encode) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact encoded original
  rw [actual]
  refine ⟨suffix.map encode,rfl,safe,?_⟩
  cases execution : (runPrefix observed w (h.filterMap decode)).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,final⟩ := out
    have run := (erases w (h.filterMap decode)).symm.trans execution
    exact ⟨(prior.1.retained (retained w value final run)).append_history,safe⟩

theorem focused_receipt
    (entry : RemoteMap) (cause : E → PeerId → Nat × Nat × Nat × Nat → Prop)
    (valid : E → Prop) (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (receipt : StateRunWitness State α → E)
    (checked : ∀ r, r.Valid action → valid (receipt r))
    (effect : ∀ r, r.Valid action → ∀ pid remote, after r.value r.after pid = some remote →
      before r.before pid = some remote ∨ cause (receipt r) pid remote) :
    PrefixEnsures (fun h w => Inv entry cause valid h (before w))
      (RemoteHistoryValid valid) (receiptObserved (focusPrefix encode decode observed) receipt)
      (fun value h final => Inv entry cause valid h (after value final)) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap decode)
  have actual := focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl appended)
  have safe : RemoteHistoryValid valid (h ++ suffix.map encode) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact encoded original
  rw [runPrefix_receiptObserved,actual]
  cases execution : (runPrefix observed w (h.filterMap decode)).1 with
  | error stop =>
    simp only [execution]
    exact ⟨suffix.map encode,rfl,safe,True.intro⟩
  | ok out =>
    obtain ⟨value,final⟩ := out
    simp only [execution]
    have run : (⟨value,w,final⟩ : StateRunWitness State α).Valid action :=
      (erases w (h.filterMap decode)).symm.trans execution
    refine ⟨suffix.map encode ++ [receipt ⟨value,w,final⟩],?_,
      safe.snoc (checked _ run),?_⟩
    · exact List.append_assoc _ _ _
    · exact ⟨prior.1.append_history.receipt _ (effect _ run),safe.snoc (checked _ run)⟩

theorem native_focused_retained
    (entry : RemoteMap) (cause : E → PeerId → Nat × Nat × Nat × Nat → Prop)
    (valid : E → Prop) (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event)) (view : WGWorld → RemoteMap)
    (observed : WGPrefix F α) (action : WG.M α)
    (appends : StateAppends observed) (erases : ErasesStatePrefix observed action)
    (retained : ∀ g a value final b, (action.run g).run a = .ok ((value,final),b) →
      RemoteRetained (view g) (view final)) :
    StatePrefixPreserves (fun h g _ => Inv entry cause valid h (view g))
      (RemoteHistoryValid valid) (focusStatePrefix encode decode observed) :=
  fun g => focused_retained entry cause valid encode decode encoded
    (fun _ => view g) (fun (out : α × WGWorld) (_ : Ambient) => view out.2) (observed.run g) (action.run g)
    (appends g) (erases g)
    (fun a out b run => retained g a out.1 out.2 b run)

theorem native_focused_receipt
    (entry : RemoteMap) (cause : E → PeerId → Nat × Nat × Nat × Nat → Prop)
    (valid : E → Prop) (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event)) (view : WGWorld → RemoteMap)
    (observed : WGPrefix F α) (action : WG.M α)
    (appends : StateAppends observed) (erases : ErasesStatePrefix observed action)
    (receipt : WGRunWitness α → E)
    (checked : ∀ r, r.Valid action → valid (receipt r))
    (effect : ∀ r, r.Valid action → ∀ pid remote, view r.after pid = some remote →
      view r.before pid = some remote ∨ cause (receipt r) pid remote) :
    StatePrefixPreserves (fun h g _ => Inv entry cause valid h (view g))
      (RemoteHistoryValid valid)
      (receiptWGObserved (focusStatePrefix encode decode observed) receipt) := by
  intro g a h prior
  let wrap : StateRunWitness Ambient (α × WGWorld) → E :=
    fun r => receipt ⟨r.value.1,g,r.value.2,r.before,r.after⟩
  have actual : runPrefix
      ((receiptWGObserved (focusStatePrefix encode decode observed) receipt).run g) a h =
      runPrefix (receiptObserved (focusPrefix encode decode (observed.run g)) wrap) a h := by
    have concrete := runWGPrefix_receiptWGObserved
      (focusStatePrefix encode decode observed) receipt g a h
    change runPrefix ((receiptWGObserved (focusStatePrefix encode decode observed) receipt).run g) a h = _ at concrete
    rw [concrete,runPrefix_receiptObserved]
    simp only [runWGPrefix,runStatePrefix,StateT.run,focusStatePrefix]
    cases runPrefix (focusPrefix encode decode (observed g)) a h with
    | mk result history =>
      cases result with
      | error stop => rfl
      | ok out => obtain ⟨⟨value,final⟩,after⟩ := out; rfl
  rw [actual]
  exact focused_receipt entry cause valid encode decode encoded
    (fun _ => view g) (fun (out : α × WGWorld) (_ : Ambient) => view out.2) (observed.run g) (action.run g)
    (appends g) (erases g) wrap
    (fun r run => checked ⟨r.value.1,g,r.value.2,r.before,r.after⟩ run)
    (fun r run => effect ⟨r.value.1,g,r.value.2,r.before,r.after⟩ run) a h prior

end Leanux.Proofs.WG.Roaming.RemoteOrigin
