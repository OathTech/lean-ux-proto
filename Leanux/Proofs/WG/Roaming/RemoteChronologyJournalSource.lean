import Leanux.Proofs.WG.Roaming.RemoteChronologyInertSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E F State α : Type}

def Inv (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (history : List E) (current : RemoteMap) : Prop :=
  Last effect entry history current ∧ RemoteHistoryValid valid history

theorem focused_retained_inert
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect (encode e) pid) =
      h.filterMap (fun e => effect (encode e) pid))
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (retained : ∀ w value final, action.run w = .ok (value,final) →
      RemoteRetained (before w) (after value final)) :
    PrefixEnsures (fun h w => Inv effect entry valid h (before w))
      (RemoteHistoryValid valid) (focusPrefix encode decode observed)
      (fun value h final => Inv effect entry valid h (after value final)) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap decode)
  have actual := focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl appended)
  have safe : RemoteHistoryValid valid (h ++ suffix.map encode) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact encoded original
  have quiet : ∀ pid, Untouched effect (suffix.map encode) pid := by
    intro pid event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact untouched_suffix (fun e target => effect (encode e) target)
      (h.filterMap decode) suffix _ appended (inert w (h.filterMap decode)) pid original
        (by assumption)
  rw [actual]
  refine ⟨suffix.map encode,rfl,safe,?_⟩
  cases execution : (runPrefix observed w (h.filterMap decode)).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,final⟩ := out
    have run := (erases w (h.filterMap decode)).symm.trans execution
    exact ⟨quiet_append prior.1 quiet (retained w value final run),safe⟩

theorem focused_receipt_inert
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event))
    (before : State → RemoteMap) (after : α → State → RemoteMap)
    (observed : PrefixT F State α) (action : StateT State (Except Stop) α)
    (inert : ∀ w h pid, (runPrefix observed w h).2.filterMap (fun e => effect (encode e) pid) =
      h.filterMap (fun e => effect (encode e) pid))
    (appends : Appends observed) (erases : ErasesPrefix observed action)
    (receiptEvent : StateRunWitness State α → E)
    (checked : ∀ r, r.Valid action → valid (receiptEvent r))
    (changed : ∀ r, r.Valid action →
      RemoteRetained (applyEffect effect (receiptEvent r) (before r.before)) (after r.value r.after)) :
    PrefixEnsures (fun h w => Inv effect entry valid h (before w))
      (RemoteHistoryValid valid) (receiptObserved (focusPrefix encode decode observed) receiptEvent)
      (fun value h final => Inv effect entry valid h (after value final)) := by
  intro w h prior
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap decode)
  have actual := focusPrefix_suffix encode decode observed w h _ suffix (Prod.ext rfl appended)
  have safe : RemoteHistoryValid valid (h ++ suffix.map encode) := by
    apply prior.2.append
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact encoded original
  have quiet : ∀ pid, Untouched effect (suffix.map encode) pid := by
    intro pid event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact untouched_suffix (fun e target => effect (encode e) target)
      (h.filterMap decode) suffix _ appended (inert w (h.filterMap decode)) pid original
        (by assumption)
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
    refine ⟨suffix.map encode ++ [receiptEvent ⟨value,w,final⟩],?_,
      safe.snoc (checked _ run),?_⟩
    · exact List.append_assoc _ _ _
    · exact ⟨receipt (quiet_append prior.1 quiet (.refl _)) _ (changed _ run),
        safe.snoc (checked _ run)⟩



theorem native_focused_receipt_inert
    (effect : Effect E) (entry : RemoteMap) (valid : E → Prop)
    (encode : F → E) (decode : E → Option F)
    (encoded : ∀ event, valid (encode event)) (view : WGWorld → RemoteMap)
    (observed : WGPrefix F α) (action : WG.M α)
    (inert : ∀ g a h pid, (runWGPrefix observed g a h).2.filterMap
      (fun e => effect (encode e) pid) = h.filterMap (fun e => effect (encode e) pid))
    (appends : StateAppends observed) (erases : ErasesStatePrefix observed action)
    (receiptEvent : WGRunWitness α → E)
    (checked : ∀ r, r.Valid action → valid (receiptEvent r))
    (changed : ∀ r, r.Valid action →
      RemoteRetained (applyEffect effect (receiptEvent r) (view r.before)) (view r.after)) :
    StatePrefixPreserves (fun h g _ => Inv effect entry valid h (view g))
      (RemoteHistoryValid valid)
      (receiptWGObserved (focusStatePrefix encode decode observed) receiptEvent) := by
  intro g a h prior
  let wrap : StateRunWitness Ambient (α × WGWorld) → E :=
    fun r => receiptEvent ⟨r.value.1,g,r.value.2,r.before,r.after⟩
  have actual : runPrefix
      ((receiptWGObserved (focusStatePrefix encode decode observed) receiptEvent).run g) a h =
      runPrefix (receiptObserved (focusPrefix encode decode (observed.run g)) wrap) a h := by
    have concrete := runWGPrefix_receiptWGObserved
      (focusStatePrefix encode decode observed) receiptEvent g a h
    change runPrefix ((receiptWGObserved (focusStatePrefix encode decode observed) receiptEvent).run g) a h = _ at concrete
    rw [concrete,runPrefix_receiptObserved]
    simp only [runWGPrefix,runStatePrefix,StateT.run,focusStatePrefix]
    cases runPrefix (focusPrefix encode decode (observed g)) a h with
    | mk result history =>
      cases result with
      | error stop => rfl
      | ok out => obtain ⟨⟨value,final⟩,after⟩ := out; rfl
  rw [actual]
  exact focused_receipt_inert effect entry valid encode decode encoded
    (fun _ => view g) (fun (out : α × WGWorld) (_ : Ambient) => view out.2)
    (observed.run g) (action.run g) (inert g) (appends g) (erases g) wrap
    (fun r run => checked ⟨r.value.1,g,r.value.2,r.before,r.after⟩ run)
    (fun r run => changed ⟨r.value.1,g,r.value.2,r.before,r.after⟩ run) a h prior

end Leanux.Proofs.WG.Roaming.RemoteChronology
