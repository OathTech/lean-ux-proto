import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixQuiet

/-! A native receipt has zero or one output event, as proved from the actual
observer. Together with separate entry and exit certificates this covers every
prefix; endpoint safety alone does not imply this structural premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal

theorem receipt_history (native : WG.M α) (record : WGRunWitness α→Event)
    (w : WGWorld) (a : Ambient) (h : List Event) :
    (runWGPrefix (receiptWGObserved (liftWGPrefix native) record) w a h).2=h ∨
      ∃ event, (runWGPrefix (receiptWGObserved (liftWGPrefix native) record) w a h).2=h++[event] := by
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases (native.run w).run a with
  | error reason => exact Or.inl rfl
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    exact Or.inr ⟨record ⟨value,w,v,a,b⟩,rfl⟩

theorem single {P : List Event→WGWorld→Ambient→Prop} {Safe : List Event→Prop}
    {Q : α→List Event→WGWorld→Ambient→Prop} {body : WGPrefix Event α}
    (endpoint : StatePrefixEnsures P Safe body Q)
    (initial : ∀ h w a, P h w a→Safe h)
    (shape : ∀ w a h, P h w a→(runWGPrefix body w a h).2=h ∨
      ∃ event, (runWGPrefix body w a h).2=h++[event]) : StateEnsures P Safe body Q := by
  apply StateEnsures.of_cuts endpoint
  intro w a h before
  have safe := (endpoint w a h before).choose_spec.2.1
  rcases shape w a h before with empty | ⟨event,one⟩
  · exact ⟨[],by simpa only [List.append_nil,runWGPrefix] using empty,Cuts.nil (initial h w a before)⟩
  · exact ⟨[event],one,Cuts.singleton (initial h w a before) (one ▸ safe)⟩

theorem native_receipt {P : List Event→WGWorld→Ambient→Prop} {Safe : List Event→Prop}
    {Q : α→List Event→WGWorld→Ambient→Prop} (native : WG.M α) (record : WGRunWitness α→Event)
    (endpoint : StatePrefixEnsures P Safe (receiptWGObserved (liftWGPrefix native) record) Q)
    (initial : ∀ h w a, P h w a→Safe h) :
    StateEnsures P Safe (receiptWGObserved (liftWGPrefix native) record) Q :=
  single endpoint initial (fun w a h _=>receipt_history native record w a h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
