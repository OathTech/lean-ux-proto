import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedHistory
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseHistory

/-! History contracts at the actual consumer checks and nested cookie repayment.
A cookie receipt is justified by this same enriched execution's native erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackHistory
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity RetirementSecurity
open NestedPeerRelease
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

variable {Safe : List Event → Prop}

private theorem initiation_check (h : Ops.History Safe g) (msg : Key) :
    Driver.StateHistorySafe Safe (initiationCheckWith g msg) := by
  unfold initiationCheckWith initiationTailWith initiationOutWith
  repeat' nested_release_history h

private theorem response_check (h : Ops.History Safe g) (msg : Key) :
    Driver.StateHistorySafe Safe (responseCheckWith g msg) := by
  unfold responseCheckWith responseTailWith
  repeat' nested_release_history h

theorem initiation (h : Ops.History Safe g) (record : HandshakeAdmission → Event)
    (emits : ∀ event, Driver.StateHistorySafe Safe (emitStatePrefix (record event)))
    (mac : HandshakeMac) : Driver.StateHistorySafe Safe (admitInitiationWith g record mac) := by
  unfold admitInitiationWith
  repeat' first
    | (driver_history_head captureWGObserved; exact (initiation_check h _).captureWGObserved)
    | (driver_history_head emitStatePrefix; exact emits _)
    | driver_state_history_step

theorem response (h : Ops.History Safe g) (record : HandshakeAdmission → Event)
    (emits : ∀ event, Driver.StateHistorySafe Safe (emitStatePrefix (record event)))
    (mac : HandshakeMac) : Driver.StateHistorySafe Safe (admitResponseWith g record mac) := by
  unfold admitResponseWith
  repeat' first
    | (driver_history_head captureWGObserved; exact (response_check h _).captureWGObserved)
    | (driver_history_head emitStatePrefix; exact emits _)
    | driver_state_history_step

theorem cookie_body (h : Ops.History Safe g) (msg : Key) :
    Driver.StateHistorySafe Safe (cookieWith g msg) := by
  unfold cookieWith cookieAfterWith
  repeat' nested_release_history h

theorem native_receipt (body : WGPrefix Event α) (native : WG.M α)
    (safe : Driver.StateHistorySafe Safe body) (erases : ErasesStatePrefix body native)
    (record : WGRunWitness α → Event)
    (append : ∀ h r, Safe h → r.Valid native → Safe (h ++ [record r])) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  intro w a h hi
  obtain ⟨suffix,history,good,normal⟩ := safe w a h hi
  have nativeRun := erases w a h
  change (runPrefix (body.run w) a h).1 = _ at nativeRun
  have equation := runWGPrefix_receiptWGObserved body record w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : runPrefix (body.run w) a h with
  | mk result hist =>
    have histEq : hist = h ++ suffix := by simpa only [run] using history
    have histSafe : Safe hist := by simpa only [run] using good
    cases result with
    | error err =>
      exact ⟨suffix,histEq,histSafe,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have valid : (WGRunWitness.mk value w v a b).Valid native := by
        rw [run] at nativeRun
        exact nativeRun.symm
      have final := append hist ⟨value,w,v,a,b⟩ histSafe valid
      refine ⟨suffix ++ [record ⟨value,w,v,a,b⟩],?_,?_,?_⟩
      · simp only [histEq,List.append_assoc]
      · exact final
      · exact final

theorem cookie (h : Ops.History Safe g) (erases : Ops.Erases g)
    (record : CookieConsumption.Receipt → Event)
    (append : ∀ h r, Safe h → r.Valid → Safe (h ++ [record r])) (msg : Key) :
    Driver.StateHistorySafe Safe (NestedPeerRelease.cookieObserved g record msg) := by
  unfold NestedPeerRelease.cookieObserved
  apply native_receipt _ (cookieMessageConsume msg) (cookie_body h msg)
  · simpa only [cookie_native] using cookie_erases erases msg
  · intro hist r safe valid
    exact append hist ⟨msg,r⟩ safe valid

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.CallbackHistory
