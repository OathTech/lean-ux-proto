import Leanux.Proofs.WG.HandshakeSecurity.ExchangeObservation

/-! Completed exchange receipts decorate the actual existing callback. Exact
history projections retain its other observations and every stopped prefix;
native result erasure alone is not a history connection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem quiet_native_projection (rho : E → Option F)
    (callback : WGPrefix E α) (native : WG.M α)
    (erases : ErasesStatePrefix callback native)
    (quiet : StateHistoryFrame rho callback) :
    StateProjectsPrefix rho id callback (liftWGPrefix native) := by
  intro w a h
  have result := erases w a h
  have history := quiet w a h
  change (runWGPrefix callback w a h).1 = (native.run w).run a at result
  change (runWGPrefix callback w a h).2.filterMap rho = h.filterMap rho at history
  change runWGPrefix (liftWGPrefix native) w a (h.filterMap rho) = _
  rw [runWGPrefix_lift]
  change ((native.run w).run a, h.filterMap rho) =
    ((runWGPrefix callback w a h).1.map
      (fun x => (Prod.map id id x.1,x.2)), (runWGPrefix callback w a h).2.filterMap rho)
  have identity : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨⟨value,state⟩,ambient⟩
    rfl
  simp only [identity,Except.map_id,id_eq,result,history]

theorem receipt_projects (rho : E → Option F)
    (callback : WGPrefix E α) (target : WGPrefix F α)
    (record : WGRunWitness α → E) (targetRecord : WGRunWitness α → F)
    (projects : StateProjectsPrefix rho id callback target)
    (records : ∀ r, rho (record r) = some (targetRecord r)) :
    StateProjectsPrefix rho id (receiptWGObserved callback record)
      (receiptWGObserved target targetRecord) := by
  intro w a h
  have base := projects w a h
  change runWGPrefix target w a (h.filterMap rho) =
    ((runWGPrefix callback w a h).1.map
      (fun x => (Prod.map id id x.1,x.2)), (runWGPrefix callback w a h).2.filterMap rho) at base
  have identity : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨⟨value,state⟩,ambient⟩
    rfl
  simp only [identity,Except.map_id,id_eq] at base
  change runWGPrefix (receiptWGObserved target targetRecord) w a (h.filterMap rho) = _
  rw [runWGPrefix_receiptWGObserved,base]
  change _ = ((runWGPrefix (receiptWGObserved callback record) w a h).1.map
    (fun x => (Prod.map id id x.1,x.2)),
    (runWGPrefix (receiptWGObserved callback record) w a h).2.filterMap rho)
  rw [runWGPrefix_receiptWGObserved,identity,Except.map_id]
  cases run : runWGPrefix callback w a h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out =>
      rcases out with ⟨⟨value,state⟩,ambient⟩
      simp only [id_eq,List.filterMap_append,List.filterMap_cons,records,List.filterMap_nil]

theorem receipt_ignored (rho : E → Option F)
    (callback : WGPrefix E α) (target : WGPrefix F α)
    (record : WGRunWitness α → E)
    (projects : StateProjectsPrefix rho id callback target)
    (records : ∀ r, rho (record r) = none) :
    StateProjectsPrefix rho id (receiptWGObserved callback record) target := by
  intro w a h
  have base := projects w a h
  change runWGPrefix target w a (h.filterMap rho) =
    ((runWGPrefix callback w a h).1.map
      (fun x => (Prod.map id id x.1,x.2)), (runWGPrefix callback w a h).2.filterMap rho) at base
  change runWGPrefix target w a (h.filterMap rho) = _
  rw [base]
  change _ = ((runWGPrefix (receiptWGObserved callback record) w a h).1.map
    (fun x => (Prod.map id id x.1,x.2)),
    (runWGPrefix (receiptWGObserved callback record) w a h).2.filterMap rho)
  rw [runWGPrefix_receiptWGObserved]
  cases run : runWGPrefix callback w a h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out =>
      rcases out with ⟨⟨value,state⟩,ambient⟩
      simp only [List.filterMap_append,List.filterMap_cons,records,List.filterMap_nil,List.append_nil]

/-- Both native state erasure and a separate exchange-history frame are
required before an existing observed callback can project to a native exchange
receipt. This preserves its execution rather than invoking a second consumer. -/
theorem decorated_native_projection (decode : E → Option Event) (encode : Event → E)
    (roundtrip : ∀ e, decode (encode e) = some e)
    (callback : WGPrefix E α) (native : WG.M α)
    (erases : ErasesStatePrefix callback native)
    (quiet : StateHistoryFrame decode callback) (record : WGRunWitness α → Event) :
    StateProjectsPrefix decode id (receiptWGObserved callback (encode ∘ record))
      (receiptWGObserved (liftWGPrefix native) record) :=
  receipt_projects decode callback _ _ record
    (quiet_native_projection decode callback native erases quiet) (fun r => roundtrip (record r))

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
