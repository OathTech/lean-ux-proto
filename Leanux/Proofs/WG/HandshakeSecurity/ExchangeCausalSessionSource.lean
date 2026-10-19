import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalProjection

/-! The same native session has two adjacent receipts in the final journal.
This selector uses its exchange receipt as the responder session cut and drops
only the old duplicate. Selection and confirmation keep their original cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects CausalJournal

abbrev Cut := Responder.DriverCuts.Event

def withoutSession : Cut → Option Cut
  | .session _ _ => none
  | e => some e

def cut? : Event → Option Cut
  | .exchange (.session pid r) => some (.session pid r)
  | .old (.responder e) => withoutSession e
  | _ => none

theorem old_cut (e : Journal.Event) : cut? (Event.old e) = (Journal.responder? e).bind withoutSession := by
  cases e <;> rfl

theorem focus_receipt (record : E → F) (decode : F → Option E)
    (a : WG.M α) (make : WGRunWitness α → E) :
    focusStatePrefix record decode (receiptWGObserved (liftWGPrefix a) make) =
      receiptWGObserved (liftWGPrefix a) (record ∘ make) := by
  funext w b h
  change ((runWGPrefix (receiptWGObserved (liftWGPrefix a) make) w b (h.filterMap decode)).1,
    h ++ ((runWGPrefix (receiptWGObserved (liftWGPrefix a) make) w b (h.filterMap decode)).2.drop
      (h.filterMap decode).length).map record) = _
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  change _ = runWGPrefix (receiptWGObserved (liftWGPrefix a) (record ∘ make)) w b h
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases run : (a.run w).run b with
  | error stop => simp
  | ok out => rcases out with ⟨⟨x,v⟩,c⟩; simp

private theorem native_result (rho : E → Option F) (g : PrefixM E α) (a : Leanux.M α)
    (projects : ProjectsPrefix rho id g (liftPrefix a)) : ErasesPrefix g a := by
  intro w h
  have result := congrArg Prod.fst (projects w h)
  change a.run w = (runPrefix g w h).1.map id at result
  simpa only [Except.map_id,id_eq] using result.symm

private theorem focused_history (g : PrefixM Journal.Event α) (appends : Appends g)
    (quiet : HistoryFrame Journal.responder? g) : HistoryFrame cut? (product g) := by
  intro w h
  obtain ⟨suffix,appended⟩ := appends w (h.filterMap old?)
  have frame := quiet w (h.filterMap old?)
  rw [appended,List.filterMap_append] at frame
  have empty : suffix.filterMap Journal.responder? = [] :=
    by simpa using frame
  change (h ++ ((runPrefix g w (h.filterMap old?)).2.drop (h.filterMap old?).length).map Event.old).filterMap cut? = _
  rw [appended,List.drop_left,List.filterMap_append,List.filterMap_map]
  have reduced : suffix.filterMap (cut? ∘ Event.old) = [] := by
    have same : (cut? ∘ Event.old) = fun e => (Journal.responder? e).bind withoutSession := funext old_cut
    rw [same,← List.filterMap_filterMap,empty]
    rfl
  rw [reduced,List.append_nil]

theorem product_native (g : PrefixM Journal.Event α) (a : Leanux.M α)
    (appends : Appends g) (projects : ProjectsPrefix Journal.responder? id g (liftPrefix a)) :
    ProjectsPrefix cut? id (product g) (liftPrefix a) := by
  apply HistoryFrame.project
  · apply focused_history g appends
    intro w h
    exact (congrArg Prod.snd (projects w h)).symm
  · exact focusPrefix_erases Event.old old? (native_result Journal.responder? g a projects)

theorem state_native (g : WGPrefix Journal.Event α) (a : WG.M α)
    (appends : StateAppends g) (projects : StateProjectsPrefix Journal.responder? id g (liftWGPrefix a)) :
    StateProjectsPrefix cut? id (state g) (liftWGPrefix a) := by
  apply Exchange.quiet_native_projection
  · intro w b h
    change (runStatePrefix g w b (h.filterMap old?)).1 = (a.run w).run b
    have result := congrArg Prod.fst (projects w b (h.filterMap old?))
    change (a.run w).run b = (runStatePrefix g w b (h.filterMap old?)).1.map id at result
    simpa only [state,focusStatePrefix,runStatePrefix,runPrefix,StateT.run,Except.map_id,id_eq] using result.symm
  · intro w b h
    have frame : HistoryFrame Journal.responder? (g.run w) := fun a hist =>
      (congrArg Prod.snd (projects w a hist)).symm
    obtain ⟨suffix,appended⟩ := appends w b (h.filterMap old?)
    have old := frame b (h.filterMap old?)
    rw [appended,List.filterMap_append] at old
    have empty : suffix.filterMap Journal.responder? = [] :=
      by simpa using old
    change (h ++ ((runPrefix (g.run w) b (h.filterMap old?)).2.drop (h.filterMap old?).length).map Event.old).filterMap cut? = _
    rw [appended,List.drop_left,List.filterMap_append,List.filterMap_map]
    have reduced : suffix.filterMap (cut? ∘ Event.old) = [] := by
      have same : (cut? ∘ Event.old) = fun e => (Journal.responder? e).bind withoutSession := funext old_cut
      rw [same,← List.filterMap_filterMap,empty]
      rfl
    rw [reduced,List.append_nil]

theorem selection_projects (pid : PeerId) :
    StateProjectsPrefix cut? id (state (Journal.selection pid)) (Responder.DriverCuts.selection pid) := by
  simp only [state,Journal.selection,Responder.DriverCuts.selection,focus_receipt]
  exact Exchange.receipt_projects cut? _ _ _ _ (Driver.Projection.state_lift cut? _) (fun _ => rfl)

theorem confirmation_projects (pid : PeerId) (kid : KeypairId) :
    StateProjectsPrefix cut? id (state (Journal.confirmation pid kid))
      (Responder.DriverCuts.confirmation pid kid) := by
  simp only [state,Journal.confirmation,Responder.DriverCuts.confirmation,focus_receipt]
  exact Exchange.receipt_projects cut? _ _ _ _ (Driver.Projection.state_lift cut? _) (fun _ => rfl)

theorem session_projects (pid : PeerId) :
    StateProjectsPrefix cut? id (session pid) (Responder.DriverCuts.session pid) := by
  change StateProjectsPrefix cut? id (receiptWGObserved (state (Journal.session pid))
    (Event.exchange ∘ Exchange.Event.session pid)) (Responder.DriverCuts.session pid)
  apply Exchange.receipt_projects cut? _ _ _ _ ?_ (fun _ => rfl)
  simp only [state,Journal.session,Responder.DriverCuts.session,focus_receipt]
  exact Exchange.receipt_ignored cut? _ _ _ (Driver.Projection.state_lift cut? _) (fun _ => rfl)

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSession
