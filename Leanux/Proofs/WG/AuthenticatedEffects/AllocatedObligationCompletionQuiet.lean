import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFree

/-! Quiet native completion callbacks retain the fixed ledger and active
local. An error exports this very callback's entry cut and exact failed run;
the history frame excludes any unaccounted first-terminal event after it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompletionCuts

def ledgerEvent? (event : CausalJournal.Event) : Option CausalJournal.Event :=
  if changesLedger event then some event else none

theorem ledger_filter (history : List CausalJournal.Event) :
    history.filterMap ledgerEvent? = history.filter changesLedger := by
  induction history with
  | nil => rfl
  | cons event tail ih =>
    simp only [List.filterMap_cons,List.filter_cons,ledgerEvent?]
    cases changesLedger event <;> simp [ih]

theorem State.views (before : State context phase history w)
    (snapshot : PacketOrigins.snapshot v.wg = PacketOrigins.snapshot w.wg)
    (ownership : ownershipPointView v.wg = ownershipPointView w.wg) :
    State context phase history v := by
  obtain ⟨ledger,debts,step,support,recorded,remaining,assigned,coverage,inventory⟩ := before
  obtain ⟨epoch,cells⟩ := Prod.mk.inj snapshot
  exact ⟨ledger,debts,step,support.views epoch cells,recorded,remaining,assigned,
    coverage.points ownership,inventory.points ownership⟩

theorem State.native (before : State context phase history w) (native : WG.M α)
    (snapshot : SameView PacketOrigins.snapshot native)
    (ownership : SameView ownershipPointView native)
    (run : (liftWG native).run w = .ok (value,v)) : State context phase history v := by
  have lifted {σ : Type} (view : WGWorld → σ) (frame : SameView view native) :
      SameView (fun w : World => view w.wg) (liftWG native) :=
    sameView_liftWG (fun w : World => view w.wg) view native frame (fun _ _ _ same => same)
  exact before.views ((ProjectedAction.iff_run _ _ _).mp (lifted _ snapshot) w value v run)
    ((ProjectedAction.iff_run _ _ _).mp (lifted _ ownership) w value v run)

theorem quiet_native_checked (site : Site) (source : site.action = action)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action)
    (erases : ErasesPrefix action (liftWG native))
    (normal : ∀ w history value v, State context phase history w →
      (liftWG native).run w = .ok (value,v) → State context phase history v) : Holds context phase action := by
  intro w history before
  obtain ⟨suffix,grown⟩ := appends w history
  refine ⟨suffix,grown,?_⟩
  cases run : runPrefix action w history with
  | mk result after =>
    cases result with
    | error reason =>
      refine ⟨⟨phase,site,w,history,before,?_,?_,?_⟩⟩
      · exact ⟨suffix,by simpa only [run] using grown.symm⟩
      · simpa only [source] using run
      · simpa only [run,ledger_filter] using quiet w history
    | ok result =>
      obtain ⟨value,v⟩ := result
      have changed := normal w history value v before
        ((erases w history).symm.trans (congrArg Prod.fst run))
      have extended := changed.append suffix
      simp only [run] at grown
      simpa only [grown] using extended

theorem authenticated_checked (context : Context) (phase : Phase) :
    Holds context phase (CausalJournal.completionOps.sent context.pid) := by
  apply quiet_native_checked (.authenticated context.pid) rfl (Appends.focus _ _ _)
  · change HistoryFrame ledgerEvent? (focusPrefix _ _ (Completion.access _))
    unfold Completion.access
    rw [CompletionEffects.focus_composed]
    exact focusPrefix_other _ _ _ (fun _ => rfl) _
  · exact focusPrefix_erases _ _ (Completion.access_erases
      (timersAnyAuthenticatedPacketSentPrefix_erases context.pid))
  · intro w history value v before run
    exact before.native _ (PacketOrigins.snapshot_wire (delTimer_cryptWire context.pid .sendKeepalive))
      (delTimer_ownership context.pid .sendKeepalive) run

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
