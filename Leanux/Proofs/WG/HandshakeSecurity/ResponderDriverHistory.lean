import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCarrier

/-! Checked source cuts for the responder projection of the shared driver.
The invariant is over the actual incoming journal and the live WG state. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged

def Event.before : Event → WGWorld
  | .confirmed _ _ r => r.before
  | .selected _ r => r.before
  | .session _ r => r.before

def Checked (pre : List Event) (e : Event) : Prop :=
  Carrier (labels pre) e.before ∧ e.Valid

def Safe (h : List Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Inv (h : List Event) (w : WGWorld) : Prop := Carrier (labels h) w ∧ Safe h

abbrev Preserves (action : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Inv h w) Safe action

theorem labels_append (a b : List Event) : labels (a ++ b) = labels a ++ labels b :=
  List.flatMap_append

theorem labels_singleton (e : Event) : labels [e] = e.labels := by
  simp [labels]

theorem Safe.append (old : Safe h)
    (new : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s old new

theorem Safe.snoc (old : Safe h) (new : Checked h e) : Safe (h ++ [e]) := by
  apply old.append
  intro pre x post position
  cases pre with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at position
    obtain ⟨rfl,_⟩ := position
    simpa using new
  | cons y ys => cases ys <;> simp at position

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) :=
  ⟨Carrier.initial net bare, by intro pre e post equation; cases pre <;> cases equation⟩

/-- A quiet native step changes no checked source event. Its local carrier
contract is what later lets the whole source driver retain authorization. -/
theorem lift (action : WG.M α)
    (preserves : ∀ confirmed, Framing.Preserves (Carrier confirmed) action) :
    Preserves (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2)
  intro h w a result v b hi run
  exact ⟨(Framing.hoare_iff_run_ambient _ _ _).mp (preserves _) _ _ _ _ _ hi.1 run,hi.2⟩

/-- The generic cut rule checks the actual entry and native return, then
advances labels before any continuation. Failed prefixes retain old checks. -/
theorem receipt (action : WG.M α) (make : WGRunWitness α → Event)
    (before : ∀ r, (make r).before = r.before)
    (valid : ∀ r, r.Valid action → (make r).Valid)
    (carrier : ∀ confirmed r, r.Valid action → Carrier confirmed r.before →
      Carrier (confirmed ++ (make r).labels) r.after) :
    Preserves (receiptWGObserved (liftWGPrefix action) make) := by
  intro w a h hi
  have equation := receipt_run action make w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : (action.run w).run a with
  | error stop => exact ⟨[],by simp,hi.2,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    let r : WGRunWitness α := ⟨value,w,v,a,b⟩
    have truth : r.Valid action := run
    have checked : Checked h (make r) := ⟨by rw [before]; exact hi.1,valid r truth⟩
    have safe := hi.2.snoc checked
    refine ⟨[make r],rfl,safe,?_,safe⟩
    rw [labels_append,labels_singleton]
    exact carrier (labels h) r truth hi.1

theorem confirmation_preserves (H1 : H1ResponderCurrentEdges) (pid : PeerId) (kid : KeypairId) :
    Preserves (confirmation pid kid) := by
  apply receipt _ (Event.confirmed pid kid) (fun _ => rfl) (fun _ h => h)
  intro confirmed r valid hi
  exact carrier_confirmation H1 pid kid confirmed r valid hi

theorem session_preserves (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Preserves (session pid) := by
  apply receipt _ (Event.session pid) (fun _ => rfl) (fun _ h => h)
  intro confirmed r valid hi
  simpa only [Event.labels,List.append_nil] using
    (Framing.hoare_iff_run_ambient _ _ _).mp (carrier_session H1 pid confirmed)
      _ _ _ _ _ hi valid

theorem selection_preserves (pid : PeerId) : Preserves (selection pid) := by
  apply receipt _ (Event.selected pid) (fun _ => rfl) (fun _ h => h)
  intro confirmed r valid hi
  simpa only [Event.labels,List.append_nil] using
    (Framing.hoare_iff_run_ambient _ _ _).mp (carrier_selection pid confirmed)
      _ _ _ _ _ hi valid

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
