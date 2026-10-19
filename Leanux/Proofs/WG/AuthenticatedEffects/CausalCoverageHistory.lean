import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeNested
import Leanux.Proofs.WG.Origins.HistorySupport

/-! Context presence for native delayed effects and the allocations inherited
by completions. Presence is deliberately separate from authorization: in
particular a candidate token still needs its own successful replay receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

def Protected : Event → Prop
  | .armed _ | .queued _ | .old (.allocated _ _) => True
  | _ => False

def Present (history : List Event) : Prop :=
  ∃ token, CausalScope.current scope? history = .ok (some token)

def Checked (history : List Event) (event : Event) : Prop := Protected event → Present history

def Safe (history : List Event) : Prop :=
  ∀ before event after, history = before ++ event :: after → Checked before event

def Inv (frames : List (CausalScope.Token Cause)) (history : List Event) : Prop :=
  Safe history ∧ CausalScope.stack (history.filterMap scope?) = .ok frames

theorem Safe.empty : Safe [] := by
  intro before event after position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (ready : Safe h)
    (checked : ∀ before event after, suffix = before ++ event :: after → Checked (h ++ before) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix ready checked

theorem Safe.emit (ready : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply ready.append
  intro before entry after position
  cases before with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

theorem present (ready : Inv frames h) (live : frames ≠ []) : Present h := by
  cases frames with
  | nil => exact (live rfl).elim
  | cons token rest => exact ⟨token,by simp only [CausalScope.current,ready.2,Except.map,List.head?_cons]⟩

theorem Inv.emit (ready : Inv frames h) (scopeQuiet : scope? event = none)
    (effect : Protected event → frames ≠ []) : Inv frames (h ++ [event]) := by
  refine ⟨ready.1.emit (fun relevant => present ready (effect relevant)),?_⟩
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,scopeQuiet,
    List.append_nil] using ready.2

theorem Inv.quiet (ready : Inv frames h) (suffix : List Event)
    (scopeQuiet : ∀ event ∈ suffix, scope? event = none)
    (effect : ∀ event ∈ suffix, Protected event → frames ≠ []) : Inv frames (h ++ suffix) := by
  induction suffix generalizing h with
  | nil => simpa only [List.append_nil] using ready
  | cons event rest ih =>
    have first := ready.emit (scopeQuiet event (by simp)) (effect event (by simp))
    simpa only [List.append_assoc,List.singleton_append] using
      ih first (fun x hx => scopeQuiet x (by simp [hx])) (fun x hx => effect x (by simp [hx]))

theorem Inv.enter (ready : Inv frames h) (token : CausalScope.Token Cause) :
    Inv (token :: frames) (h ++ [.scope (.entered token)]) :=
  ⟨ready.1.emit (fun impossible => impossible.elim),
    CausalScope.stack_entered scope? Event.scope (fun _ => rfl) h frames token ready.2⟩

theorem Inv.leave (ready : Inv (token :: frames) h) :
    Inv frames (h ++ [.scope (.exited token.position)]) :=
  ⟨ready.1.emit (fun impossible => impossible.elim),
    CausalScope.stack_exited scope? Event.scope (fun _ => rfl) h frames token ready.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
